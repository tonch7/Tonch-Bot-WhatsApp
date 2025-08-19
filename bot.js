// bot.js — TonchB0T (versão VPS/Headless/Antispam)

// === DEPENDÊNCIAS ===
const { Client, LocalAuth, MessageMedia } = require('whatsapp-web.js');
const qrcode = require('qrcode-terminal');
const fs = require('fs');
const path = require('path');
const readline = require('readline');
const moment = require('moment');
const { exec } = require('child_process');
const mime = require('mime-types');
const open = require('open');
const os = require('os');
const https = require('https');
const crypto = require('crypto');

// === CONFIG & PASTAS ===
const BASE_DIR = process.cwd();
const LOG_DIR = path.join(BASE_DIR, 'whatsapp-bot-logs');
const FILES_DIR = path.join(BASE_DIR, 'whatsapp-bot-files');
const CONFIG_FILE = path.join(BASE_DIR, 'whatsapp-bot-config.json');
const PROGRESS_FILE = path.join(BASE_DIR, 'whatsapp-bot-progress.json');
const BACKUP_DIR = path.join(BASE_DIR, 'whatsapp-bot-backups');
const RESPONSES_FILE = path.join(BASE_DIR, 'whatsapp-bot-responses.json');
const ADMINS_FILE = path.join(BASE_DIR, 'whatsapp-bot-admins.json');
const SCHEDULE_FILE = path.join(BASE_DIR, 'whatsapp-bot-schedules.json');
const SENT_HISTORY_FILE = path.join(BASE_DIR, 'whatsapp-bot-sent-history.json');
const QUEUE_FILE = path.join(BASE_DIR, 'whatsapp-bot-queue.json');
const SEGMENTS_FILE = path.join(BASE_DIR, 'whatsapp-bot-segments.json');

// === CONSOLE COLORS ===
const colors = {
  error: '\x1b[31m',
  success: '\x1b[32m',
  info: '\x1b[36m',
  warning: '\x1b[33m',
  reset: '\x1b[0m'
};
function colorLog(type, ...messages) {
  const prefix = `${colors[type] || ''}`;
  console.log(prefix + messages.join(' ') + colors.reset);
}

// === JSON SAFE R/W ===
function safeReadJSON(filePath, fallback) {
  try {
    if (!fs.existsSync(filePath)) return fallback;
    const raw = fs.readFileSync(filePath, 'utf8');
    if (!raw) return fallback;
    return JSON.parse(raw);
  } catch (err) {
    colorLog('warning', `[JSON] Falha ao ler ${path.basename(filePath)}: ${err.message}. Usando fallback.`);
    return fallback;
  }
}
function safeWriteJSON(filePath, data) {
  try {
    fs.writeFileSync(filePath, JSON.stringify(data, null, 2));
    return true;
  } catch (err) {
    colorLog('error', `[JSON] Falha ao salvar ${path.basename(filePath)}: ${err.message}`);
    return false;
  }
}

// === SETUP ===
function setupDirectories() {
  [LOG_DIR, FILES_DIR, BACKUP_DIR].forEach(dir => {
    if (!fs.existsSync(dir)) {
      fs.mkdirSync(dir, { recursive: true });
      colorLog('info', `[SISTEMA] Pasta criada: ${path.basename(dir)}`);
    }
  });

  if (!fs.existsSync(CONFIG_FILE)) {
    safeWriteJSON(CONFIG_FILE, {
      delayBetweenMessages: 3500,
      maxRetries: 3,
      autoReconnect: true,
      maxDelay: 30000,
      safeBatchSize: 50,
      safeBatchPauseMs: 60000,
      maxMessagesPerMinute: 20,      // LIMITE POR MINUTO (antiflood)
      weeklyReportHourUTC: 12,
      concurrency: 2,                // concorrência segura
      duplicateWindowDays: 30,       // não repetir campanha por X dias
      duplicateIgnoreIfOlderThanDays: 365
    });
  }

  if (!fs.existsSync(PROGRESS_FILE)) safeWriteJSON(PROGRESS_FILE, { lastIndex: 0 });
  if (!fs.existsSync(RESPONSES_FILE)) safeWriteJSON(RESPONSES_FILE, {});
  if (!fs.existsSync(ADMINS_FILE)) safeWriteJSON(ADMINS_FILE, []);
  if (!fs.existsSync(SCHEDULE_FILE)) safeWriteJSON(SCHEDULE_FILE, []);
  if (!fs.existsSync(SENT_HISTORY_FILE)) safeWriteJSON(SENT_HISTORY_FILE, []);
  if (!fs.existsSync(QUEUE_FILE)) safeWriteJSON(QUEUE_FILE, []);
  if (!fs.existsSync(SEGMENTS_FILE)) safeWriteJSON(SEGMENTS_FILE, {});
}
function preStartAnalysis() {
  colorLog('info', '[CHECK] Análise pré-inicialização...');
  const issues = [];
  [LOG_DIR, FILES_DIR, BACKUP_DIR].forEach(dir => {
    try { fs.accessSync(dir, fs.constants.R_OK | fs.constants.W_OK); } catch { issues.push(`Permissão incoerente: ${dir}`); }
  });
  const cfg = safeReadJSON(CONFIG_FILE, null);
  if (!cfg) issues.push('Configuração inválida ou ausente');
  colorLog('info', `[SYS] Hostname: ${os.hostname()} | User: ${os.userInfo().username}`);
  if (issues.length) {
    colorLog('warning', '[CHECK] Problemas detectados:');
    issues.forEach(i => colorLog('warning', '- ' + i));
    colorLog('warning', '[CHECK] Recomendo corrigir antes de produção.');
  } else {
    colorLog('success', '[CHECK] Verificação concluída sem problemas críticos.');
  }
  return { issues, cfg };
}

// === NET UTILS ===
function getPublicIP(timeout = 5000) {
  return new Promise((resolve) => {
    try {
      const req = https.get('https://api.ipify.org?format=json', (res) => {
        let data = '';
        res.on('data', chunk => data += chunk);
        res.on('end', () => {
          try { resolve((JSON.parse(data).ip) || 'unknown'); } catch { resolve('unknown'); }
        });
      });
      req.on('error', () => resolve('unknown'));
      req.setTimeout(timeout, () => { req.abort(); resolve('timeout'); });
    } catch { resolve('unknown'); }
  });
}

// === ESTADO ===
let contatos = [];
let isSending = false;
let isPaused = false;
let dynamicDelay = 3500;
let clientReady = false;
let qrCodeGenerated = false;
let currentQrCode = null;
let client = null;
let admins = safeReadJSON(ADMINS_FILE, []);
let queueProcessor = null;

// relatório/envio atual
let currentSending = {
  type: null,
  content: null,
  total: 0,
  sent: 0,
  failed: 0,
  startTime: null,
  entries: []
};

// === HISTÓRICO DE ENVIOS (dedupe) ===
function loadSentHistory() { return safeReadJSON(SENT_HISTORY_FILE, []); }
function saveSentHistory(history) {
  const cfg = safeReadJSON(CONFIG_FILE, {});
  const keepDays = cfg.duplicateIgnoreIfOlderThanDays || 365;
  const cutoff = Date.now() - (keepDays * 24 * 60 * 60 * 1000);
  const pruned = history.filter(h => new Date(h.time).getTime() >= cutoff);
  safeWriteJSON(SENT_HISTORY_FILE, pruned);
}
function recordSent(contactId, campaignId, status, reason) {
  const history = loadSentHistory();
  history.push({ contactId, campaignId, status, reason: reason || null, time: new Date().toISOString() });
  saveSentHistory(history);
}
function wasSentRecently(contactId, campaignId) {
  const history = loadSentHistory();
  const cfg = safeReadJSON(CONFIG_FILE, {});
  const windowDays = cfg.duplicateWindowDays || 30;
  const cutoff = Date.now() - (windowDays * 24 * 60 * 60 * 1000);
  return history.some(h => h.contactId === contactId && h.campaignId === campaignId && new Date(h.time).getTime() >= cutoff);
}

// === FILA PERSISTENTE ===
function loadQueue() { return safeReadJSON(QUEUE_FILE, []); }
function saveQueue(queue) { return safeWriteJSON(QUEUE_FILE, queue); }
function createJob(payload) {
  const id = crypto.randomBytes(8).toString('hex');
  const job = Object.assign({ id, createdAt: new Date().toISOString() }, payload);
  const queue = loadQueue();
  queue.push(job);
  saveQueue(queue);
  return job;
}
function removeJob(jobId) {
  let queue = loadQueue();
  queue = queue.filter(j => j.id !== jobId);
  saveQueue(queue);
}
function listQueue() { return loadQueue(); }

// === AGENDADOR ===
function loadSchedules() { return safeReadJSON(SCHEDULE_FILE, []); }
function saveSchedules(schedules) { return safeWriteJSON(SCHEDULE_FILE, schedules); }
function addScheduleItem(item) {
  const schedules = loadSchedules();
  const id = crypto.randomBytes(8).toString('hex');
  schedules.push(Object.assign({ id }, item));
  saveSchedules(schedules);
  return id;
}
function removeScheduleItem(id) {
  let schedules = loadSchedules();
  schedules = schedules.filter(s => s.id !== id);
  saveSchedules(schedules);
}
function listSchedules() { return loadSchedules(); }
function startScheduleLoop() {
  setInterval(async () => {
    const schedules = loadSchedules();
    const now = Date.now();
    for (const s of schedules.slice()) {
      const when = new Date(s.when).getTime();
      if (!when || isNaN(when)) continue;
      if (when <= now) {
        try {
          const targets = resolveTargetsForSchedule(s);
          if (!targets.length) colorLog('warning', `[SCHEDULE] Nenhum target para schedule ${s.id}`);
          else {
            createJob({
              type: s.type,
              message: s.message,
              filename: s.filename,
              targets,
              tag: s.tag,
              campaignId: s.campaignId || s.id,
              scheduledFrom: s.id
            });
            colorLog('info', `[SCHEDULE] Job enfileirado para ${s.id} (${targets.length} contatos)`);
          }
        } catch (err) {
          colorLog('error', '[SCHEDULE] Erro ao enfileirar schedule:', err.message || err);
        } finally {
          removeScheduleItem(s.id);
        }
      }
    }
  }, 30_000);
}

// === SEGMENTOS ===
function loadSegments() { return safeReadJSON(SEGMENTS_FILE, {}); }
function saveSegments(segs) { return safeWriteJSON(SEGMENTS_FILE, segs); }
function resolveTargetsForTag(tag) {
  const segs = loadSegments();
  const matched = [];
  contatos.forEach(c => {
    const tags = segs[c.id] || [];
    if (tags.includes(tag)) matched.push(c.id);
  });
  return matched;
}
function resolveTargetsForSchedule(schedule) {
  if (schedule.tag) return resolveTargetsForTag(schedule.tag);
  if (Array.isArray(schedule.targets) && schedule.targets.length) return schedule.targets;
  return contatos.map(c => c.id);
}

// === CONTATOS (ignora grupos) ===
async function updateContacts(clientInstance = client) {
  try {
    const chats = await clientInstance.getChats();
    contatos = chats.filter(c => !c.isGroup && !c.archived)
      .map(c => ({ id: c.id._serialized, name: c.name || c.id.user }));
    colorLog('success', `[CONTATOS] ${contatos.length} contatos carregados (grupos ignorados).`);
  } catch (error) {
    colorLog('error', '[Erro] Falha ao buscar contatos:', error);
  }
}

// === MIDIA ===
async function criarMessageMedia(filepath, nomeArquivo) {
  try {
    const stats = fs.statSync(filepath);
    const maxSizeBytes = 10 * 1024 * 1024; // 10MB
    if (stats.size > maxSizeBytes) {
      throw new Error(`Arquivo muito grande (${(stats.size / 1024 / 1024).toFixed(2)}MB). Limite: 10MB`);
    }
    const data = fs.readFileSync(filepath, { encoding: 'base64' });
    const mimeType = mime.lookup(nomeArquivo) || 'application/octet-stream';
    return new MessageMedia(mimeType, data, nomeArquivo);
  } catch (err) {
    colorLog('error', `[Erro] Falha ao ler arquivo ${nomeArquivo}: ${err.message || err}`);
    throw err;
  }
}

// === RELATÓRIOS AVANÇADOS (CSV+HTML) ===
function generateCSVReport(entries, filename) {
  const header = ['contact', 'status', 'reason', 'time', 'campaignId'];
  const rows = entries.map(e => [
    e.contact,
    e.status,
    (e.reason || '').replace(/\n/g, ' '),
    e.time,
    e.campaignId || ''
  ]);
  const csv = [header.join(','), ...rows.map(r => r.map(v => `"${String(v).replace(/"/g, '""')}"`).join(','))].join('\n');
  const filePath = path.join(LOG_DIR, filename);
  fs.writeFileSync(filePath, csv, 'utf8');
  return filePath;
}
function generateAdvancedReport() {
  try {
    const history = loadSentHistory();
    const recent = history.slice(-500);
    const stats = {
      total: recent.length,
      sent: recent.filter(r => r.status === 'sent').length,
      failed: recent.filter(r => r.status !== 'sent').length,
      timeframeStart: recent.length ? recent[0].time : '-',
      timeframeEnd: recent.length ? recent[recent.length - 1].time : '-'
    };
    const csvName = `report_${moment().format('YYYY-MM-DD_HH-mm-ss')}.csv`;
    const csvPath = generateCSVReport(recent, csvName);
    const html = `
<!doctype html>
<html><head><meta charset="utf-8"><title>Relatório Avançado</title></head><body>
<h1>Relatório Avançado - Projeto Tonch</h1>
<p>Total registros analisados: ${stats.total}</p>
<p>Enviados: ${stats.sent}</p>
<p>Falhas: ${stats.failed}</p>
<p>Período: ${stats.timeframeStart} → ${stats.timeframeEnd}</p>
<p>CSV: ${csvName}</p>
</body></html>`;
    const htmlPath = path.join(LOG_DIR, `report_${moment().format('YYYY-MM-DD_HH-mm-ss')}.html`);
    fs.writeFileSync(htmlPath, html, 'utf8');
    return { csvPath, htmlPath, stats };
  } catch (err) {
    colorLog('error', '[RELATORIO] Falha ao gerar relatório avançado:', err.message || err);
    return null;
  }
}

// === ENVIO UNITÁRIO ===
async function sendToContactSingle(clientInstance, contatoId, job) {
  try {
    if (job.type === 'message' && job.message) {
      await clientInstance.sendMessage(contatoId, job.message);
    } else if ((job.type === 'file' || job.type === 'message+file') && job.filename) {
      const filepath = path.join(FILES_DIR, job.filename);
      if (!fs.existsSync(filepath)) throw new Error('Arquivo não encontrado: ' + job.filename);
      const media = await criarMessageMedia(filepath, job.filename);
      if (job.type === 'message+file' && job.message) {
        await clientInstance.sendMessage(contatoId, job.message);
        await delay(1500);
      }
      await clientInstance.sendMessage(contatoId, media);
    } else {
      throw new Error('Tipo de job inválido ou faltando dados');
    }
    return { status: 'sent' };
  } catch (err) {
    return { status: 'failed', reason: err.message || String(err) };
  }
}

// === LIMITADOR POR MINUTO (ANTIFLOOD) ===
const rateLimiter = {
  windowStart: Date.now(),
  count: 0
};
async function respectRateLimit(cfg) {
  const now = Date.now();
  const windowMs = 60 * 1000;
  if (now - rateLimiter.windowStart >= windowMs) {
    rateLimiter.windowStart = now;
    rateLimiter.count = 0;
    return;
  }
  if (rateLimiter.count >= (cfg.maxMessagesPerMinute || 20)) {
    const waitMs = windowMs - (now - rateLimiter.windowStart) + 250;
    colorLog('info', `[RATE] Atingido limite/min. Aguardando ${(waitMs / 1000).toFixed(1)}s...`);
    await delay(waitMs);
    rateLimiter.windowStart = Date.now();
    rateLimiter.count = 0;
  }
}

// === PROCESSADOR DE FILA (com pausa real, dedupe, backoff, limite/min) ===
async function startQueueProcessor(clientInstance) {
  if (queueProcessor) return;
  queueProcessor = true;
  colorLog('info', '[QUEUE] Iniciando processador de fila...');

  (async function loop() {
    while (true) {
      try {
        if (!clientInstance || !clientReady) { await delay(2000); continue; }

        // respeita $pause
        if (isPaused) { await delay(1000); continue; }

        let queue = loadQueue();
        if (!queue.length) { await delay(1000); continue; }

        const cfg = safeReadJSON(CONFIG_FILE, {});
        const concurrency = Math.max(1, cfg.concurrency || 2);
        const safeBatchSize = cfg.safeBatchSize || 50;
        const safeBatchPauseMs = cfg.safeBatchPauseMs || 60000;

        const job = queue[0];
        if (!job) { await delay(1000); continue; }

        const targets = Array.isArray(job.targets) ? job.targets.slice() : [];
        if (!targets.length) { removeJob(job.id); continue; }

        const chunkSize = Math.max(1, Math.min(concurrency, 10));
        const chunk = targets.splice(0, chunkSize);

        // envia cada item do chunk, com limite por minuto
        const sendPromises = chunk.map(async (contactId) => {
          // dedupe
          if (wasSentRecently(contactId, job.campaignId || 'default')) {
            colorLog('warning', `[DUP] Pular ${contactId} — já recebeu campanha ${job.campaignId}`);
            currentSending.entries.push({ contact: contactId, status: 'skipped_duplicate', time: new Date().toISOString(), campaignId: job.campaignId });
            recordSent(contactId, job.campaignId, 'skipped_duplicate', 'duplicate_recent');
            return;
          }

          // respeita janela por minuto
          await respectRateLimit(cfg);

          // retries com backoff
          const maxRetries = (cfg.maxRetries || 3);
          let lastErr = null;
          for (let attempt = 0; attempt <= maxRetries; attempt++) {
            const res = await sendToContactSingle(clientInstance, contactId, job);
            if (res.status === 'sent') {
              rateLimiter.count += 1;
              currentSending.sent++;
              currentSending.entries.push({ contact: contactId, status: 'sent', time: new Date().toISOString(), campaignId: job.campaignId });
              recordSent(contactId, job.campaignId, 'sent');
              return;
            }
            lastErr = res.reason;
            if (attempt < maxRetries) {
              const backoff = 1500 + attempt * 1500 + Math.floor(Math.random() * 750);
              colorLog('warning', `[RETRY] Tentativa ${attempt + 1} falhou para ${contactId}: ${res.reason}. Aguardando ${backoff}ms...`);
              await delay(backoff);
            }
          }
          currentSending.failed++;
          currentSending.entries.push({ contact: contactId, status: 'failed', reason: lastErr, time: new Date().toISOString(), campaignId: job.campaignId });
          recordSent(contactId, job.campaignId, 'failed', lastErr);
          colorLog('error', `[FAIL] ${contactId} → ${lastErr}`);
        });

        await Promise.all(sendPromises);

        // atualiza fila
        const remainingTargets = targets;
        let q = loadQueue();
        const idx = q.findIndex(j => j.id === job.id);
        if (idx >= 0) {
          if (remainingTargets.length === 0) q.splice(idx, 1);
          else q[idx].targets = remainingTargets;
          saveQueue(q);
        }

        // delay seguro entre chunks
        await delay((cfg.delayBetweenMessages || dynamicDelay || 3500) + Math.floor(Math.random() * 800) - 300);

        // pausa entre lotes grandes
        if (chunk.length >= safeBatchSize) {
          colorLog('info', `[BATCH] Processado ${chunk.length} — Pausando ${safeBatchPauseMs / 1000}s`);
          await delay(safeBatchPauseMs);
        }

      } catch (err) {
        colorLog('error', '[QUEUE] Erro no loop da fila:', err.message || err);
        await delay(3000);
      }
    }
  })();
}

// === COMANDOS ADMIN (mantidos + ajustes) ===
async function processAdminCommand(cmd, msg) {
  try {
    if (cmd === '$help') {
      await msg.reply(`*COMANDOS ADMIN:*\n$global=mensagem - Envia msg para todos\n$file=arquivo - Envia arquivo\n$delay=XXXX - Altera delay\n$pergunta=Pergunta $resposta=Resposta\n$removerpergunta=Pergunta\n$listarperguntas\n$pause / $resume\n$status\n$updatecontacts\n$reconnect / $restart\n...`);
    } else if (cmd.startsWith('$global=')) {
      const data = cmd.replace('$global=', '').trim();
      if (data.includes(' + ')) {
        const [mensagem, arquivo] = data.split(' + ').map(v => v.trim());
        const filepath = path.join(FILES_DIR, arquivo);
        if (!fs.existsSync(filepath)) { await msg.reply(`[Erro] Arquivo '${arquivo}' não encontrado.`); return; }
        await enqueueCampaign({ type: 'message+file', message: mensagem, filename: arquivo, tag: null, campaignId: `global_${moment().format('YYYYMMDD_HHmmss')}` });
        await msg.reply(`[SUCESSO] Job enfileirado para ${contatos.length} contatos.`);
      } else {
        await enqueueCampaign({ type: 'message', message: data, filename: null, tag: null, campaignId: `global_${moment().format('YYYYMMDD_HHmmss')}` });
        await msg.reply(`[SUCESSO] Job enfileirado para ${contatos.length} contatos.`);
      }
    } else if (cmd.startsWith('$file=')) {
      const filename = cmd.replace('$file=', '').trim();
      const filepath = path.join(FILES_DIR, filename);
      if (!fs.existsSync(filepath)) { await msg.reply(`[Erro] Arquivo '${filename}' não encontrado.`); return; }
      await enqueueCampaign({ type: 'file', message: null, filename, tag: null, campaignId: `file_${moment().format('YYYYMMDD_HHmmss')}` });
      await msg.reply(`[SUCESSO] Arquivo enfileirado para ${contatos.length} contatos.`);
    } else if (cmd.startsWith('$delay=')) {
      const delayVal = parseInt(cmd.replace('$delay=', '').trim());
      if (isNaN(delayVal) || delayVal < 500) { await msg.reply('[Erro] Delay inválido (mínimo 500ms).'); return; }
      const config = safeReadJSON(CONFIG_FILE, {});
      config.delayBetweenMessages = delayVal;
      dynamicDelay = delayVal;
      safeWriteJSON(CONFIG_FILE, config);
      await msg.reply(`[Config] Delay entre mensagens atualizado para ${delayVal}ms`);
    } else if (cmd.startsWith('$pergunta=')) {
      const parts = cmd.split('$resposta=');
      if (parts.length !== 2) { await msg.reply('[Erro] Formato inválido. Use: $pergunta=Pergunta $resposta=Resposta'); return; }
      const pergunta = parts[0].replace('$pergunta=', '').trim();
      const resposta = parts[1].trim();
      if (!pergunta || !resposta) { await msg.reply('[Erro] Pergunta e resposta não podem estar vazias.'); return; }
      const responses = safeReadJSON(RESPONSES_FILE, {});
      responses[pergunta] = resposta;
      saveResponses(responses);
      await msg.reply(`[AUTO-RESPOSTA] Configurado: "${pergunta}" → "${resposta}"`);
    } else if (cmd.startsWith('$removerpergunta=')) {
      const pergunta = cmd.replace('$removerpergunta=', '').trim();
      const responses = safeReadJSON(RESPONSES_FILE, {});
      if (responses.hasOwnProperty(pergunta)) { delete responses[pergunta]; saveResponses(responses); await msg.reply(`[AUTO-RESPOSTA] Removido: "${pergunta}"`); }
      else { await msg.reply(`[AUTO-RESPOSTA] Pergunta "${pergunta}" não encontrada.`); }
    } else if (cmd === '$listarperguntas') {
      const responses = safeReadJSON(RESPONSES_FILE, {});
      if (Object.keys(responses).length === 0) await msg.reply('[AUTO-RESPOSTA] Nenhuma pergunta configurada.');
      else {
        let reply = '[AUTO-RESPOSTAS CONFIGURADAS]\n';
        for (const [pergunta, resposta] of Object.entries(responses)) reply += `- "${pergunta}" → "${resposta}"\n`;
        await msg.reply(reply);
      }
    } else if (cmd === '$pause') {
      if (!isSending && loadQueue().length === 0) { await msg.reply('[Erro] Nenhum envio em andamento.'); return; }
      isPaused = true; await msg.reply('[PAUSA] Envio pausado.');
    } else if (cmd === '$resume') {
      isPaused = false; await msg.reply('[RETOMAR] Envio continuando.');
    } else if (cmd === '$status') {
      if (!isSending && loadQueue().length === 0) { await msg.reply('[STATUS] Sem envios em andamento.'); return; }
      const elapsed = currentSending.startTime ? ((new Date() - currentSending.startTime) / 1000).toFixed(1) : '0.0';
      const progress = currentSending.total ? (((currentSending.sent + currentSending.failed) / currentSending.total) * 100).toFixed(1) : '0.0';
      let reply = '[STATUS DO ENVIO]\n';
      reply += `- Progresso: ${progress}%\n`;
      reply += `- Tempo decorrido: ${elapsed}s\n`;
      reply += `- Enviados: ${currentSending.sent}\n`;
      reply += `- Falhas: ${currentSending.failed}\n`;
      reply += `- Restantes: ${Math.max(0, currentSending.total - currentSending.sent - currentSending.failed)}\n`;
      reply += `- Status: ${isPaused ? 'PAUSADO' : 'EM ANDAMENTO'}\n`;
      reply += `- Delay atual: ${dynamicDelay}ms\n`;
      await msg.reply(reply);
    } else if (cmd === '$updatecontacts') {
      await updateContacts(client);
      await msg.reply(`[CONTATOS] ${contatos.length} contatos carregados.`);
    } else if (cmd.startsWith('$scheduletag=')) {
      const parts = cmd.replace('$scheduletag=', '').split('|').map(s => s.trim());
      const whenPart = parts.find(p => /^\d{4}-\d{2}-\d{2} \d{2}:\d{2}/.test(p));
      if (!whenPart) { await msg.reply('[Erro] Data/Hora inválida'); return; }
      const when = whenPart;
      const obj = { when: new Date(when).toISOString() };
      for (const p of parts) {
        if (p.startsWith('type=')) obj.type = p.replace('type=', '');
        if (p.startsWith('message=')) obj.message = p.replace('message=', '');
        if (p.startsWith('file=')) obj.filename = p.replace('file=', '');
        if (p.startsWith('tag=')) obj.tag = p.replace('tag=', '');
      }
      const id = addScheduleItem(obj);
      await msg.reply(`[SCHEDULE] Agendado com ID ${id}`);
    } else if (cmd === '$listschedules') {
      const sched = listSchedules();
      if (!sched.length) { await msg.reply('[SCHEDULE] Nenhum agendamento.'); return; }
      let r = '[SCHEDULES]\n';
      sched.forEach(s => r += `- ID:${s.id} Quando:${s.when} Tipo:${s.type} Tag:${s.tag || '-'}\n`);
      await msg.reply(r);
    } else if (cmd.startsWith('$delschedule=')) {
      const id = cmd.replace('$delschedule=', '').trim();
      removeScheduleItem(id);
      await msg.reply(`[SCHEDULE] Removido ${id}`);
    } else if (cmd === '$listqueue') {
      const q = listQueue();
      if (!q.length) { await msg.reply('[QUEUE] Nenhuma job na fila.'); return; }
      let r = '[QUEUE]\n';
      q.forEach(j => r += `- ID:${j.id} Tipo:${j.type} Targets:${j.targets.length}\n`);
      await msg.reply(r);
    } else if (cmd.startsWith('$canceljob=')) {
      const id = cmd.replace('$canceljob=', '').trim();
      removeJob(id);
      await msg.reply(`[QUEUE] Job ${id} removido.`);
    } else if (cmd === '$genreport') {
      const rep = generateAdvancedReport();
      if (!rep) { await msg.reply('[Sistema Geral] Erro ao gerar relatório.'); return; }
      for (const a of loadAdmins()) {
        try {
          await client.sendMessage(a, `📊 Relatório avançado gerado.\nResumo: Enviados ${rep.stats.sent}, Falhas ${rep.stats.failed}\nCSV salvo no servidor: ${path.basename(rep.csvPath)}`);
        } catch (err) { colorLog('warning', '[Sistema Geral] Falha ao notificar admin sobre relatório:', err.message); }
      }
      await msg.reply('[Sistema Geral] Relatório gerado e admins notificados no chat.');
    } else if (cmd === '$reconnect') {
      await msg.reply('[Sistema Geral] Reiniciando conexão...');
      try { if (client) await client.destroy().catch(() => {}); await delay(3000); client = initializeClient(); }
      catch { await msg.reply('[ERRO CRÍTICO] Falha na reconexão.'); }
    } else if (cmd === '$restart') {
      await msg.reply('[Sistema Geral] Reiniciando bot...');
      gerarLogHTML();
      exec(`node "${__filename}"`);
      process.exit(0);
    } else {
      await msg.reply('[Erro] Comando inválido. Digite $help para ajuda.');
    }
  } catch (err) {
    await msg.reply(`[Erro] Ocorreu um erro: ${err.message}`);
    colorLog('error', '[Erro] Ao processar comando administrativo:', err);
  }
}

// === ENFILEIRAR CAMPANHA ===
async function enqueueCampaign({ type = 'message', message = '', filename = null, tag = null, campaignId = null }) {
  let targets = [];
  if (tag) targets = resolveTargetsForTag(tag);
  else targets = contatos.map(c => c.id);

  const campaign = campaignId || `campaign_${moment().format('YYYYMMDD_HHmmss')}`;
  const uniqueTargets = [...new Set(targets)];
  const filtered = uniqueTargets.filter(contactId => !wasSentRecently(contactId, campaign));
  if (!filtered.length) { colorLog('warning', '[ENQUEUE] Nenhum target elegível (todos duplicados recentes).'); return null; }

  // atualiza status de envio atual
  currentSending = {
    type,
    content: filename ? `${message || ''} + ${filename}` : message,
    total: filtered.length,
    sent: 0,
    failed: 0,
    startTime: new Date(),
    entries: []
  };

  const job = createJob({ type, message, filename, targets: filtered, tag, campaignId: campaign });
  if (!queueProcessor) startQueueProcessor(client);
  isSending = true;
  return job;
}

// === FINALIZAR/LOG ===
function finalizarEnvio() {
  const elapsed = ((new Date() - currentSending.startTime) / 1000).toFixed(1);
  colorLog('success', `\n[Sistema Geral] Operação de envio interna: ${elapsed}s.`);
  console.log(`- Total previstos: ${currentSending.total}`);
  console.log(`- Enviados: ${currentSending.sent}`);
  console.log(`- Falhas: ${currentSending.failed}`);

  const hist = loadSentHistory();
  const toPersist = (currentSending.entries || []).map(e => ({
    contactId: e.contact,
    campaignId: e.campaignId || 'unknown',
    status: e.status,
    reason: e.reason || null,
    time: e.time
  }));
  safeWriteJSON(SENT_HISTORY_FILE, hist.concat(toPersist));

  safeWriteJSON(PROGRESS_FILE, { lastIndex: 0 });
  gerarLogHTML();
  isSending = false;
  dynamicDelay = safeReadJSON(CONFIG_FILE, {}).delayBetweenMessages || dynamicDelay;
}

// === BACKUP + LOG HTML ===
async function backupProgress() {
  try {
    const timestamp = moment().format('YYYY-MM-DD_HH-mm-ss');
    const backupFile = path.join(BACKUP_DIR, `backup_${timestamp}.json`);
    const backupData = {
      config: safeReadJSON(CONFIG_FILE, {}),
      contacts: contatos,
      progress: safeReadJSON(PROGRESS_FILE, {}),
      sendingStatus: currentSending,
      responses: safeReadJSON(RESPONSES_FILE, {}),
      admins: loadAdmins(),
      queue: loadQueue()
    };
    fs.writeFileSync(backupFile, JSON.stringify(backupData, null, 2));
  } catch (err) {
    colorLog('error', '[Erro] Falha ao criar backup:', err);
  }
}
function gerarLogHTML() {
  try {
    const timestamp = moment().format('YYYY-MM-DD_HH-mm-ss');
    const htmlPath = path.join(LOG_DIR, `log_${timestamp}.html`);
    let rows = '';
    (currentSending.entries || []).forEach((e, idx) => {
      rows += `<tr>
                <td>${idx + 1}</td>
                <td>${e.contact}</td>
                <td>${e.status}</td>
                <td>${e.reason ? e.reason : '-'}</td>
                <td>${e.time}</td>
                <td>${e.campaignId || '-'}</td>
            </tr>`;
    });
    const html = `
<!DOCTYPE html><html><head><meta charset="utf-8"/><title>Log de Envios - ${timestamp}</title>
<style>body{font-family:Arial;margin:20px}h1{color:#075e54}table{width:100%;border-collapse:collapse}th,td{border:1px solid #ddd;padding:8px}th{background:#075e54;color:#fff}</style>
</head><body>
<h1>Relatório de Envios - WWW.TONCH.COM.BR</h1>
<div><strong>Tipo:</strong> ${currentSending.type}</div>
<div><strong>Conteúdo:</strong> ${currentSending.content || '-'}</div>
<div style="margin-top:8px"><strong>Total:</strong> ${currentSending.total}</div>
<div><strong>Enviados:</strong> ${currentSending.sent}</div>
<div><strong>Falhas:</strong> ${currentSending.failed}</div>
<div><strong>Início:</strong> ${currentSending.startTime ? currentSending.startTime.toLocaleString() : '-'}</div>
<div><strong>Fim:</strong> ${new Date().toLocaleString()}</div>
<h2>Detalhes</h2>
<table><thead><tr><th>#</th><th>Contato</th><th>Status</th><th>Motivo</th><th>Hora</th><th>Campaign</th></tr></thead><tbody>${rows}</tbody></table>
</body></html>`;
    fs.writeFileSync(htmlPath, html);
    colorLog('success', `[Sistema Geral] Relatório salvo em ${path.basename(LOG_DIR)}/${path.basename(htmlPath)}`);
  } catch (err) {
    colorLog('error', '[Erro] Falha ao gerar log HTML:', err);
  }
}

// === CLIENTE WWebJS (headless VPS seguro) ===
function initializeClient() {
  colorLog('info', '[Sistema Geral] Criando nova instância do cliente...');
  const config = safeReadJSON(CONFIG_FILE, {});
  dynamicDelay = config.delayBetweenMessages;

  // Permite definir caminho fixo do Chromium via variável de ambiente (VPS)
  const executablePath = process.env.PUPPETEER_EXECUTABLE_PATH || process.env.CHROMIUM_PATH || undefined;

  const newClient = new Client({
    authStrategy: new LocalAuth({
      clientId: 'whatsapp-bot-session',
      dataPath: path.join(BASE_DIR, 'whatsapp-bot-session')
    }),
    puppeteer: {
      headless: true,
      executablePath, // usa se definido; senão, puppeteer internal
      args: [
        '--no-sandbox',
        '--disable-setuid-sandbox',
        '--disable-dev-shm-usage',
        '--disable-accelerated-2d-canvas',
        '--no-first-run',
        '--no-zygote',
        '--single-process',
        '--disable-gpu',
        '--disable-extensions',
        '--disable-background-networking',
        '--disable-background-timer-throttling',
        '--disable-breakpad',
        '--disable-client-side-phishing-detection',
        '--disable-default-apps',
        '--disable-features=site-per-process',
        '--mute-audio'
      ],
      timeout: 60000
    },
    restartOnAuthFail: true,
    takeoverOnConflict: true,
    qrTimeout: 60000
  });

  newClient.on('qr', qr => {
    qrCodeGenerated = true;
    currentQrCode = qr;
    qrcode.generate(qr, { small: true });
    colorLog('info', '\n[Sistema Geral] Escaneie este código com seu WhatsApp:');
    console.log('1. Abra o WhatsApp no seu celular');
    console.log('2. ⋮ → Dispositivos vinculados → Vincular um dispositivo');
    console.log('3. Aponte a câmera para o QR code acima\n');
  });

  newClient.on('ready', async () => {
    colorLog('success', '\n[Sistema Geral] WhatsApp conectado com sucesso! Site Oficial: WWW.TONCH.COM.BR');
    clientReady = true;
    qrCodeGenerated = false;
    await updateContacts(newClient);
    showHelp();

    // Notifica admins (startup)
    try {
      const publicIp = await getPublicIP(5000);
      const localIps = Object.values(os.networkInterfaces()).flat().filter(Boolean).map(i => i.address).join(', ');
      const user = os.userInfo().username;
      const hostname = os.hostname();
      const startedAt = new Date().toLocaleString();
      const cfg = safeReadJSON(CONFIG_FILE, {});
      const msg = `🤖 *TonchB0T*\nStatus: Online\nVersao: 1.0 - By Gabriel Perdigao - Projeto Tonch\nSite: www.tonch.com.br\n\nIniciado por: ${user}\nHost: ${hostname}\nData/Hora: ${startedAt}\nIP Público: ${publicIp}\nIP Locais: ${localIps}\nDelay: ${cfg.delayBetweenMessages || 'N/A'}ms`;
      admins = loadAdmins();
      if (!admins.length) colorLog('warning', '[Sistema Geral] Nenhum admin para notificar sobre a inicialização.');
      else {
        for (const admin of admins) {
          try { await newClient.sendMessage(admin, msg); colorLog('success', `[Sistema Geral] Startup enviada para ${admin.replace('@c.us', '')}`); }
          catch (err) { colorLog('error', `[Sistema Geral] Falha ao enviar startup para ${admin}: ${err.message}`); }
        }
      }
    } catch (err) {
      colorLog('error', '[Sistema Geral] Erro ao notificar admins sobre startup:', err.message || err);
    }

    // Inicia agendador e fila
    startScheduleLoop();
    startQueueProcessor(newClient);
  });

  newClient.on('authenticated', () => colorLog('success', '[Sistema Geral] Autenticação realizada!'));
  newClient.on('auth_failure', msg => colorLog('error', '[Erro] Falha na autenticação:', msg));

  newClient.on('disconnected', async (reason) => {
    colorLog('warning', '\n[Sistema Geral] Desconectado:', reason);
    clientReady = false;

    // Notifica admins (desconectado)
    try {
      for (const admin of loadAdmins()) {
        try { await newClient.sendMessage(admin, `⚠️ TonchB0T desconectado. Motivo: ${reason || 'desconhecido'}`); }
        catch {}
      }
    } catch {}

    const cfg = safeReadJSON(CONFIG_FILE, {});
    if (cfg.autoReconnect) {
      colorLog('info', '[Sistema Geral] Tentando reconectar automaticamente em 30 segundos...');
      setTimeout(() => initializeClient(), 30000);
    }
  });

  // ignora grupos
  newClient.on('message', async msg => {
    try {
      if (msg.fromMe) return;
      if (msg.from && msg.from.endsWith('@g.us')) return;
      const isAdmin = loadAdmins().includes(msg.from);
      if (isAdmin && msg.body && msg.body.startsWith('$')) {
        colorLog('info', `[Admin] ${msg.from.replace('@c.us', '')}: ${msg.body}`);
        await processAdminCommand(msg.body, msg);
        return;
      }
      // auto-respostas
      const responses = safeReadJSON(RESPONSES_FILE, {});
      const receivedText = (msg.body || '').toLowerCase().trim();
      for (const [pergunta, resposta] of Object.entries(responses)) {
        try {
          if (receivedText.includes(pergunta.toLowerCase())) {
            await msg.reply(resposta);
            colorLog('info', `[AUTO-RESPOSTA] Para "${pergunta}": "${resposta}"`);
            break;
          }
        } catch (err) { colorLog('error', '[Erro] Ao enviar auto-resposta especifica:', err.message); }
      }
    } catch (err) {
      colorLog('error', '[Erro] manipulador de mensagem:', err);
    }
  });

  newClient.initialize().catch(err => {
    colorLog('error', '[Erro] Falha ao inicializar:', err);
    colorLog('info', '[Tentativa] Tentando novamente em 10 segundos...');
    setTimeout(() => initializeClient(), 10000);
  });

  return newClient;
}

// === ADMINs ===
async function manageAdmins() {
  colorLog('info', '\n[Admin] Configuração de Administradores');
  console.log('1. Adicionar admin');
  console.log('2. Remover admin');
  console.log('3. Listar admins');
  console.log('4. Voltar');
  const choice = await askQuestion('Escolha uma opção: ');
  switch (choice) {
    case '1': await addAdmin(); break;
    case '2': await removeAdmin(); break;
    case '3': listAdmins(); break;
    case '4': return;
    default: colorLog('error', '[Erro] Opção inválida.');
  }
  await manageAdmins();
}
async function addAdmin() {
  const number = await askQuestion('Digite o número do admin (com código do país, ex: 5511999999999): ');
  if (!number.match(/^\d+$/)) { colorLog('error', '[Erro] Número inválido. Use apenas dígitos.'); return; }
  const adminId = `${number}@c.us`;
  const list = loadAdmins();
  if (list.includes(adminId)) { colorLog('warning', '[Admin] Este número já é admin.'); return; }
  list.push(adminId);
  saveAdmins(list);
  colorLog('success', `[Admin] Número ${number} adicionado como admin.`);
}
async function removeAdmin() {
  const list = loadAdmins();
  if (list.length === 0) { colorLog('info', '[Admin] Nenhum admin cadastrado.'); return; }
  listAdmins();
  const idx = parseInt(await askQuestion('Digite o número do admin a ser removido (1, 2, ...): ')) - 1;
  if (isNaN(idx) || idx < 0 || idx >= list.length) { colorLog('error', '[Erro] Índice inválido.'); return; }
  const removed = list.splice(idx, 1);
  saveAdmins(list);
  colorLog('success', `[Admin] Número ${removed[0].replace('@c.us','')} removido.`);
}
function listAdmins() {
  const list = loadAdmins();
  if (!list.length) { colorLog('info', '[Admin] Nenhum admin cadastrado.'); return; }
  colorLog('info', '\n[Lista de Admins]');
  list.forEach((a, i) => console.log(`${i+1}. ${a.replace('@c.us','')}`));
}
function loadAdmins() { return safeReadJSON(ADMINS_FILE, []); }
function saveAdmins(list) { return safeWriteJSON(ADMINS_FILE, list); }

// === HELPERS ===
function delay(ms) { return new Promise(resolve => setTimeout(resolve, ms)); }

// === SEGMENTOS (CLI) ===
async function manageSegments() {
  colorLog('info', '[SEGMENTS] Gerenciamento de segments/tags');
  console.log('1. Adicionar tag a contato');
  console.log('2. Remover tag de contato');
  console.log('3. Listar tags de contato');
  console.log('4. Voltar');
  const choice = await askQuestion('Escolha: ');
  const segs = loadSegments();
  switch (choice) {
    case '1': {
      const contact = await askQuestion('Contato ID (ex: 5511999999999@c.us): ');
      const tag = await askQuestion('Tag a adicionar: ');
      if (!segs[contact]) segs[contact] = [];
      if (!segs[contact].includes(tag)) segs[contact].push(tag);
      saveSegments(segs);
      colorLog('success','Tag adicionada.');
      break;
    }
    case '2': {
      const contact = await askQuestion('Contato ID: ');
      const tag = await askQuestion('Tag a remover: ');
      if (segs[contact]) { segs[contact] = segs[contact].filter(t => t !== tag); saveSegments(segs); colorLog('success','Tag removida.'); }
      else colorLog('warning','Contato sem tags.');
      break;
    }
    case '3': {
      const contact = await askQuestion('Contato ID: ');
      colorLog('info', `Tags: ${(segs[contact]||[]).join(', ')}`);
      break;
    }
    case '4': return;
    default: colorLog('error', 'Opção inválida.');
  }
  await manageSegments();
}

// === CLI ===
const rl = readline.createInterface({ input: process.stdin, output: process.stdout, prompt: 'TonchB0T> ' });
function askQuestion(question) { return new Promise(resolve => { rl.question(question, answer => resolve(answer.trim())); }); }

rl.on('line', async input => {
  const cmdRaw = input.trim();
  const cmd = cmdRaw.toLowerCase();
  try {
    if (cmd === '$manageadmins') {
      await manageAdmins();
    } else if (cmd === '$managesegments') {
      await manageSegments();
    } else if (cmd.startsWith('$global=')) {
      if (!clientReady) return colorLog('error', '[Erro] Aguarde a conexão com WhatsApp.');
      const data = cmdRaw.replace('$global=', '').trim();
      if (!data) return colorLog('error', '[Erro] Mensagem vazia.');
      if (data.includes(' + ')) {
        const [mensagem, arquivo] = data.split(' + ').map(v => v.trim());
        const filepath = path.join(FILES_DIR, arquivo);
        if (!fs.existsSync(filepath)) return colorLog('error', `[Erro] Arquivo '${arquivo}' não encontrado.`);
        await enqueueCampaign({ type: 'message+file', message: mensagem, filename: arquivo, tag: null, campaignId: `global_${moment().format('YYYYMMDD_HHmmss')}` });
        colorLog('success', `Job enfileirado para ${contatos.length}`);
      } else {
        await enqueueCampaign({ type: 'message', message: data, filename: null, tag: null, campaignId: `global_${moment().format('YYYYMMDD_HHmmss')}` });
        colorLog('success', `Job enfileirado para ${contatos.length}`);
      }
    } else if (cmd.startsWith('$globaltag=')) {
      if (!clientReady) return colorLog('error', '[Erro] Aguarde a conexão com WhatsApp.');
      const body = cmdRaw.replace('$globaltag=', '').trim();
      const parts = body.split('|').map(s => s.trim());
      const tag = parts.shift();
      let message = null, filename = null;
      parts.forEach(p => {
        if (p.startsWith('message=')) message = p.replace('message=', '');
        else if (p.startsWith('file=')) filename = p.replace('file=', '');
        else message = message ? message + ' ' + p : p;
      });
      if (!message && !filename) return colorLog('error', '[Erro] Forneça message ou file.');
      const type = filename ? (message ? 'message+file' : 'file') : 'message';
      await enqueueCampaign({ type, message, filename, tag, campaignId: `tag_${tag}_${moment().format('YYYYMMDD_HHmmss')}` });
      colorLog('success', `Job enfileirado para TAG:${tag}`);
    } else if (cmd.startsWith('$file=')) {
      if (!clientReady) return colorLog('error', '[Erro] Aguarde a conexão com WhatsApp.');
      const filename = cmdRaw.replace('$file=', '').trim();
      const filepath = path.join(FILES_DIR, filename);
      if (!fs.existsSync(filepath)) return colorLog('error', `[Erro] Arquivo '${filename}' não encontrado.`);
      await enqueueCampaign({ type: 'file', message: null, filename, tag: null, campaignId: `file_${moment().format('YYYYMMDD_HHmmss')}` });
      colorLog('success', `Job de arquivo enfileirado.`);
    } else if (cmd.startsWith('$delay=')) {
      const delayVal = parseInt(cmdRaw.replace('$delay=', '').trim());
      if (isNaN(delayVal) || delayVal < 500) return colorLog('error', '[Erro] Delay inválido (mínimo 500ms).');
      const config = safeReadJSON(CONFIG_FILE, {});
      config.delayBetweenMessages = delayVal;
      dynamicDelay = delayVal;
      safeWriteJSON(CONFIG_FILE, config);
      colorLog('success', `[Config] Delay atualizado para ${delayVal}ms`);
    } else if (cmd.startsWith('$pergunta=')) {
      const parts = cmdRaw.split('$resposta=');
      if (parts.length !== 2) return colorLog('error', '[Erro] Formato inválido.');
      const pergunta = parts[0].replace('$pergunta=', '').trim();
      const resposta = parts[1].trim();
      if (!pergunta || !resposta) return colorLog('error', '[Erro] Pergunta/Resposta vazia.');
      const responses = safeReadJSON(RESPONSES_FILE, {});
      responses[pergunta] = resposta; safeWriteJSON(RESPONSES_FILE, responses);
      colorLog('success', `[AUTO-RESPOSTA] Configurado: "${pergunta}" → "${resposta}"`);
    } else if (cmd.startsWith('$removerpergunta=')) {
      const pergunta = cmdRaw.replace('$removerpergunta=', '').trim();
      const responses = safeReadJSON(RESPONSES_FILE, {});
      if (responses.hasOwnProperty(pergunta)) { delete responses[pergunta]; safeWriteJSON(RESPONSES_FILE, responses); colorLog('success', 'Removido.'); }
      else colorLog('warning', 'Pergunta não encontrada.');
    } else if (cmd === '$listarperguntas') {
      const responses = safeReadJSON(RESPONSES_FILE, {});
      if (!Object.keys(responses).length) colorLog('info', 'Nenhuma auto-resposta.');
      else { colorLog('info', '[AUTO-RESPOSTAS ESPECIFICAS]'); for (const [k,v] of Object.entries(responses)) console.log(`- ${k} => ${v}`); }
    } else if (cmd === '$pause') {
      isPaused = true; colorLog('warning', 'Envio pausado.');
    } else if (cmd === '$resume') {
      isPaused = false; colorLog('success', 'Envio retomado.');
    } else if (cmd === '$status') {
      showStatus();
    } else if (cmd === '$updatecontacts') {
      if (!clientReady) return colorLog('error', '[Erro] Aguarde conexão.'); await updateContacts(client);
    } else if (cmd === '$listschedules') {
      const s = listSchedules(); if (!s.length) colorLog('info','Nenhum agendamento encontrado'); else s.forEach(x => console.log(`${x.id} | ${x.when} | ${x.type} | ${x.tag || '-'}`));
    } else if (cmd.startsWith('$scheduletag=')) {
      const body = cmdRaw.replace('$scheduletag=', '').trim();
      const parts = body.split('|').map(s => s.trim());
      const whenPart = parts.shift();
      const obj = { when: new Date(whenPart).toISOString() };
      parts.forEach(p => { if (p.startsWith('type=')) obj.type = p.replace('type=',''); else if (p.startsWith('message=')) obj.message = p.replace('message=',''); else if (p.startsWith('file=')) obj.filename = p.replace('file=',''); else if (p.startsWith('tag=')) obj.tag = p.replace('tag=',''); });
      const id = addScheduleItem(obj); colorLog('success', `Agendamento criado: ${id}`);
    } else if (cmd === '$listqueue') {
      const q = loadQueue(); if (!q.length) colorLog('info','Fila vazia'); else q.forEach(j => console.log(`${j.id} | ${j.type} | targets:${j.targets.length} | campaign:${j.campaignId}`));
    } else if (cmd.startsWith('$canceljob=')) {
      const id = cmdRaw.replace('$canceljob=', '').trim(); removeJob(id); colorLog('success', `Job ${id} cancelado`);
    } else if (cmd === '$genreport') {
      const rep = generateAdvancedReport();
      if (!rep) colorLog('error','Erro ao gerar relatório'); else colorLog('success', `Relatório gerado: ${path.basename(rep.csvPath)}`);
    } else if (cmd === '$openfiles') {
      open(FILES_DIR).then(() => colorLog('success', `Pasta aberta: ${FILES_DIR}`)).catch(err => colorLog('error','Falha ao abrir pasta', err));
    } else if (cmd === '$listfiles') {
      const files = fs.readdirSync(FILES_DIR); if (!files.length) colorLog('info','Nenhum arquivo'); else files.forEach(f => console.log('- ' + f));
    } else if (cmd === '$reconnect') {
      colorLog('info', 'Reconectando...'); if (client) await client.destroy().catch(()=>{}); client = initializeClient();
    } else if (cmd === '$logout') {
      colorLog('info','Desconectando sessão...'); await cleanSession(); client = initializeClient();
    } else if (cmd === '$showqr') {
      if (qrCodeGenerated && currentQrCode) { qrcode.generate(currentQrCode, { small: true }); colorLog('success','QR exibido'); } else colorLog('warning','Nenhum QR disponível');
    } else if (cmd === '$autoreconnect') {
      const cfg = safeReadJSON(CONFIG_FILE, {}); cfg.autoReconnect = !cfg.autoReconnect; safeWriteJSON(CONFIG_FILE, cfg); colorLog('success', `AutoReconnect ${cfg.autoReconnect ? 'ativado' : 'desativado'}`);
    } else if (cmd === '$shutdown' || cmd === '$exit') {
      colorLog('info', '[SAIR] Encerrando bot...'); gerarLogHTML(); if (client) await client.destroy().catch(()=>{}); process.exit(0);
    } else if (cmd === '$help') {
      showHelp();
    } else if (cmd === 'clear' || cmd === 'cls') {
      console.clear();
    } else if (cmd) {
      colorLog('error', '[Erro] Comando inválido. Digite $help para ajuda.');
    }
  } catch (err) {
    colorLog('error', '[Erro] Ocorreu um erro:', err.message || err);
  }
  rl.prompt();
}).on('close', () => { colorLog('info','[SISTEMA] Encerrando bot...'); process.exit(0); });

// === LIMPEZA DE SESSÃO ===
async function cleanSession() {
  try {
    if (client) await client.destroy().catch(() => {});
    fs.rmSync(path.join(BASE_DIR, 'whatsapp-bot-session'), { recursive: true, force: true });
    colorLog('success', '[SESSÃO] Limpeza completa da sessão anterior');
  } catch (err) { colorLog('error','[Erro] Falha ao limpar sessão:', err.message || err); }
}

// === STATUS & HELP ===
function showStatus() {
  const q = loadQueue();
  colorLog('info', '\n[STATUS DO TONCH BOT]');
  console.log(`- Client ready: ${clientReady}`);
  console.log(`- Contatos: ${contatos.length}`);
  console.log(`- Fila: ${q.length} jobs`);
  console.log(`- Enviando: ${isSending}`);
  console.log(`- Pausado: ${isPaused}`);
  if (isSending) {
    const elapsed = ((new Date() - currentSending.startTime) / 1000).toFixed(1);
    const progress = currentSending.total ? (((currentSending.sent + currentSending.failed) / currentSending.total) * 100).toFixed(1) : 0;
    console.log(`- Progresso envio atual: ${progress}% (sent:${currentSending.sent}, failed:${currentSending.failed})`);
    console.log(`- Tempo decorrido: ${elapsed}s`);
  }
}
function showHelp() {
  console.log(`
╔════════════════════════════════════════════╗
║          TONCH BOT - COMANDOS              ║
╠════════════════════════════════════════════╣
║  $global=mensagem           → Envia msg    ║
║  $global=mensagem + arq.ext → Msg + arquivo║
║  $globaltag=TAG|message=..  → Envia por tag║
║  $file=arquivo.ext          → Envia arquivo║
║  $delay=XXXX                → Altera delay ║
╠════════════════════════════════════════════╣
║  $pergunta=Pergunta $resposta=Resposta     ║
║  $removerpergunta=Pergunta  → Remove resp. ║
║  $listarperguntas           → Lista resp.  ║
║  $manageadmins              → Gerenciar Admins
║  $managesegments            → Gerenciar TAGS/SEGMENTOS
╠════════════════════════════════════════════╣
║  $pause / $resume           → Pausa/Retoma ║
║  $status                    → Mostra status║
║  $listschedules / $scheduletag=...         ║
║  $listqueue / $canceljob=ID  → Gerencia fila║
║  $genreport                 → Relatório    ║
╠════════════════════════════════════════════╣
║  $updatecontacts → Atualiza contatos       ║
║  $openfiles      → Abre pasta de arquivos  ║
║  $listfiles      → Lista arquivos          ║
╠════════════════════════════════════════════╣
║  $reconnect      → Reconecta ao WhatsApp   ║
║  $logout         → Sai da sessão atual     ║
║  $showqr         → Mostra QR code novamente║
║  $autoreconnect  → Ativa/Desativa auto-recon
╠════════════════════════════════════════════╣
║  $restart / $shutdown / $help              ║
╚════════════════════════════════════════════╝
`);
}

// === ERROS GLOBAIS ===
process.on('unhandledRejection', (reason) => {
  colorLog('error', '[ERRO NÃO TRATADO]', reason);
  setTimeout(() => { if (client) client.destroy().then(() => { client = initializeClient(); }); }, 5000);
});
process.on('uncaughtException', (err) => {
  colorLog('error', '[ERRO CRÍTICO]', err);
  setTimeout(() => process.exit(1), 10000);
});

// === RELATÓRIO SEMANAL (opcional) ===
let weeklyReportTimer = null;
function scheduleWeeklyReports(clientInstance) {
  if (!clientInstance || !clientReady) {
    if (!weeklyReportTimer) weeklyReportTimer = setTimeout(() => { weeklyReportTimer = null; scheduleWeeklyReports(clientInstance); }, 60_000);
    return;
  }
  if (global._weeklyScheduled) return;
  global._weeklyScheduled = true;
  const weekMs = 7 * 24 * 60 * 60 * 1000;
  setTimeout(async () => {
    await sendWeeklyReport(clientInstance);
    setInterval(() => sendWeeklyReport(clientInstance).catch(err => colorLog('error','[Sistema Geral] sendWeeklyReport',err)), weekMs);
  }, 60_000);
}
async function sendWeeklyReport(clientInstance) {
  try {
    const rep = generateAdvancedReport();
    const adminsList = loadAdmins();
    if (!adminsList.length) { colorLog('info','[Sistema Geral] Nenhum admin para enviar relatório semanal.'); return; }
    const message = `📊 Relatório Semanal - Tonch\nEnviados: ${rep ? rep.stats.sent : 'N/A'} | Falhas: ${rep ? rep.stats.failed : 'N/A'}\nVer arquivos no servidor.`;
    for (const a of adminsList) {
      try {
        await clientInstance.sendMessage(a, message);
        if (rep && fs.existsSync(rep.csvPath)) {
          const csvMedia = MessageMedia.fromFilePath(rep.csvPath);
          await clientInstance.sendMessage(a, csvMedia);
        }
      } catch (err) { colorLog('warning','[Sistema Geral] Falha ao enviar relatório semanal para', a, err.message); }
    }
  } catch (err) { colorLog('error','[Sistema Geral] Erro ao enviar relatório semanal:', err); }
}

// === NOTIFICAÇÃO DE SHUTDOWN GRACIOSO ===
async function notifyShutdown(reason) {
  try {
    for (const a of loadAdmins()) {
      try { await client.sendMessage(a, `🛑 TonchB0T encerrando (${reason || 'desconhecido'}).`); } catch {}
    }
  } catch {}
}
['SIGINT','SIGTERM'].forEach(sig => {
  process.on(sig, async () => {
    try { await notifyShutdown(sig); } catch {}
    try { gerarLogHTML(); } catch {}
    try { if (client) await client.destroy().catch(()=>{}); } catch {}
    process.exit(0);
  });
});

// === BANNER & BOOT ===
console.log(`
╔════════════════════════════════════════════╗
║                  Tonch BOT                 ║
╠════════════════════════════════════════════╣
║  VERSAO 1.0 - By Gabriel Perdigao          ║
║  Projeto Tonch - site www.tonch.com.br     ║
╚════════════════════════════════════════════╝
`);

function saveResponses(obj){ safeWriteJSON(RESPONSES_FILE, obj); }

setupDirectories();
preStartAnalysis();
admins = loadAdmins();
client = initializeClient();
startScheduleLoop();
rl.prompt();
