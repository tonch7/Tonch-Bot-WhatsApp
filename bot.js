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

// ------------------------
// Configuracoes - CONFIG
// ------------------------
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

// ------------------------
// Console colors
// ------------------------
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

// ------------------------
// Helpers: safe JSON read/write
// ------------------------
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

// ------------------------
// Pre-start analysis, ensure dirs & files
// ------------------------
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
            maxMessagesPerMinute: 20,
            weeklyReportHourUTC: 12,
            concurrency: 2, // envio assíncrono simultâneo
            duplicateWindowDays: 30, // evitar duplicados dentro de X dias
            duplicateIgnoreIfOlderThanDays: 365 // histórico de long time
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
    // permissões
    [LOG_DIR, FILES_DIR, BACKUP_DIR].forEach(dir => {
        try { fs.accessSync(dir, fs.constants.R_OK | fs.constants.W_OK); } catch (err) { issues.push(`Permissão incoerente: ${dir}`); }
    });
    // config valid
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

// ------------------------
// Network utilities
// ------------------------
function getPublicIP(timeout = 5000) {
    return new Promise((resolve) => {
        try {
            const req = https.get('https://api.ipify.org?format=json', (res) => {
                let data = '';
                res.on('data', chunk => data += chunk);
                res.on('end', () => {
                    try {
                        const json = JSON.parse(data);
                        resolve(json.ip || 'unknown');
                    } catch { resolve('unknown'); }
                });
            });
            req.on('error', () => resolve('unknown'));
            req.setTimeout(timeout, () => { req.abort(); resolve('timeout'); });
        } catch {
            resolve('unknown');
        }
    });
}

// ------------------------
// State
// ------------------------
let contatos = [];
let isSending = false;
let isPaused = false;
let dynamicDelay = 3500;
let currentSending = {
    type: null,
    content: null,
    total: 0,
    sent: 0,
    failed: 0,
    startTime: null,
    entries: []
};
let clientReady = false;
let qrCodeGenerated = false;
let currentQrCode = null;
let client = null;
let admins = safeReadJSON(ADMINS_FILE, []);
let queueProcessor = null;

// ------------------------
// Sent history (duplicate control)
// ------------------------
function loadSentHistory() {
    return safeReadJSON(SENT_HISTORY_FILE, []);
}
function saveSentHistory(history) {
    // prune old entries older than duplicateIgnoreIfOlderThanDays
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

// ------------------------
// Queue system (persisted) - supports jobs and concurrency/throttling
// job structure: { id, type: 'message'|'file'|'message+file', message, filename, targets: [contactIds], tag (optional), campaignId, scheduledFrom }
// ------------------------
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

// ------------------------
// Scheduler (loads SCHEDULE_FILE and enqueues jobs when time arrives)
// schedule item: { id, when: ISO, type, message, filename, tag, campaignId }
// ------------------------
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

// Scheduler loop
function startScheduleLoop() {
    setInterval(async () => {
        const schedules = loadSchedules();
        const now = Date.now();
        for (const s of schedules.slice()) {
            const when = new Date(s.when).getTime();
            if (!when || isNaN(when)) continue;
            if (when <= now) {
                // enqueue job using segments/tags/resolved targets
                try {
                    const targets = resolveTargetsForSchedule(s);
                    if (targets.length === 0) {
                        colorLog('warning', `[SCHEDULE] Nenhum target para schedule ${s.id}`);
                    } else {
                        createJob({
                            type: s.type,
                            message: s.message,
                            filename: s.filename,
                            targets,
                            tag: s.tag,
                            campaignId: s.campaignId || s.id,
                            scheduledFrom: s.id
                        });
                        colorLog('info', `[SCHEDULE] Agendado enfileirado job para schedule ${s.id} (${targets.length} contatos)`);
                    }
                } catch (err) {
                    colorLog('error', '[SCHEDULE] Erro ao enfileirar schedule:', err.message || err);
                } finally {
                    // remove schedule item executed once
                    removeScheduleItem(s.id);
                }
            }
        }
    }, 30_000); // a cada 30s
}

// ------------------------
// Segments (mapping contactId -> [tags])
// ------------------------
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
    // if explicit list provided:
    if (Array.isArray(schedule.targets) && schedule.targets.length) return schedule.targets;
    // fallback to all non-group contacts
    return contatos.map(c => c.id);
}

// ------------------------
// Update contacts (ignore groups)
 // ------------------------
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

// ------------------------
// Create MessageMedia with size check
// ------------------------
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

// ------------------------
// Advanced reports (CSV + HTML) generation
// ------------------------
function generateCSVReport(entries, filename) {
    // entries: array of {contact, status, reason, time, campaignId}
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
        // gather recent logs / backups
        const history = loadSentHistory();
        const recent = history.slice(-500); // last 500 entries
        const stats = {
            total: recent.length,
            sent: recent.filter(r => r.status === 'sent').length,
            failed: recent.filter(r => r.status !== 'sent').length,
            timeframeStart: recent.length ? recent[0].time : '-',
            timeframeEnd: recent.length ? recent[recent.length - 1].time : '-'
        };
        // create CSV
        const csvName = `report_${moment().format('YYYY-MM-DD_HH-mm-ss')}.csv`;
        const csvPath = generateCSVReport(recent, csvName);
        // create small summary HTML
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

// ------------------------
// Sending primitives (single contact) - return promise that resolves status
// ------------------------
async function sendToContactSingle(clientInstance, contatoId, job) {
    // job: { type, message, filename, campaignId }
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

// ------------------------
// Queue processor (concurrency + throttling + duplicates + safe pauses)
// ------------------------
async function startQueueProcessor(clientInstance) {
    if (queueProcessor) return; // already running
    queueProcessor = true;
    colorLog('info', '[QUEUE] Iniciando processador de fila...');
    (async function loop() {
        while (true) {
            try {
                if (!clientInstance || !clientReady) {
                    await delay(2000);
                    continue;
                }
                let queue = loadQueue();
                if (!queue.length) {
                    await delay(1000);
                    continue;
                }

                const cfg = safeReadJSON(CONFIG_FILE, {});
                const concurrency = Math.max(1, cfg.concurrency || 2);
                const maxPerMinute = cfg.maxMessagesPerMinute || 20;
                const safeBatchSize = cfg.safeBatchSize || 50;
                const safeBatchPauseMs = cfg.safeBatchPauseMs || 60000;

                // Process first job in queue (FIFO)
                const job = queue[0];
                if (!job) { await delay(1000); continue; }

                // job.targets is array of contact ids
                const targets = Array.isArray(job.targets) ? job.targets.slice() : [];
                if (!targets.length) {
                    // remove job and continue
                    removeJob(job.id);
                    continue;
                }

                // Break targets into chunks to respect concurrency & minutely quota
                // We'll process chunk by chunk
                const chunkSize = Math.max(1, Math.min(concurrency, 10));
                const chunk = targets.splice(0, chunkSize);

                // For each contact in chunk, check duplicates and send asynchronously
                const sendPromises = chunk.map(async (contactId) => {
                    // duplicate control
                    if (wasSentRecently(contactId, job.campaignId || 'default')) {
                        colorLog('warning', `[DUP] Pular ${contactId} — já recebeu campanha ${job.campaignId}`);
                        currentSending.entries.push({ contact: contactId, status: 'skipped_duplicate', time: new Date().toISOString(), campaignId: job.campaignId });
                        recordSent(contactId, job.campaignId, 'skipped_duplicate', 'duplicate_recent');
                        return;
                    }
                    // send with retries
                    const maxRetries = (cfg.maxRetries || 3);
                    for (let attempt = 0; attempt <= maxRetries; attempt++) {
                        const res = await sendToContactSingle(clientInstance, contactId, job);
                        if (res.status === 'sent') {
                            currentSending.sent++;
                            currentSending.entries.push({ contact: contactId, status: 'sent', time: new Date().toISOString(), campaignId: job.campaignId });
                            recordSent(contactId, job.campaignId, 'sent');
                            break;
                        } else {
                            if (attempt < maxRetries) {
                                colorLog('warning', `[RETRY] Tentativa ${attempt + 1} falhou para ${contactId}: ${res.reason}. Retry...`);
                                await delay(1500 + Math.floor(Math.random() * 1000));
                                continue;
                            } else {
                                currentSending.failed++;
                                currentSending.entries.push({ contact: contactId, status: 'failed', reason: res.reason, time: new Date().toISOString(), campaignId: job.campaignId });
                                recordSent(contactId, job.campaignId, 'failed', res.reason);
                                colorLog('error', `[FAIL] ${contactId} → ${res.reason}`);
                            }
                        }
                    }
                });

                // throttle: ensure we don't exceed max per minute — we do a simple per-loop check
                await Promise.all(sendPromises);

                // update job.targets removing processed chunk
                const remainingTargets = targets; // we mutated a copy earlier
                // update original job in persistent queue
                let q = loadQueue();
                const idx = q.findIndex(j => j.id === job.id);
                if (idx >= 0) {
                    if (remainingTargets.length === 0) {
                        q.splice(idx, 1); // job done
                    } else {
                        q[idx].targets = remainingTargets;
                    }
                    saveQueue(q);
                }

                // small randomized delay between chunks to reduce pattern detection
                await delay((cfg.delayBetweenMessages || dynamicDelay || 3500) + Math.floor(Math.random() * 800) - 300);

                // If processed many contacts (batch), respect safeBatchPauseMs
                const processedCount = chunk.length;
                if (processedCount >= safeBatchSize) {
                    colorLog('info', `[BATCH] Processado ${processedCount} — Pausando ${safeBatchPauseMs / 1000}s`);
                    await delay(safeBatchPauseMs);
                }
            } catch (err) {
                colorLog('error', '[QUEUE] Erro no loop da fila:', err.message || err);
                await delay(3000);
            }
        }
    })();
}

// ------------------------
// Admin commands and CLI: additions for schedule, queue, segments, report, force enqueue
// ------------------------
async function processAdminCommand(cmd, msg) {
    try {
        if (cmd === '$help') {
            await msg.reply(`*COMANDOS ADMIN:*\n$global=mensagem - Envia msg para todos\n$file=arquivo - Envia arquivo\n$delay=XXXX - Altera delay\n$pergunta=Pergunta $resposta=Resposta\n$removerpergunta=Pergunta\n$listarperguntas\n$pause - Pausa envios\n$resume - Retoma envios\n$status - Mostra status\n$updatecontacts - Atualiza contatos\n$reconnect - Reconecta\n$restart - Reinicia bot\nVer mais com $help no console`);
        } else if (cmd.startsWith('$global=')) {
            const data = cmd.replace('$global=', '').trim();
            if (data.includes(' + ')) {
                const [mensagem, arquivo] = data.split(' + ').map(v => v.trim());
                const filepath = path.join(FILES_DIR, arquivo);
                if (!fs.existsSync(filepath)) {
                    await msg.reply(`[Erro] Arquivo '${arquivo}' não encontrado.`);
                    return;
                }
                // enqueue job for all contacts
                await enqueueCampaign({ type: 'message+file', message: mensagem, filename: arquivo, tag: null, campaignId: `global_${moment().format('YYYYMMDD_HHmmss')}` });
                await msg.reply(`[SUCESSO] Job enfileirado para ${contatos.length} contatos.`);
            } else {
                await enqueueCampaign({ type: 'message', message: data, filename: null, tag: null, campaignId: `global_${moment().format('YYYYMMDD_HHmmss')}` });
                await msg.reply(`[SUCESSO] Job enfileirado para ${contatos.length} contatos.`);
            }
        } else if (cmd.startsWith('$file=')) {
            const filename = cmd.replace('$file=', '').trim();
            const filepath = path.join(FILES_DIR, filename);
            if (!fs.existsSync(filepath)) {
                await msg.reply(`[Erro] Arquivo '${filename}' não encontrado.`);
                return;
            }
            await enqueueCampaign({ type: 'file', message: null, filename, tag: null, campaignId: `file_${moment().format('YYYYMMDD_HHmmss')}` });
            await msg.reply(`[SUCESSO] Arquivo enfileirado para ${contatos.length} contatos.`);
        } else if (cmd.startsWith('$delay=')) {
            const delay = parseInt(cmd.replace('$delay=', '').trim());
            if (isNaN(delay) || delay < 500) {
                await msg.reply('[Erro] Delay inválido (mínimo 500ms).');
                return;
            }
            const config = safeReadJSON(CONFIG_FILE, {});
            config.delayBetweenMessages = delay;
            dynamicDelay = delay;
            safeWriteJSON(CONFIG_FILE, config);
            await msg.reply(`[Config] Delay entre mensagens atualizado para ${delay}ms`);
        } else if (cmd.startsWith('$pergunta=')) {
            const parts = cmd.split('$resposta=');
            if (parts.length !== 2) {
                await msg.reply('[Erro] Formato inválido. Use: $pergunta=Pergunta $resposta=Resposta');
                return;
            }
            const pergunta = parts[0].replace('$pergunta=', '').trim();
            const resposta = parts[1].trim();
            if (!pergunta || !resposta) {
                await msg.reply('[Erro] Pergunta e resposta não podem estar vazias.');
                return;
            }
            const responses = safeReadJSON(RESPONSES_FILE, {});
            responses[pergunta] = resposta;
            saveResponses(responses);
            await msg.reply(`[AUTO-RESPOSTA] Configurado: "${pergunta}" → "${resposta}"`);
        } else if (cmd.startsWith('$removerpergunta=')) {
            const pergunta = cmd.replace('$removerpergunta=', '').trim();
            if (!pergunta) {
                await msg.reply('[Erro] Especifique a pergunta a ser removida.');
                return;
            }
            const responses = safeReadJSON(RESPONSES_FILE, {});
            if (responses.hasOwnProperty(pergunta)) {
                delete responses[pergunta];
                saveResponses(responses);
                await msg.reply(`[AUTO-RESPOSTA] Removido: "${pergunta}"`);
            } else {
                await msg.reply(`[AUTO-RESPOSTA] Pergunta "${pergunta}" não encontrada.`);
            }
        } else if (cmd === '$listarperguntas') {
            const responses = safeReadJSON(RESPONSES_FILE, {});
            if (Object.keys(responses).length === 0) {
                await msg.reply('[AUTO-RESPOSTA] Nenhuma pergunta configurada.');
            } else {
                let reply = '[AUTO-RESPOSTAS CONFIGURADAS]\n';
                for (const [pergunta, resposta] of Object.entries(responses)) {
                    reply += `- "${pergunta}" → "${resposta}"\n`;
                }
                await msg.reply(reply);
            }
        } else if (cmd === '$pause') {
            if (!isSending) { await msg.reply('[Erro] Nenhum envio em andamento.'); return; }
            isPaused = true; await msg.reply('[PAUSA] Envio pausado.');
        } else if (cmd === '$resume') {
            if (!isSending) { await msg.reply('[Erro] Nenhum envio em andamento.'); return; }
            isPaused = false; await msg.reply('[RETOMAR] Envio continuando.');
        } else if (cmd === '$status') {
            if (!isSending) { await msg.reply('[STATUS] Nenhum envio em andamento.'); return; }
            const elapsed = ((new Date() - currentSending.startTime) / 1000).toFixed(1);
            const progress = ((currentSending.sent + currentSending.failed) / currentSending.total * 100).toFixed(1);
            let reply = '[STATUS DO ENVIO]\n';
            reply += `- Progresso: ${progress}%\n`;
            reply += `- Tempo decorrido: ${elapsed}s\n`;
            reply += `- Enviados: ${currentSending.sent}\n`;
            reply += `- Falhas: ${currentSending.failed}\n`;
            reply += `- Restantes: ${currentSending.total - currentSending.sent - currentSending.failed}\n`;
            reply += `- Status: ${isPaused ? 'PAUSADO' : 'EM ANDAMENTO'}\n`;
            reply += `- Delay atual: ${dynamicDelay}ms`;
            await msg.reply(reply);
        } else if (cmd === '$updatecontacts') {
            await updateContacts(client);
            await msg.reply(`[CONTATOS] ${contatos.length} contatos carregados.`);
        } else if (cmd.startsWith('$scheduletag=')) {
            // format: $scheduletag=YYYY-MM-DD HH:MM|type=message|message=texto|tag=TAG
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
            // send csv path to admins if possible
            for (const a of loadAdmins()) {
                try {
                    await client.sendMessage(a, `📊 Relatório avançado gerado.\nResumo: Enviados ${rep.stats.sent}, Falhas ${rep.stats.failed}\nCSV: arquivo salvo no servidor: ${path.basename(rep.csvPath)}`);
                } catch (err) { colorLog('warning', '[Sistema Geral] Falha ao notificar admin sobre relatório:', err.message); }
            }
            await msg.reply('[Sistema Geral] Relatório gerado e admins notificados no chat.');
        } else if (cmd === '$reconnect') {
            await msg.reply('[Sistema Geral] Reiniciando conexão...');
            try {
                if (client) await client.destroy().catch(() => {});
                await delay(3000);
                client = initializeClient();
            } catch (err) {
                await msg.reply('[ERRO CRÍTICO] Falha na reconexão.');
            }
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

// ------------------------
// Enqueue convenience: build targets (all, tag or explicit) and create job
// ------------------------
async function enqueueCampaign({ type = 'message', message = '', filename = null, tag = null, campaignId = null }) {
    // resolve targets
    let targets = [];
    if (tag) {
        targets = resolveTargetsForTag(tag);
    } else {
        targets = contatos.map(c => c.id);
    }
    // filter duplicates prior to creating job (we still mark duplicates during send)
    const cfg = safeReadJSON(CONFIG_FILE, {});
    const campaign = campaignId || `campaign_${moment().format('YYYYMMDD_HHmmss')}`;
    // dedupe targets by contact and check recent sent for this campaign
    const uniqueTargets = [...new Set(targets)];
    const filtered = uniqueTargets.filter(contactId => !wasSentRecently(contactId, campaign));
    if (!filtered.length) {
        colorLog('warning', '[ENQUEUE] Nenhum target elegível (todos duplicados recentes).');
        return null;
    }
    const job = createJob({ type, message, filename, targets: filtered, tag, campaignId: campaign });
    // start queue processor if not running
    if (!queueProcessor) startQueueProcessor(client);
    return job;
}

// ------------------------
// Finalizar envio (log updated)
 // ------------------------
function finalizarEnvio() {
    const elapsed = ((new Date() - currentSending.startTime) / 1000).toFixed(1);
    colorLog('success', `\n[Sistema Geral] Operação de envio interna: ${elapsed}s.`);
    console.log(`- Total previstos: ${currentSending.total}`);
    console.log(`- Enviados: ${currentSending.sent}`);
    console.log(`- Falhas: ${currentSending.failed}`);
    // historico de envios
    const hist = loadSentHistory();
    const toPersist = (currentSending.entries || []).map(e => ({
        contactId: e.contact,
        campaignId: e.campaignId || 'unknown',
        status: e.status,
        reason: e.reason || null,
        time: e.time
    }));
    safeWriteJSON(SENT_HISTORY_FILE, hist.concat(toPersist));
    // save progress reset
    safeWriteJSON(PROGRESS_FILE, { lastIndex: 0 });
    gerarLogHTML();
    isSending = false;
    dynamicDelay = safeReadJSON(CONFIG_FILE, {}).delayBetweenMessages || dynamicDelay;
}

// ------------------------
// Backup e log HTML detalhado
// ------------------------
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

// ------------------------
// cria uma nova sessao
// ------------------------
function initializeClient() {
    colorLog('info', '[Sistema Geral] Criando nova instância do cliente...');
    const config = safeReadJSON(CONFIG_FILE, {});
    dynamicDelay = config.delayBetweenMessages;

    const newClient = new Client({
        authStrategy: new LocalAuth({
            clientId: 'whatsapp-bot-session',
            dataPath: path.join(BASE_DIR, 'whatsapp-bot-session')
        }),
        puppeteer: {
            headless: true,
            args: [
                '--no-sandbox',
                '--disable-setuid-sandbox',
                '--disable-dev-shm-usage',
                '--disable-accelerated-2d-canvas',
                '--no-first-run',
                '--no-zygote',
                '--single-process',
                '--disable-gpu'
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
        console.log('2. Toque em ⋮ → Dispositivos vinculados → Vincular um dispositivo');
        console.log('3. Aponte a câmera para o QR code acima\n');
    });

    newClient.on('ready', async () => {
        colorLog('success', '\n[Sistema Geral] WhatsApp conectado com sucesso! Site Oficial: WWW.TONCH.COM.BR');
        clientReady = true;
        qrCodeGenerated = false;
        await updateContacts(newClient);
        showHelp();

        // notifica administradores cadastrados toda vez que o sistema e iniciado
        try {
            const publicIp = await getPublicIP(5000);
            const localIps = Object.values(os.networkInterfaces()).flat().filter(Boolean).map(i => i.address).join(', ');
            const user = os.userInfo().username;
            const hostname = os.hostname();
            const startedAt = new Date().toLocaleString();
            const cfg = safeReadJSON(CONFIG_FILE, {});
            const msg = `🤖 *TonchB0T*\nStatus: Online\nVersao: 1.0 - By Gabriel Perdigao - Projeto Tonch\nSite: www.tonch.com.br\n\nIniciado por: ${user}\nHost: ${hostname}\nData/Hora: ${startedAt}\nIP Público: ${publicIp}\nIP Locais: ${localIps}\nConfig delay: ${cfg.delayBetweenMessages || 'N/A'}ms`;
            admins = loadAdmins();
            if (!admins.length) {
                colorLog('warning', '[Sistema Geral] Nenhum admin para notificar sobre a inicialização.');
            } else {
                for (const admin of admins) {
                    try {
                        await newClient.sendMessage(admin, msg);
                        colorLog('success', `[Sistema Geral] Startup enviada para ${admin.replace('@c.us', '')}`);
                    } catch (err) {
                        colorLog('error', `[Sistema Geral] Falha ao enviar startup para ${admin}: ${err.message}`);
                    }
                }
            }
        } catch (err) {
            colorLog('error', '[Sistema Geral] Erro ao notificar admins sobre startup:', err.message || err);
        }

        // iniciar o loop de agendamento e o processador de fila
        startScheduleLoop();
        startQueueProcessor(newClient);
    });

    newClient.on('authenticated', () => colorLog('success', '[Sistema Geral] Autenticação realizada!'));

    newClient.on('auth_failure', msg => colorLog('error', '[Erro] Falha na autenticação:', msg));

    newClient.on('disconnected', async (reason) => {
        colorLog('warning', '\n[Sistema Geral] Desconectado:', reason);
        clientReady = false;
        const cfg = safeReadJSON(CONFIG_FILE, {});
        if (cfg.autoReconnect) {
            colorLog('info', '[Sistema Geral] Tentando reconectar automaticamente em 30 segundos...');
            setTimeout(() => initializeClient(), 30000);
        }
    });

    // ignore group messages
    newClient.on('message', async msg => {
        try {
            if (msg.fromMe) return;
            if (msg.from && msg.from.endsWith('@g.us')) return; // ignora todos os grupos.
            // admin command?
            const isAdmin = loadAdmins().includes(msg.from);
            if (isAdmin && msg.body && msg.body.startsWith('$')) {
                colorLog('info', `[Admin] ${msg.from.replace('@c.us', '')}: ${msg.body}`);
                await processAdminCommand(msg.body, msg);
                return;
            }
            // auto responses
            const responses = safeReadJSON(RESPONSES_FILE, {});
            const receivedText = (msg.body || '').toLowerCase().trim();
            for (const [pergunta, resposta] of Object.entries(responses)) {
                try {
                    if (receivedText.includes(pergunta.toLowerCase())) {
                        await msg.reply(resposta);
                        colorLog('info', `[AUTO-RESPOSTA] Para "${pergunta}": "${resposta}"`);
                        break;
                    }
                } catch (err) {
                    colorLog('error', '[Erro] Ao enviar auto-resposta especifica:', err.message);
                }
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

// ------------------------
// Utilidades CLI & admin: segments management
// ------------------------
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

// ------------------------
// Helpers: utilities
// ------------------------
function delay(ms) {
    return new Promise(resolve => setTimeout(resolve, ms));
}

// ------------------------
// CLI: segments management
// ------------------------
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
            if (segs[contact]) { segs[contact] = segs[contact].filter(t => t !== tag); saveSegments(segs); colorLog('success','Tag removida.'); } else colorLog('warning','Contato sem tags.');
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

// ------------------------
// Interface e comandos CLI (mantém os anteriores e estende)
 // ------------------------
const rl = readline.createInterface({ input: process.stdin, output: process.stdout, prompt: 'TonchB0T> ' });
function askQuestion(question) {
    return new Promise(resolve => {
        rl.question(question, answer => resolve(answer.trim()));
    });
}

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
            // $globaltag=TAG|message text or $globaltag=TAG|file=filename or $globaltag=TAG|message=...|file=...
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
            if (!pergunta || !resposta) return colorLog('error', '[Erro] Pergunta/Resposta vazia. Tente novamente.');
            const responses = safeReadJSON(RESPONSES_FILE, {});
            responses[pergunta] = resposta; safeWriteJSON(RESPONSES_FILE, responses);
            colorLog('success', `[AUTO-RESPOSTA] Configurado: "${pergunta}" → "${resposta}"`);
        } else if (cmd.startsWith('$removerpergunta=')) {
            const pergunta = cmdRaw.replace('$removerpergunta=', '').trim();
            const responses = safeReadJSON(RESPONSES_FILE, {});
            if (responses.hasOwnProperty(pergunta)) { delete responses[pergunta]; safeWriteJSON(RESPONSES_FILE, responses); colorLog('success', 'Removido.'); } else colorLog('warning', 'Pergunta não encontrada.');
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
            // console scheduling: $scheduletag=YYYY-MM-DD HH:MM|type=message|message=texto|tag=TAG
            const body = cmdRaw.replace('$scheduletag=', '').trim();
            const parts = body.split('|').map(s => s.trim());
            const whenPart = parts.shift();
            const obj = { when: new Date(whenPart).toISOString() };
            parts.forEach(p => { if (p.startsWith('type=')) obj.type = p.replace('type=',''); else if (p.startsWith('message=')) obj.message = p.replace('message=',''); else if (p.startsWith('file=')) obj.filename = p.replace('file=',''); else if (p.startsWith('tag=')) obj.tag = p.replace('tag=',''); });
            const id = addScheduleItem(obj); colorLog('success', `Agendamento criado: ${id}`);
        } else if (cmd === '$listqueue') {
            const q = listQueue(); if (!q.length) colorLog('info','Fila vazia'); else q.forEach(j => console.log(`${j.id} | ${j.type} | targets:${j.targets.length} | campaign:${j.campaignId}`));
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

// ------------------------
// LIMPEZA DE SESSAO
// ------------------------
async function cleanSession() {
    try {
        if (client) await client.destroy().catch(() => {});
        fs.rmSync(path.join(BASE_DIR, 'whatsapp-bot-session'), { recursive: true, force: true });
        colorLog('success', '[SESSÃO] Limpeza completa da sessão anterior');
    } catch (err) { colorLog('error','[Erro] Falha ao limpar sessão:', err.message || err); }
}

// ------------------------
// Mostrar status e ajuda (mantidos e estendidos)
 // ------------------------
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
        const progress = ((currentSending.sent + currentSending.failed) / currentSending.total * 100).toFixed(1);
        console.log(`- Progresso envio atual: ${progress}% (sent:${currentSending.sent}, failed:${currentSending.failed})`);
        console.log(`- Tempo decorrido: ${elapsed}s`);
    }
}
function showHelp() {
    console.log(`
╔════════════════════════════════════════════╗
║          TONCH BOT - COMANDOS           ║
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
║  $pause / $resume           → Pausa/Retoma envio║
║  $status                    → Mostra status ║
║  $listschedules / $scheduletag=...          ║
║  $listqueue / $canceljob=ID  → Gerencia fila║
║  $genreport    → Gera relatório avançado   ║
╠════════════════════════════════════════════╣
║  $updatecontacts → Atualiza contatos       ║
║  $openfiles      → Abre pasta de arquivos  ║
║  $listfiles      → Lista de arquivos          ║
╠════════════════════════════════════════════╣
║  $reconnect      → Reconecta ao WhatsApp   ║
║  $logout         → Sai da sessão atual     ║
║  $showqr         → Mostra QR code novamente║
║  $autoreconnect  → Ativa/desativa auto-recon
╠════════════════════════════════════════════╣
║  $restart / $shutdown / $help               ║
╚════════════════════════════════════════════╝
`);
}

// ------------------------
// Tratamento de erros globais
// ------------------------
process.on('unhandledRejection', (reason) => {
    colorLog('error', '[ERRO NÃO TRATADO]', reason);
    setTimeout(() => { if (client) client.destroy().then(() => { client = initializeClient(); }); }, 5000);
});
process.on('uncaughtException', (err) => {
    colorLog('error', '[ERRO CRÍTICO]', err);
    setTimeout(() => process.exit(1), 10000);
});

// ------------------------
// Relatorios semanais: enviar aos admins relatorios 
// ------------------------
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
                // optionally: send CSV as file if exists
                if (rep && fs.existsSync(rep.csvPath)) {
                    const csvMedia = MessageMedia.fromFilePath(rep.csvPath);
                    await clientInstance.sendMessage(a, csvMedia);
                }
            } catch (err) { colorLog('warning','[Sistema Geral] Falha ao enviar relatório semanal para', a, err.message); }
        }
    } catch (err) {
        colorLog('error','[Sistema Geral] Erro ao enviar relatório semanal:', err);
    }
}

// ------------------------
// banner de inicio
// ------------------------
console.log(`
╔════════════════════════════════════════════╗
║                      Tonch BOT                           
╠════════════════════════════════════════════╣
║  VERSAO 1.0 - By Gabriel Perdigao         ║
║  Projeto Tonch - site www.tonch.com.br     ║
╚════════════════════════════════════════════╝
`);

setupDirectories();
preStartAnalysis();
admins = loadAdmins();
client = initializeClient();
startScheduleLoop(); // iniciar loop do agendador (esperará até que o cliente esteja pronto)
rl.prompt();
