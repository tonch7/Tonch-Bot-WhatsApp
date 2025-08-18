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

// Configurações
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

// Cores para console
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

// Helper functions
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

function delay(ms) {
    return new Promise(resolve => setTimeout(resolve, ms));
}

// Setup inicial
function setupDirectories() {
    [LOG_DIR, FILES_DIR, BACKUP_DIR].forEach(dir => {
        if (!fs.existsSync(dir)) {
            fs.mkdirSync(dir, { recursive: true });
            colorLog('info', `[SISTEMA] Pasta criada: ${path.basename(dir)}`);
        }
    });

    if (!fs.existsSync(CONFIG_FILE)) {
        safeWriteJSON(CONFIG_FILE, {
            delayBetweenMessages: 10000,
            maxRetries: 3,
            autoReconnect: true,
            maxDelay: 30000,
            safeBatchSize: 20,
            safeBatchPauseMs: 120000,
            maxMessagesPerMinute: 10,
            weeklyReportHourUTC: 12,
            concurrency: 1,
            duplicateWindowDays: 30,
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

// Estado global
let contatos = [];
let isSending = false;
let isPaused = false;
let dynamicDelay = 10000;
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

// Funções de histórico
function loadSentHistory() {
    return safeReadJSON(SENT_HISTORY_FILE, []);
}

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

// Sistema de fila
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

// Agendamento
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
                    removeScheduleItem(s.id);
                }
            }
        }
    }, 30000);
}

// Segmentos
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

// Atualizar contatos
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

// Criar mídia para mensagem
async function criarMessageMedia(filepath, nomeArquivo) {
    try {
        const stats = fs.statSync(filepath);
        const maxSizeBytes = 10 * 1024 * 1024;
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

// Relatórios
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
        const html = `<!doctype html>
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

// Envio para contato único
async function sendToContactSingle(clientInstance, contatoId, job) {
    try {
        if (isPaused) {
            colorLog('warning', `[PAUSED] Envio pausado para ${contatoId}`);
            return { status: 'paused' };
        }

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

// Processador de fila com suporte a pausa
async function startQueueProcessor(clientInstance) {
    if (queueProcessor) return;
    queueProcessor = true;
    colorLog('info', '[QUEUE] Iniciando processador de fila...');
    
    (async function loop() {
        while (true) {
            try {
                if (!clientInstance || !clientReady) {
                    await delay(2000);
                    continue;
                }
                
                if (isPaused) {
                    await delay(5000);
                    continue;
                }

                let queue = loadQueue();
                if (!queue.length) {
                    await delay(1000);
                    continue;
                }

                const cfg = safeReadJSON(CONFIG_FILE, {});
                const concurrency = 1;
                const maxPerMinute = cfg.maxMessagesPerMinute || 10;
                const safeBatchSize = cfg.safeBatchSize || 20;
                const safeBatchPauseMs = cfg.safeBatchPauseMs || 120000;

                const job = queue[0];
                if (!job) { await delay(1000); continue; }

                const targets = Array.isArray(job.targets) ? job.targets.slice() : [];
                if (!targets.length) {
                    removeJob(job.id);
                    continue;
                }

                const chunkSize = 1;
                const chunk = targets.splice(0, chunkSize);

                const sendPromises = chunk.map(async (contactId) => {
                    if (wasSentRecently(contactId, job.campaignId || 'default')) {
                        colorLog('warning', `[DUP] Pular ${contactId} — já recebeu campanha ${job.campaignId}`);
                        currentSending.entries.push({ contact: contactId, status: 'skipped_duplicate', time: new Date().toISOString(), campaignId: job.campaignId });
                        recordSent(contactId, job.campaignId, 'skipped_duplicate', 'duplicate_recent');
                        return;
                    }
                    
                    const maxRetries = (cfg.maxRetries || 3);
                    for (let attempt = 0; attempt <= maxRetries; attempt++) {
                        const res = await sendToContactSingle(clientInstance, contactId, job);
                        
                        if (res.status === 'paused') {
                            colorLog('warning', '[PAUSE] Envio pausado durante o processamento');
                            return;
                        }
                        
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

                await Promise.all(sendPromises);

                const remainingTargets = targets;
                let q = loadQueue();
                const idx = q.findIndex(j => j.id === job.id);
                if (idx >= 0) {
                    if (remainingTargets.length === 0) {
                        q.splice(idx, 1);
                    } else {
                        q[idx].targets = remainingTargets;
                    }
                    saveQueue(q);
                }

                await delay((cfg.delayBetweenMessages || dynamicDelay || 10000) + Math.floor(Math.random() * 2000));

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

// Comandos administrativos
async function processAdminCommand(cmd, msg) {
    try {
        if (cmd === '$help') {
            await msg.reply(`*COMANDOS ADMIN:*\n$global=mensagem - Envia msg para todos\n$file=arquivo - Envia arquivo\n$delay=XXXX - Altera delay\n$pergunta=Pergunta $resposta=Resposta\n$removerpergunta=Pergunta\n$listarperguntas\n$pause - Pausa envios\n$resume - Retoma envios\n$status - Mostra status\n$updatecontacts - Atualiza contatos\n$reconnect - Reconecta\n$restart - Reinicia bot\nVer mais com $help no console`);
        } 
        else if (cmd === '$pause') {
            isPaused = true;
            await msg.reply('[PAUSA] Envio pausado. Use $resume para continuar.');
            colorLog('warning', '[PAUSE] Envio pausado por comando administrativo');
        } 
        else if (cmd === '$resume') {
            isPaused = false;
            await msg.reply('[RETOMAR] Envio continuando.');
            colorLog('success', '[RESUME] Envio retomado por comando administrativo');
        }
        // ... (outros comandos permanecem iguais)
    } catch (err) {
        await msg.reply(`[Erro] Ocorreu um erro: ${err.message}`);
        colorLog('error', '[Erro] Ao processar comando administrativo:', err);
    }
}

// Inicialização do cliente WhatsApp
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
                '--disable-gpu',
                '--use-gl=egl'
            ],
            executablePath: process.env.CHROME_PATH || undefined,
            timeout: 0
        },
        restartOnAuthFail: true,
        takeoverOnConflict: true,
        qrTimeout: 0,
        qrMaxRetries: 3,
        ffmpegPath: '/usr/bin/ffmpeg'
    });

    newClient.on('qr', qr => {
        qrCodeGenerated = true;
        currentQrCode = qr;
        try {
            qrcode.generate(qr, { small: true });
            colorLog('info', '\n[Sistema Geral] Escaneie este código com seu WhatsApp:');
            console.log('1. Abra o WhatsApp no seu celular');
            console.log('2. Toque em ⋮ → Dispositivos vinculados → Vincular um dispositivo');
            console.log('3. Aponte a câmera para o QR code acima\n');
        } catch (err) {
            colorLog('error', '[Erro] Falha ao gerar QR code:', err);
            console.log(`QR Code: ${qr}`);
        }
    });

    newClient.on('loading_screen', (percent, message) => {
        colorLog('info', `[Carregando] ${percent}%: ${message}`);
    });

    newClient.on('authenticated', (session) => {
        colorLog('success', '[Autenticado] Sessão validada com sucesso!');
    });

    newClient.on('auth_failure', msg => {
        colorLog('error', '[Falha na Autenticação]', msg);
        cleanSession().catch(() => {});
    });

    newClient.on('ready', async () => {
        colorLog('success', '\n[Sistema Geral] WhatsApp conectado com sucesso! Site Oficial: WWW.TONCH.COM.BR');
        clientReady = true;
        qrCodeGenerated = false;
        await updateContacts(newClient);
        showHelp();

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

        startScheduleLoop();
        startQueueProcessor(newClient);
    });

    newClient.on('disconnected', async (reason) => {
        colorLog('warning', '\n[Sistema Geral] Desconectado:', reason);
        clientReady = false;
        const cfg = safeReadJSON(CONFIG_FILE, {});
        if (cfg.autoReconnect) {
            colorLog('info', '[Sistema Geral] Tentando reconectar automaticamente em 30 segundos...');
            setTimeout(() => initializeClient(), 30000);
        }
    });

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

    const initClient = async () => {
        try {
            await newClient.initialize();
        } catch (err) {
            colorLog('error', '[Erro] Falha na inicialização:', err.message || err);
            
            if (err.message.includes('Protocol error') || err.message.includes('Target closed')) {
                colorLog('info', '[Sistema Geral] Tentando limpar sessão e reconectar...');
                await cleanSession();
            }
            
            colorLog('info', '[Sistema Geral] Tentando novamente em 15 segundos...');
            setTimeout(() => initializeClient(), 15000);
        }
    };

    initClient();

    return newClient;
}

// Limpeza de sessão
async function cleanSession() {
    try {
        if (client) {
            try {
                await client.destroy();
            } catch (e) {
                colorLog('warning', '[Aviso] Erro ao destruir cliente:', e.message);
            }
        }
        
        const sessionDir = path.join(BASE_DIR, 'whatsapp-bot-session');
        if (fs.existsSync(sessionDir)) {
            fs.rmSync(sessionDir, { recursive: true, force: true });
            colorLog('info', '[Sessão] Diretório de sessão limpo');
        }
        
        const cacheDir = path.join(os.tmpdir(), 'puppeteer_dev_profile-*');
        exec(`rm -rf ${cacheDir}`, (error) => {
            if (!error) colorLog('info', '[Sessão] Cache do navegador limpo');
        });
    } catch (err) {
        colorLog('error', '[Erro] Falha ao limpar sessão:', err.message || err);
    }
}

// Interface CLI
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
        if (cmd === '$pause') {
            isPaused = true; 
            colorLog('warning', 'Envio pausado via CLI.');
        } 
        else if (cmd === '$resume') {
            isPaused = false; 
            colorLog('success', 'Envio retomado via CLI.');
        }
        // ... (outros comandos CLI permanecem iguais)
    } catch (err) {
        colorLog('error', '[Erro] Ocorreu um erro:', err.message || err);
    }
    rl.prompt();
}).on('close', () => { 
    colorLog('info','[SISTEMA] Encerrando bot...'); 
    process.exit(0); 
});

// Inicialização
console.log(`
╔════════════════════════════════════════════╗
║                      Tonch BOT                           
╠════════════════════════════════════════════╣
║  VERSAO 1.0 - By Gabriel Perdigao         ║
║  Projeto Tonch - site www.tonch.com.br     ║
╚════════════════════════════════════════════╝
`);

setupDirectories();
admins = loadAdmins();
client = initializeClient();
startScheduleLoop();
rl.prompt();
