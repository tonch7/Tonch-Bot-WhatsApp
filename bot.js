const { Client, LocalAuth, MessageMedia } = require('whatsapp-web.js');
const qrcode = require('qrcode-terminal');
const fs = require('fs');
const path = require('path');
const readline = require('readline');
const moment = require('moment');
const { exec } = require('child_process');
const mime = require('mime-types');
const open = require('open');

// Configurações - diretórios externos ao executável
const BASE_DIR = process.cwd();
const LOG_DIR = path.join(BASE_DIR, 'whatsapp-bot-logs');
const FILES_DIR = path.join(BASE_DIR, 'whatsapp-bot-files');
const CONFIG_FILE = path.join(BASE_DIR, 'whatsapp-bot-config.json');
const PROGRESS_FILE = path.join(BASE_DIR, 'whatsapp-bot-progress.json');
const BACKUP_DIR = path.join(BASE_DIR, 'whatsapp-bot-backups');
const RESPONSES_FILE = path.join(BASE_DIR, 'whatsapp-bot-responses.json');

// Cores para o console
const colors = {
    error: '\x1b[31m', // Vermelho
    success: '\x1b[32m', // Verde
    info: '\x1b[36m', // Ciano
    warning: '\x1b[33m', // Amarelo
    reset: '\x1b[0m' // Reset
};

function colorLog(type, message) {
    console.log(`${colors[type]}${message}${colors.reset}`);
}

// Verificar e criar diretórios necessários
function setupDirectories() {
    [LOG_DIR, FILES_DIR, BACKUP_DIR].forEach(dir => {
        if (!fs.existsSync(dir)) {
            fs.mkdirSync(dir);
            colorLog('info', `[SISTEMA] Pasta criada: ${path.basename(dir)}`);
        }
    });

    if (!fs.existsSync(CONFIG_FILE)) {
        fs.writeFileSync(CONFIG_FILE, JSON.stringify({ 
            delayBetweenMessages: 3500, 
            maxRetries: 3,
            autoReconnect: true,
            maxDelay: 30000
        }, null, 2));
    }

    if (!fs.existsSync(PROGRESS_FILE)) {
        fs.writeFileSync(PROGRESS_FILE, JSON.stringify({ lastIndex: 0 }, null, 2));
    }

    if (!fs.existsSync(RESPONSES_FILE)) {
        fs.writeFileSync(RESPONSES_FILE, JSON.stringify({}, null, 2));
    }
}

// Estado do sistema
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
    startTime: null
};

let clientReady = false;
let qrCodeGenerated = false;
let currentQrCode = null;
let client = null;

// Carregar respostas automáticas
function loadResponses() {
    try {
        return JSON.parse(fs.readFileSync(RESPONSES_FILE));
    } catch (err) {
        colorLog('error', '[ERRO] Falha ao carregar respostas:', err);
        return {};
    }
}

// Salvar respostas automáticas
function saveResponses(responses) {
    try {
        fs.writeFileSync(RESPONSES_FILE, JSON.stringify(responses, null, 2));
        return true;
    } catch (err) {
        colorLog('error', '[ERRO] Falha ao salvar respostas:', err);
        return false;
    }
}

// Inicializa o cliente WhatsApp
function initializeClient() {
    colorLog('info', '[INICIALIZAÇÃO] Criando nova instância do cliente...');
    
    const config = JSON.parse(fs.readFileSync(CONFIG_FILE));
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
                '--no-zygote'
            ],
            timeout: 60000
        },
        restartOnAuthFail: true,
        takeoverOnConflict: true,
        qrTimeout: 60000
    });

    // Eventos do WhatsApp
    newClient.on('qr', qr => {
        qrCodeGenerated = true;
        currentQrCode = qr;
        qrcode.generate(qr, { small: true });
        colorLog('info', '\n[QR CODE] Escaneie este código com seu WhatsApp:');
        console.log('1. Abra o WhatsApp no seu celular');
        console.log('2. Toque em ⋮ → Dispositivos vinculados → Vincular um dispositivo');
        console.log('3. Aponte a câmera para o QR code acima\n');
    });

    newClient.on('ready', async () => {
        colorLog('success', '\n[CONEXÃO] WhatsApp conectado com sucesso! Site Oficial: WWW.TONCH.COM.BR');
        clientReady = true;
        qrCodeGenerated = false;
        await updateContacts(newClient);
        showHelp();
    });

    newClient.on('authenticated', () => {
        colorLog('success', '[SESSÃO] Autenticação realizada!');
    });

    newClient.on('auth_failure', msg => {
        colorLog('error', '[ERRO] Falha na autenticação:', msg);
    });

    newClient.on('disconnected', async (reason) => {
        colorLog('warning', '\n[CONEXÃO] Desconectado:', reason);
        clientReady = false;
        
        const config = JSON.parse(fs.readFileSync(CONFIG_FILE));
        if (config.autoReconnect) {
            colorLog('info', '[RECONEXÃO] Tentando reconectar automaticamente em 5 segundos...');
            setTimeout(() => initializeClient(), 5000);
        }
    });

    newClient.on('message', async msg => {
        if (!msg.fromMe) {
            const responses = loadResponses();
            const receivedText = msg.body.toLowerCase().trim();
            
            for (const [pergunta, resposta] of Object.entries(responses)) {
                if (receivedText.includes(pergunta.toLowerCase())) {
                    await msg.reply(resposta);
                    colorLog('info', `[AUTO-RESPOSTA] Para "${pergunta}": "${resposta}"`);
                    break;
                }
            }
        }
    });

    newClient.initialize().catch(err => {
        colorLog('error', '[ERRO] Falha ao inicializar:', err);
        colorLog('info', '[TENTATIVA] Tentando novamente em 10 segundos...');
        setTimeout(() => initializeClient(), 10000);
    });

    return newClient;
}

// Função para limpar sessão
async function cleanSession() {
    try {
        if (client) {
            await client.destroy().catch(err => {
                colorLog('warning', '[AVISO] Erro ao destruir cliente:', err.message);
            });
        }
        fs.rmSync(path.join(BASE_DIR, 'whatsapp-bot-session'), { 
            recursive: true, 
            force: true 
        });
        colorLog('success', '[SESSÃO] Limpeza completa da sessão anterior');
    } catch (err) {
        colorLog('error', '[ERRO] Falha ao limpar sessão:', err);
    }
}

// Interface de linha de comando
const rl = readline.createInterface({ 
    input: process.stdin, 
    output: process.stdout,
    prompt: 'BOT> '
});

rl.on('line', async input => {
    const cmd = input.trim().toLowerCase();

    try {
        if (cmd.startsWith('$global=')) {
            if (!clientReady) return colorLog('error', '[ERRO] Aguarde a conexão com WhatsApp.');
            
            const data = cmd.replace('$global=', '').trim();
            if (!data) return colorLog('error', '[ERRO] Mensagem vazia.');

            if (data.includes(' + ')) {
                const [mensagem, arquivo] = data.split(' + ').map(v => v.trim());
                const filepath = path.join(FILES_DIR, arquivo);
                if (!fs.existsSync(filepath)) return colorLog('error', `[ERRO] Arquivo '${arquivo}' não encontrado.`);
                await enviarMensagemArquivoParaTodos(mensagem, filepath, arquivo);
            } else {
                await enviarMensagemParaTodos(data);
            }

        } else if (cmd.startsWith('$file=')) {
            if (!clientReady) return colorLog('error', '[ERRO] Aguarde a conexão com WhatsApp.');
            
            const filename = cmd.replace('$file=', '').trim();
            const filepath = path.join(FILES_DIR, filename);
            if (!fs.existsSync(filepath)) return colorLog('error', `[ERRO] Arquivo '${filename}' não encontrado.`);
            await enviarArquivoParaTodos(filepath, filename);

        } else if (cmd.startsWith('$delay=')) {
            const delay = parseInt(cmd.replace('$delay=', '').trim());
            if (isNaN(delay) || delay < 500) return colorLog('error', '[ERRO] Delay inválido (mínimo 500ms).');
            const config = JSON.parse(fs.readFileSync(CONFIG_FILE));
            config.delayBetweenMessages = delay;
            dynamicDelay = delay;
            fs.writeFileSync(CONFIG_FILE, JSON.stringify(config, null, 2));
            colorLog('success', `[CONFIG] Delay entre mensagens atualizado para ${delay}ms`);

        } else if (cmd.startsWith('$pergunta=')) {
            const parts = cmd.split('$resposta=');
            if (parts.length !== 2) return colorLog('error', '[ERRO] Formato inválido. Use: $pergunta=Pergunta $resposta=Resposta');
            
            const pergunta = parts[0].replace('$pergunta=', '').trim();
            const resposta = parts[1].trim();
            
            if (!pergunta || !resposta) return colorLog('error', '[ERRO] Pergunta e resposta não podem estar vazias.');
            
            const responses = loadResponses();
            responses[pergunta] = resposta;
            
            if (saveResponses(responses)) {
                colorLog('success', `[AUTO-RESPOSTA] Configurado: "${pergunta}" → "${resposta}"`);
            }

        } else if (cmd.startsWith('$removerpergunta=')) {
            const pergunta = cmd.replace('$removerpergunta=', '').trim();
            if (!pergunta) return colorLog('error', '[ERRO] Especifique a pergunta a ser removida.');
            
            const responses = loadResponses();
            if (responses.hasOwnProperty(pergunta)) {
                delete responses[pergunta];
                if (saveResponses(responses)) {
                    colorLog('success', `[AUTO-RESPOSTA] Removido: "${pergunta}"`);
                }
            } else {
                colorLog('warning', `[AUTO-RESPOSTA] Pergunta "${pergunta}" não encontrada.`);
            }

        } else if (cmd === '$listarperguntas') {
            const responses = loadResponses();
            if (Object.keys(responses).length === 0) {
                colorLog('info', '[AUTO-RESPOSTA] Nenhuma pergunta configurada.');
            } else {
                colorLog('info', '[AUTO-RESPOSTAS CONFIGURADAS]');
                for (const [pergunta, resposta] of Object.entries(responses)) {
                    console.log(`- "${pergunta}" → "${resposta}"`);
                }
            }

        } else if (cmd === '$pause') {
            if (!isSending) return colorLog('error', '[ERRO] Nenhum envio em andamento.');
            isPaused = true;
            colorLog('warning', '[PAUSA] Envio pausado.');

        } else if (cmd === '$resume') {
            if (!isSending) return colorLog('error', '[ERRO] Nenhum envio em andamento.');
            isPaused = false;
            colorLog('success', '[RETOMAR] Envio continuando.');

        } else if (cmd === '$status') {
            showStatus();

        } else if (cmd === '$updatecontacts') {
            if (!clientReady) return colorLog('error', '[ERRO] Aguarde a conexão com WhatsApp.');
            await updateContacts(client);

        } else if (cmd === '$standby') {
            isPaused = true;
            colorLog('warning', '[STANDBY] Bot em modo de espera.');

        } else if (cmd === '$restart') {
            colorLog('info', '[REINICIAR] Reiniciando bot...');
            gerarLogHTML();
            exec(`node "${__filename}"`);
            process.exit(0);

        } else if (cmd === '$shutdown' || cmd === '$exit') {
            colorLog('info', '[SAIR] Encerrando bot...');
            gerarLogHTML();
            if (client) await client.destroy();
            process.exit(0);

        } else if (cmd === '$help') {
            showHelp();

        } else if (cmd === '$openfiles') {
            open(FILES_DIR)
                .then(() => colorLog('success', `[ARQUIVOS] Pasta aberta: ${FILES_DIR}`))
                .catch(err => colorLog('error', '[ERRO] Falha ao abrir pasta:', err));

        } else if (cmd === '$listfiles') {
            const files = fs.readdirSync(FILES_DIR);
            if (files.length === 0) {
                colorLog('info', '[ARQUIVOS] Nenhum arquivo encontrado.');
            } else {
                colorLog('info', '[ARQUIVOS DISPONÍVEIS]');
                files.forEach(file => console.log(`- ${file}`));
            }

        } else if (cmd === '$reconnect') {
            colorLog('info', '[RECONECTAR] Reiniciando conexão...');
            try {
                if (client) {
                    await client.destroy().catch(err => {
                        colorLog('warning', '[AVISO] Erro ao destruir cliente:', err.message);
                    });
                }
                await delay(3000);
                client = initializeClient();
                colorLog('success', '[RECONECTAR] Reconexão iniciada. Aguarde o novo QR Code se necessário.');
            } catch (err) {
                colorLog('error', '[ERRO CRÍTICO] Falha na reconexão:', err);
                colorLog('info', '[SOLUÇÃO] Tente reiniciar completamente o bot com $restart');
            }

        } else if (cmd === '$logout') {
            colorLog('info', '[SAIR] Desconectando da sessão atual...');
            await cleanSession();
            client = initializeClient();

        } else if (cmd === '$showqr') {
            if (qrCodeGenerated && currentQrCode) {
                qrcode.generate(currentQrCode, { small: true });
                colorLog('success', '[QR CODE] Código exibido novamente.');
            } else {
                colorLog('warning', '[QR CODE] Nenhum código disponível no momento.');
            }

        } else if (cmd === '$autoreconnect') {
            const config = JSON.parse(fs.readFileSync(CONFIG_FILE));
            config.autoReconnect = !config.autoReconnect;
            fs.writeFileSync(CONFIG_FILE, JSON.stringify(config, null, 2));
            colorLog('success', `[CONFIG] Auto-reconexão ${config.autoReconnect ? 'ativada' : 'desativada'}`);

        } else if (cmd === 'clear' || cmd === 'cls') {
            console.clear();

        } else if (cmd) {
            colorLog('error', '[ERRO] Comando inválido. Digite $help para ajuda.');
        }
    } catch (err) {
        colorLog('error', '[ERRO] Ocorreu um erro:', err);
    }

    rl.prompt();
}).on('close', () => {
    colorLog('info', '\n[SISTEMA] Encerrando bot...');
    process.exit(0);
});

// Funções principais
async function updateContacts(clientInstance = client) {
    try {
        const chats = await clientInstance.getChats();
        contatos = chats.filter(c => !c.isGroup && !c.archived)
            .map(c => ({ id: c.id._serialized, name: c.name || c.id.user }));
        colorLog('success', `[CONTATOS] ${contatos.length} contatos carregados.`);
    } catch (error) {
        colorLog('error', '[ERRO] Falha ao buscar contatos:', error);
    }
}

async function enviarMensagemParaTodos(mensagem) {
    await iniciarEnvio('message', mensagem, async (contato) => {
        await client.sendMessage(contato.id, mensagem);
    });
}

async function enviarArquivoParaTodos(filepath, nomeArquivo) {
    const media = await criarMessageMedia(filepath, nomeArquivo);
    await iniciarEnvio('file', nomeArquivo, async (contato) => {
        await client.sendMessage(contato.id, media);
    });
}

async function enviarMensagemArquivoParaTodos(mensagem, filepath, nomeArquivo) {
    const media = await criarMessageMedia(filepath, nomeArquivo);
    await iniciarEnvio('message+file', `${mensagem} + ${nomeArquivo}`, async (contato) => {
        await client.sendMessage(contato.id, `*${mensagem}*`);
        await delay(2000);
        await client.sendMessage(contato.id, media);
    });
}

async function criarMessageMedia(filepath, nomeArquivo) {
    try {
        const data = fs.readFileSync(filepath, { encoding: 'base64' });
        const mimeType = mime.lookup(nomeArquivo) || 'application/octet-stream';
        return new MessageMedia(mimeType, data, nomeArquivo);
    } catch (err) {
        colorLog('error', `[ERRO] Falha ao ler arquivo ${nomeArquivo}:`, err);
        throw err;
    }
}

async function iniciarEnvio(tipo, conteudo, sendFunction) {
    const config = JSON.parse(fs.readFileSync(CONFIG_FILE));
    let progress = JSON.parse(fs.readFileSync(PROGRESS_FILE));

    isSending = true;
    isPaused = false;
    currentSending = { 
        type: tipo, 
        content: conteudo, 
        total: contatos.length, 
        sent: 0, 
        failed: 0, 
        startTime: new Date() 
    };

    colorLog('info', `\n[ENVIO] Iniciando: ${tipo} para ${contatos.length} contatos`);
    colorLog('info', `[CONFIG] Delay entre mensagens: ${dynamicDelay}ms (ajuste automático)`);

    for (let i = progress.lastIndex; i < contatos.length; i++) {
        if (isPaused) {
            i--;
            await delay(1000);
            continue;
        }

        try {
            await sendFunction(contatos[i]);
            currentSending.sent++;
            dynamicDelay = Math.max(config.delayBetweenMessages, dynamicDelay * 0.9);
            colorLog('success', `[✔] (${currentSending.sent}/${contatos.length}) ${contatos[i].name}`);
        } catch (err) {
            currentSending.failed++;
            dynamicDelay = Math.min(config.maxDelay, dynamicDelay * 1.5);
            colorLog('error', `[✖] Falha em ${contatos[i].name} → ${err.message} (Novo delay: ${dynamicDelay}ms)`);
        }

        progress.lastIndex = i + 1;
        fs.writeFileSync(PROGRESS_FILE, JSON.stringify(progress));
        await backupProgress();
        await delay(dynamicDelay);
    }

    finalizarEnvio();
}

function finalizarEnvio() {
    const elapsed = ((new Date() - currentSending.startTime) / 1000).toFixed(1);
    colorLog('success', `\n[FINALIZADO] Envio concluído em ${elapsed} segundos.`);
    console.log(`- Total: ${currentSending.total}`);
    console.log(`- Enviados: ${currentSending.sent}`);
    console.log(`- Falhas: ${currentSending.failed}`);
    
    fs.writeFileSync(PROGRESS_FILE, JSON.stringify({ lastIndex: 0 }));
    gerarLogHTML();
    isSending = false;
    dynamicDelay = JSON.parse(fs.readFileSync(CONFIG_FILE)).delayBetweenMessages;
}

async function backupProgress() {
    try {
        const timestamp = moment().format('YYYY-MM-DD_HH-mm-ss');
        const backupFile = path.join(BACKUP_DIR, `backup_${timestamp}.json`);
        const backupData = {
            config: JSON.parse(fs.readFileSync(CONFIG_FILE)),
            contacts: contatos,
            progress: JSON.parse(fs.readFileSync(PROGRESS_FILE)),
            sendingStatus: currentSending,
            responses: loadResponses()
        };
        
        fs.writeFileSync(backupFile, JSON.stringify(backupData, null, 2));
    } catch (err) {
        colorLog('error', '[ERRO] Falha ao criar backup:', err);
    }
}

function gerarLogHTML() {
    const timestamp = moment().format('YYYY-MM-DD_HH-mm-ss');
    const htmlPath = path.join(LOG_DIR, `log_${timestamp}.html`);
    
    const html = `
<!DOCTYPE html>
<html>
<head>
    <title>Log de Envios - ${timestamp}</title>
    <style>
        body { font-family: Arial, sans-serif; margin: 20px; }
        h1 { color: #075e54; }
        .info { background: #f5f5f5; padding: 15px; border-radius: 5px; }
        .stats { margin-top: 20px; }
        .stat { display: inline-block; margin-right: 20px; }
        .success { color: #25D366; }
        .error { color: #FF0000; }
    </style>
</head>
<body>
    <h1>Relatório de Envios - WWW.TONCH.COM.BR</h1>
    <div class="info">
        <p><strong>Tipo:</strong> ${currentSending.type}</p>
        <p><strong>Conteúdo:</strong> ${currentSending.content}</p>
    </div>
    
    <div class="stats">
        <div class="stat"><strong>Total:</strong> ${currentSending.total}</div>
        <div class="stat success"><strong>Enviados:</strong> ${currentSending.sent}</div>
        <div class="stat error"><strong>Falhas:</strong> ${currentSending.failed}</div>
        <div class="stat"><strong>Início:</strong> ${currentSending.startTime.toLocaleString()}</div>
        <div class="stat"><strong>Fim:</strong> ${new Date().toLocaleString()}</div>
    </div>
</body>
</html>`;

    fs.writeFileSync(htmlPath, html);
    colorLog('success', `[LOG] Relatório salvo em ${path.basename(LOG_DIR)}/${path.basename(htmlPath)}`);
}

function showStatus() {
    if (!isSending) {
        colorLog('info', '[STATUS] Nenhum envio em andamento.');
        return;
    }
    
    const elapsed = ((new Date() - currentSending.startTime) / 1000).toFixed(1);
    const progress = ((currentSending.sent + currentSending.failed) / currentSending.total * 100).toFixed(1);
    
    colorLog('info', '\n[STATUS DO ENVIO]');
    console.log(`- Progresso: ${progress}%`);
    console.log(`- Tempo decorrido: ${elapsed}s`);
    console.log(`- Enviados: ${currentSending.sent}`);
    console.log(`- Falhas: ${currentSending.failed}`);
    console.log(`- Restantes: ${currentSending.total - currentSending.sent - currentSending.failed}`);
    console.log(`- Status: ${isPaused ? 'PAUSADO' : 'EM ANDAMENTO'}`);
    console.log(`- Delay atual: ${dynamicDelay}ms`);
}

function showHelp() {
    console.log(`
╔════════════════════════════════════════════╗
║          WHATSAPP BOT - COMANDOS           ║
╠════════════════════════════════════════════╣
║  $global=mensagem           → Envia msg    ║
║  $global=mensagem + arq.ext → Msg + arquivo║
║  $file=arquivo.ext          → Envia arquivo║
║  $delay=XXXX                → Altera delay ║
╠════════════════════════════════════════════╣
║  $pergunta=Pergunta $resposta=Resposta     ║
║  $removerpergunta=Pergunta  → Remove resp. ║
║  $listarperguntas           → Lista resp.  ║
╠════════════════════════════════════════════╣
║  $pause          → Pausa envio             ║
║  $resume         → Retoma envio            ║
║  $status         → Mostra status           ║
║  $standby        → Modo espera             ║
╠════════════════════════════════════════════╣
║  $updatecontacts → Atualiza contatos       ║
║  $openfiles      → Abre pasta de arquivos  ║
║  $listfiles      → Lista arquivos          ║
╠════════════════════════════════════════════╣
║  $reconnect      → Reconecta ao WhatsApp   ║
║  $logout         → Sai da sessão atual     ║
║  $showqr         → Mostra QR code novamente║
║  $autoreconnect  → Ativa/desativa auto-recon
╠════════════════════════════════════════════╣
║  $restart        → Reinicia o bot          ║
║  $shutdown       → Encerra o bot           ║
║  $help           → Mostra esta ajuda       ║
║  clear/cls       → Limpa a tela            ║
╚════════════════════════════════════════════╝
`);
}

function delay(ms) {
    return new Promise(resolve => setTimeout(resolve, ms));
}

// Tratamento de erros globais
process.on('unhandledRejection', (reason, promise) => {
    colorLog('error', '[ERRO NÃO TRATADO]', reason);
    colorLog('info', '[AÇÃO] Tentando recuperação automática em 5 segundos...');
    setTimeout(() => {
        if (client) client.destroy().then(() => {
            client = initializeClient();
        });
    }, 5000);
});

process.on('uncaughtException', (err) => {
    colorLog('error', '[ERRO CRÍTICO]', err);
    colorLog('info', '[AÇÃO] Reiniciando em 10 segundos...');
    setTimeout(() => process.exit(1), 10000);
});

// Inicialização do sistema
console.log(`
╔════════════════════════════════════════════╗
║          WHATSAPP BOT - INICIANDO          ║
╠════════════════════════════════════════════╣
║  Versão: 2.0 - www.tonch.com.br            ║
║  Diretório base: ${path.basename(BASE_DIR)}          ║
║  Arquivos: whatsapp-bot-files/             ║
║  Logs: whatsapp-bot-logs/                  ║
║  Backups: whatsapp-bot-backups/            ║
╚════════════════════════════════════════════╝
`);

setupDirectories();
client = initializeClient();
rl.prompt();