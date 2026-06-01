'use strict';
// Voice Control Center — voice_control.js
//
// 1. Web Bluetooth で M5Stack Atom Lite / AtomS3 Voice ファームに接続
// 2. Web Speech API での音声認識 (Chrome)
// 3. 音声コマンド判定 ＆ 音声-IRマッピングの管理 (localStorage)
// 4. JSで対話生成 ＆ 簡易読み仮名（ひらがな）変換
// 5. Web BT 経由での発声 (CMD_VOICE 0x60) と赤外線送信 (CMD_IR_SEND 0x40)
// 6. ハウリング防止のための音声認識一時停止制御

const VoiceControl = (() => {
  // ===== BLE UUID =====
  const SERVICE_UUID    = '12345678-1234-5678-1234-56789abcdef0';
  const CMD_CHAR_UUID   = '12345678-1234-5678-1234-56789abcdef1';
  const STS_CHAR_UUID   = '12345678-1234-5678-1234-56789abcdef2';
  const CFG_CHAR_UUID   = '12345678-1234-5678-1234-56789abcdef3';
  const IR_RX_CHAR_UUID = '12345678-1234-5678-1234-56789abcdef4';

  // ===== BLE Opcode =====
  const CMD_IR_SEND          = 0x40;
  const CMD_IR_RX_START      = 0x41;
  const CMD_IR_RX_STOP       = 0x42;
  const CMD_IR_RX_DATA_EVENT = 0x43;
  const CMD_VOICE            = 0x60;
  const CMD_VOICE_VOLUME     = 0x61;
  const VOICE_MTU_MAX        = 244;

  const ERR_NAMES = {
    0x00: 'SUCCESS', 0x01: 'INVALID_COMMAND', 0x02: 'INVALID_PAYLOAD',
    0x03: 'OUT_OF_BOUNDS', 0x04: 'MEMORY_FULL', 0x05: 'UNSUPPORTED_FMT',
    0x06: 'UNSUPPORTED_CAP', 0x07: 'PIN_BUSY', 0x08: 'VOICE_BUSY'
  };

  // ===== 簡易読み仮名変換用辞書 =====
  const KANJI_HIRA_MAP = {
    'テレビ': 'てれび', 'エアコン': 'えあこん', '電気': 'でんき', 'ライト': 'らいと',
    '電源': 'でんげん', '温度': 'おんど', '音量': 'おんりょう', 'こんにちは': 'こんにちは',
    'ありがとう': 'ありがとう', 'さようなら': 'さようなら', 'おもちゃ': 'おもちゃ',
    'ロボット': 'ろぼっと', '右': 'みぎ', '左': 'ひだり', '前': 'まえ', '後': 'うしろ',
    '進め': 'すすめ', '止まれ': 'とまれ', '曲がって': 'まがって', '動いて': 'うごいて',
    'つける': 'つける', '消す': 'けす', 'つけて': 'つけて', '消して': 'けして',
    '上げる': 'あげる', '下げる': 'さげる', '上げて': 'あげて', '下げて': 'さげて',
    'オン': 'おん', 'オフ': 'おふ', 'はい': 'はい', 'いいえ': 'いいえ', '了解': 'りょうかい',
    'わかりました': 'わかりました', 'おっけー': 'おっけー'
  };

  // 数字の読み辞書
  const NUM_YOMI = ['ぜろ', 'いち', 'に', 'さん', 'よん', 'ご', 'ろく', 'なな', 'はち', 'きゅう'];
  const NUM_TEN_YOMI = ['', 'じゅう', 'にじゅう', 'さんじゅう', 'よんじゅう', 'ごじゅう', 'ろくじゅう', 'ななじゅう', 'はちじゅう', 'きゅうじゅう'];

  // ===== 状態変数 =====
  let device = null;
  let server = null;
  let chars = { cmd: null, sts: null, cfg: null, irRx: null };
  let cfg = null;
  let isConnected = false;
  let userInitiatedDisconnect = false;

  // ===== 機種別有効 GPIO pin =====
  const DEVICE_GPIO = {
    atomlite: [12, 19, 21, 22, 23, 25, 26, 32, 33, 39],
    atoms3ir: [1, 2, 5, 6, 7, 8, 38, 39]
  };

  let config = { irTxPin: null, geminiKey: null, systemPrompt: null };
  const LOCAL_STORAGE_CONFIG_KEY = 'notif_voice_control_config';

  // 音声認識関連
  let recognition = null;
  let isSpeechActive = false; // ユーザーが明示的に開始したか
  let isMutedForSpeaking = false; // 自身の発声中に一時停止するためのフラグ
  let lastSpeechText = '';

  // 赤外線学習
  let lastIrPattern = null;

  // 音声-IRマッピングデータ
  let mappings = [];
  const LOCAL_STORAGE_MAPPINGS_KEY = 'notif_voice_ir_mappings';
  let editingMapId = null;

  // 顔認識オート起動関連
  let isFaceDetectionActive = false;
  let visionModule = null;
  let faceDetector = null;
  let cameraStream = null;
  let faceDetectionLoopActive = false;
  let lastFaceTriggerTime = 0;

  // ===== ローカル AI (Built-in Prompt API) 用ラッパーブリッジ =====
  const LocalAiBridge = {
    // 利用可能か判定する
    async checkAvailability() {
      // 1. 最新のグローバル LanguageModel クラスによる検出
      if (typeof LanguageModel !== 'undefined' && typeof LanguageModel.availability === 'function') {
        try {
          const status = await LanguageModel.availability();
          if (status !== 'no') {
            return { available: true, type: 'LanguageModel (Global)', status };
          }
        } catch (e) {
          // ignore
        }
      }

      // 2. window.ai.languageModel による検出
      if (window.ai && window.ai.languageModel) {
        // 2.a 最新の availability メソッド
        if (typeof window.ai.languageModel.availability === 'function') {
          try {
            const status = await window.ai.languageModel.availability();
            if (status !== 'no') {
              return { available: true, type: 'ai.languageModel (Availability)', status };
            }
          } catch (e) {
            // ignore
          }
        }
        // 2.b 以前の capabilities メソッド
        if (typeof window.ai.languageModel.capabilities === 'function') {
          try {
            const caps = await window.ai.languageModel.capabilities();
            if (caps && caps.available !== 'no') {
              return { available: true, type: 'ai.languageModel (Capabilities)', status: caps.available };
            }
          } catch (e) {
            // ignore
          }
        }
      }

      // 3. 旧仕様の window.ai.assistant による検出
      if (window.ai && window.ai.assistant) {
        if (typeof window.ai.assistant.capabilities === 'function') {
          try {
            const caps = await window.ai.assistant.capabilities();
            if (caps && caps.available !== 'no') {
              return { available: true, type: 'ai.assistant (Capabilities)', status: caps.available };
            }
          } catch (e) {
            // ignore
          }
        }
      }

      return { available: false, type: 'none', status: 'no' };
    },

    // セッションを作成する
    async createSession(options = {}) {
      const systemPrompt = options.systemPrompt || '';

      // 互換オプションオブジェクトの作成
      const sessionOptions = {
        // 1. 旧仕様用オプション
        systemPrompt: systemPrompt,
        // 2. 最新の Prompt API (Chrome 131以降) 仕様用オプション
        initialPrompts: systemPrompt ? [
          { role: 'system', content: systemPrompt }
        ] : [],
        // 言語設定とシステムプロンプトの整合性を確保するためのヒント設定
        expectedInputs: [
          { type: 'text', languages: ['ja'] }
        ],
        expectedOutputs: [
          { type: 'text', languages: ['ja'] }
        ]
      };

      // 1. グローバルの LanguageModel が使える場合
      if (typeof LanguageModel !== 'undefined' && typeof LanguageModel.create === 'function') {
        try {
          return await LanguageModel.create(sessionOptions);
        } catch (e) {
          console.warn('LanguageModel.create failed, falling back...', e);
        }
      }

      // 2. window.ai.languageModel が使える場合
      if (window.ai && window.ai.languageModel && typeof window.ai.languageModel.create === 'function') {
        try {
          return await window.ai.languageModel.create(sessionOptions);
        } catch (e) {
          console.warn('ai.languageModel.create failed, falling back...', e);
        }
      }

      // 3. window.ai.assistant (旧) が使える場合
      if (window.ai && window.ai.assistant && typeof window.ai.assistant.create === 'function') {
        try {
          return await window.ai.assistant.create({
            systemPrompt: systemPrompt
          });
        } catch (e) {
          console.warn('ai.assistant.create failed...', e);
        }
      }

      throw new Error('No local AI creation method available on this browser version');
    }
  };

  // ===== ユーティリティ =====
  const $ = (id) => document.getElementById(id);

  function log(msg, cls) {
    const el = $('log');
    if (!el) return;
    const ts = new Date().toLocaleTimeString();
    const line = document.createElement('div');
    if (cls) line.className = cls;
    line.textContent = `[${ts}] ${msg}`;
    el.insertBefore(line, el.firstChild);
  }

  function hex(bytes) {
    return Array.from(bytes, (b) => b.toString(16).padStart(2, '0')).join(' ');
  }

  function parseHexBytes(txt) {
    const parts = txt.trim().split(/[\s,]+/).filter(Boolean);
    const bytes = parts.map((p) => parseInt(p, 16));
    if (bytes.some(isNaN)) throw new Error('hex parse 失敗');
    return new Uint8Array(bytes);
  }

  // ===== Web Bluetooth 通信 =====
  function buildPacket(opcode, payload) {
    const pl = payload instanceof Uint8Array ? payload : new Uint8Array(payload);
    const pkt = new Uint8Array(3 + pl.length);
    pkt[0] = opcode;
    pkt[1] = pl.length & 0xff;
    pkt[2] = (pl.length >> 8) & 0xff;
    pkt.set(pl, 3);
    return pkt;
  }

  async function sendCommand(opcode, payload, label) {
    if (!chars.cmd) {
      log(`CMD char 未取得、 送信スキップ (${label})`, 'ng');
      return false;
    }
    const pkt = buildPacket(opcode, payload);
    try {
      log(`send ${label}: ${hex(pkt)}`);
      await chars.cmd.writeValueWithResponse(pkt);
      return true;
    } catch (e) {
      log(`send NG (${label}): ${e.message}`, 'ng');
      return false;
    }
  }

  // ===== 接続管理 =====
  async function connect() {
    if (!navigator.bluetooth) {
      log('Web Bluetooth API が使えません (Chrome / Edge が必要)', 'ng');
      return;
    }
    try {
      log('デバイススキャン開始...');
      device = await navigator.bluetooth.requestDevice({
        filters: [
          { namePrefix: 'notif_atom' },
          { namePrefix: 'notif_atoms3' }
        ],
        optionalServices: [SERVICE_UUID]
      });
      log(`デバイス選択: ${device.name || '(no name)'}`, 'ok');
      device.addEventListener('gattserverdisconnected', onDisconnected);

      await acquireGattAndChars();
      setConnectedState(true);
      userInitiatedDisconnect = false;
      
      // 接続成功時におしゃべりで挨拶
      setTimeout(() => {
        speakResponse("接続しました。何でも話しかけてください！", "せつぞくしました。なんでもはなしかけてください！");
      }, 1000);
    } catch (e) {
      log(`接続失敗: ${e.message}`, 'ng');
    }
  }

  async function acquireGattAndChars() {
    log('GATT 接続中...');
    server = await device.gatt.connect();
    log('GATT 接続成功', 'ok');

    const service = await server.getPrimaryService(SERVICE_UUID);
    log('BLE サービス取得成功', 'ok');

    const charSpec = [
      ['cmd',  CMD_CHAR_UUID,   'CMD'],
      ['sts',  STS_CHAR_UUID,   'STS'],
      ['cfg',  CFG_CHAR_UUID,   'CFG'],
      ['irRx', IR_RX_CHAR_UUID, 'IR_RX']
    ];

    for (const [slot, uuid, name] of charSpec) {
      try {
        chars[slot] = await service.getCharacteristic(uuid);
        log(`キャラクタリスティック ${name} 取得成功`, 'ok');
      } catch (e) {
        log(`キャラクタリスティック ${name} は利用できません: ${e.message}`);
      }
    }

    if (chars.sts && chars.sts.properties.notify) {
      await chars.sts.startNotifications();
      chars.sts.addEventListener('characteristicvaluechanged', onStsNotify);
      log('STS 通知購読開始', 'ok');
    }

    await readCfg();
  }

  async function readCfg() {
    if (!chars.cfg || !chars.cfg.properties.read) {
      log('CFG 読み込み不可');
      cfg = null;
      return;
    }
    try {
      const dv = await chars.cfg.readValue();
      const txt = new TextDecoder().decode(new Uint8Array(dv.buffer));
      cfg = JSON.parse(txt);
      log(`CFG: type=${cfg.type} fw=${cfg.fw} caps=[${(cfg.caps || []).join(',')}]`, 'ok');
      $('cfgView').textContent = JSON.stringify(cfg, null, 2);
      
      // capability に応じたUIの有効・無効化
      applyCapabilities(cfg.caps || []);
      
      // 接続デバイスに合わせたポート選択肢の更新
      populateSettingsGpioSelects();
    } catch (e) {
      log(`CFGパース失敗: ${e.message}`, 'ng');
      cfg = null;
    }
  }

  function applyCapabilities(caps) {
    const hasIrRx = caps.includes('ir_rx');
    const irRxCard = $('irRxCard');
    
    // 赤外線学習ボタン制御
    $('btnIrRxStart').disabled = !hasIrRx;
    $('btnIrRxStop').disabled = true;

    if (!hasIrRx) {
      log('このデバイスは赤外線受信(学習)に対応していません（IRユニット未装着）');
      irRxCard.style.opacity = '0.6';
    } else {
      log('赤外線受信(学習)機能が利用可能です', 'ok');
      irRxCard.style.opacity = '1';
    }
  }

  function onStsNotify(ev) {
    const bytes = new Uint8Array(ev.target.value.buffer);
    if (bytes.length === 0) return;
    const code = bytes[0];
    const name = ERR_NAMES[code] || `UNKNOWN(0x${code.toString(16)})`;
    log(`STS通知: ${name} (0x${code.toString(16).padStart(2, '0')})`, code === 0 ? 'ok' : 'ng');
  }

  function onDisconnected() {
    log('BLE 接続が切断されました', 'ng');
    setConnectedState(false);
    
    if (isSpeechActive) {
      stopSpeechRecognition();
    }

    if (!userInitiatedDisconnect) {
      log('自動再接続を試みます...');
      // 簡易的な自動再接続
      setTimeout(async () => {
        if (!device) return;
        try {
          await acquireGattAndChars();
          setConnectedState(true);
          log('自動再接続に成功しました', 'ok');
        } catch (e) {
          log('自動再接続失敗。手動で再度接続してください。', 'ng');
        }
      }, 2000);
    }
  }

  async function disconnect() {
    userInitiatedDisconnect = true;
    if (isSpeechActive) {
      stopSpeechRecognition();
    }
    if (device && device.gatt.connected) {
      device.gatt.disconnect();
      log('手動切断しました');
    }
    setConnectedState(false);
  }

  function setConnectedState(connected) {
    isConnected = connected;
    $('btnConnect').disabled = connected;
    $('btnDisconnect').disabled = !connected;
    
    const badge = $('connStatus');
    if (connected) {
      badge.textContent = '接続中';
      badge.className = 'status-badge connected';
    } else {
      badge.textContent = '未接続';
      badge.className = 'status-badge';
      $('cfgView').textContent = '未接続';
      $('btnIrRxStart').disabled = true;
      $('btnIrRxStop').disabled = true;
      $('btnIrSave').disabled = true;
    }
  }

  // ===== 音声認識 (Web Speech API) =====
  function initSpeechRecognition() {
    const SpeechRecognition = window.SpeechRecognition || window.webkitSpeechRecognition;
    if (!SpeechRecognition) {
      $('browserAlert').style.display = 'block';
      log('SpeechRecognition API がこのブラウザでサポートされていません', 'ng');
      return;
    }

    recognition = new SpeechRecognition();
    recognition.lang = 'ja-JP';
    recognition.continuous = true;
    recognition.interimResults = false;

    recognition.onstart = () => {
      if (isMutedForSpeaking) return; // 自身の発声による自動On/Offはステータス変化させない
      setSphereState('listening', '音声認識中...');
    };

    recognition.onerror = (event) => {
      if (event.error !== 'no-speech') {
        log(`音声認識エラー: ${event.error}`, 'ng');
      }
    };

    recognition.onend = () => {
      // ユーザーが停止していない、かつ発声のためのミュート中でない場合は、自動で再起動して連続待ち受け
      if (isSpeechActive && !isMutedForSpeaking) {
        try {
          recognition.start();
        } catch (e) {
          // すでに開始している場合の例外は無視
        }
      } else if (!isSpeechActive) {
        setSphereState('standby', 'STANDBY');
      }
    };

    recognition.onresult = (event) => {
      if (isMutedForSpeaking) return; // 発声中は自分の声を無視

      const resultIndex = event.resultIndex;
      const transcript = event.results[resultIndex][0].transcript.trim();
      log(`音声認識結果: 「${transcript}」`, 'ok');
      
      appendChatMessage(transcript, 'user');
      handleVoiceCommand(transcript);
    };
  }

  function startSpeechRecognition() {
    if (!recognition) return;
    isSpeechActive = true;
    isMutedForSpeaking = false;
    try {
      recognition.start();
      $('btnToggleSpeech').textContent = '音声認識を停止する';
      $('btnToggleSpeech').className = 'btn-accent';
      log('音声待ち受けを開始しました');
    } catch (e) {
      log('音声認識開始エラー: ' + e.message, 'ng');
    }
  }

  function stopSpeechRecognition() {
    isSpeechActive = false;
    if (!recognition) return;
    try {
      recognition.stop();
      $('btnToggleSpeech').textContent = '音声認識を開始する';
      $('btnToggleSpeech').className = 'btn-primary';
      setSphereState('standby', 'STANDBY');
      log('音声待ち受けを停止しました');
    } catch (e) {
      log('音声認識停止エラー: ' + e.message, 'ng');
    }
  }

  function setSphereState(state, labelText) {
    const sphere = $('voiceSphere');
    const label = $('voiceStatusLabel');
    if (!sphere || !label) return;

    sphere.className = 'voice-sphere';
    if (state === 'listening') {
      sphere.classList.add('listening');
    } else if (state === 'speaking') {
      sphere.classList.add('speaking');
    }

    label.textContent = labelText;
  }

  // ===== コマンド判定 ＆ 対話生成 ＆ 送信処理 =====
  async function handleVoiceCommand(text) {
    let matched = false;

    // 1. ユーザー定義マッピングからマッチング検索
    for (const map of mappings) {
      if (!map.trigger) continue;
      try {
        const regex = new RegExp(map.trigger, 'i');
        if (regex.test(text)) {
          matched = true;
          log(`マッピングにマッチ: 「${map.trigger}」`, 'ok');

          // 赤外線送信処理 (紐付けがある場合)
          if (map.irCodeName) {
            await sendStoredIrByName(map.irCodeName);
          }

          // 読み仮名の解決
          let responseText = map.response || "わかりました";
          let responseYomi = map.responseYomi || convertToYomi(responseText);

          await speakResponse(responseText, responseYomi);
          break;
        }
      } catch (err) {
        log(`正規表現エラー (${map.trigger}): ${err.message}`, 'ng');
      }
    }

    // 2. マッチしなかった場合の自然対話への自動移行
    if (!matched) {
      setSphereState('speaking', 'AI応答生成中...');
      log('定型コマンドに不一致。自然対話（AI）に移行します。');
      
      let responseText = "";
      let responseYomi = "";
      
      try {
        responseText = await generateAiResponse(text);
        responseYomi = convertToYomi(responseText);
      } catch (err) {
        log(`AI応答生成エラー: ${err.message}`, 'ng');
        responseText = "よく聞き取れませんでした。もう一度言ってみてください。";
        responseYomi = "よくききとれませんでした。もういちど いってみてください。";
      }
      
      await speakResponse(responseText, responseYomi);
    }
  }

  // 音声応答の再生 (ハウリング防止の制御込み)
  async function speakResponse(text, yomi) {
    appendChatMessage(text, 'toy');

    // 自身の発声をマイクが拾わないように一時的に音声認識のイベント処理を無効化
    if (isSpeechActive && recognition) {
      isMutedForSpeaking = true;
      recognition.stop(); // 一旦止める
      setSphereState('speaking', '発声中...');
    } else {
      setSphereState('speaking', '発声中...');
    }

    // 音量適用
    await sendVoiceVolume();

    // クレンジングされた読みの取得
    const cleanYomi = cleanYomiText(yomi);
    const bytes = new TextEncoder().encode(cleanYomi);

    if (bytes.length > VOICE_MTU_MAX) {
      log(`音声テキストが長すぎます (${bytes.length} bytes / 最大 244)`, 'ng');
      setSphereState('standby', 'STANDBY');
      return;
    }

    // BLE送信
    log(`発声送信: 「${cleanYomi}」 (${bytes.length}B)`);
    const success = await sendCommand(CMD_VOICE, bytes, `VOICE("${cleanYomi}")`);

    // 発声の長さを概算して、その間マイクをミュートする
    // 標準的な発声速度: 1文字あたり約 250ms + 500msバッファ
    const delay = Math.max(1500, cleanYomi.length * 250 + 500);

    setTimeout(() => {
      isMutedForSpeaking = false;
      setSphereState('standby', 'STANDBY');
      
      // ユーザーが音声認識を有効にしていた場合は、マイクを再開
      if (isSpeechActive && recognition) {
        try {
          recognition.start();
          setSphereState('listening', '音声認識中...');
        } catch (e) {
          // すでに動いている場合の例外
        }
      }
    }, delay);
  }

  async function sendVoiceVolume() {
    let vol = parseInt($('voiceVolume').value, 10);
    if (isNaN(vol)) vol = 70;
    await sendCommand(CMD_VOICE_VOLUME, new Uint8Array([vol]), `VOLUME(${vol})`);
  }

  // ===== 漢字 $\rightarrow$ ひらがな（読み仮名）簡易変換ロジック =====
  function convertToYomi(text) {
    let result = text;

    // 1. 簡易漢字/カタカナ置換
    for (const [kanji, hira] of Object.entries(KANJI_HIRA_MAP)) {
      const regex = new RegExp(kanji, 'g');
      result = result.replace(regex, hira);
    }

    // 2. 数字（0-99）の読み変換
    result = result.replace(/\d+/g, (match) => {
      const num = parseInt(match, 10);
      if (num >= 0 && num < 100) {
        return convertNumberToJapanese(num);
      }
      return match;
    });

    // 3. カタカナからひらがなへの単純置換
    result = result.replace(/[\u30a1-\u30f6]/g, (match) => {
      return String.fromCharCode(match.charCodeAt(0) - 0x60);
    });

    return result;
  }

  function convertNumberToJapanese(num) {
    if (num === 0) return NUM_YOMI[0];
    if (num < 10) return NUM_YOMI[num];
    
    const ten = Math.floor(num / 10);
    const one = num % 10;
    
    const tenStr = NUM_TEN_YOMI[ten];
    const oneStr = one === 0 ? '' : NUM_YOMI[one];
    
    return tenStr + oneStr;
  }

  // Atom (AquesTalk系) が発声できるひらがな、記号以外をクリア
  function cleanYomiText(text) {
    // 読点「、」やスペースは一時的に保持し、英数字・ひらがな・長音「ー」・スペースのみ残す
    let clean = text.replace(/[。！？」]/g, ' ');
    
    // 挨拶の中の助詞「は」を「わ」に変換する安全な対応のみ実施
    clean = clean.replace(/こんにちは/g, 'こんにちわ');
    clean = clean.replace(/こんばんは/g, 'こんばんわ');
    
    // カタカナ・ひらがな変換後の残存漢字を排除し、ひらがな/数字/アルファベット/スペースのみにする
    // ひらがな範囲: \u3040-\u309F、長音: ー
    // アルファベット・数字、スペース
    const allowedRegex = /[\u3040-\u309fーa-zA-Z0-9\s]/g;
    const matches = clean.match(allowedRegex);
    return matches ? matches.join('') : '';
  }

  // ===== JSON バックアップエクスポート / インポート機能 =====
  function exportIrBackup() {
    try {
      // 1. 所有しているすべての赤外線パターンを収集
      const irPatterns = {};
      const keys = Object.keys(localStorage).filter((k) => k.startsWith('notif_ir_')).sort();
      keys.forEach((key) => {
        const name = key.replace(/^notif_ir_/, '');
        irPatterns[name] = localStorage.getItem(key);
      });

      // 2. 音声マッピングの収集
      const voiceMappings = mappings;

      // 3. バックアップ用JSONデータの作成
      const backupData = {
        version: "1.0",
        exportedAt: new Date().toISOString(),
        irPatterns: irPatterns,
        voiceMappings: voiceMappings
      };

      // 4. ダウンロード処理の実行
      const jsonStr = JSON.stringify(backupData, null, 2);
      const blob = new Blob([jsonStr], { type: 'application/json' });
      const url = URL.createObjectURL(blob);
      
      const a = document.createElement('a');
      a.href = url;
      a.download = `voice_control_backup_${new Date().toISOString().slice(0,10)}.json`;
      document.body.appendChild(a);
      a.click();
      document.body.removeChild(a);
      URL.revokeObjectURL(url);
      
      log('赤外線コマンドおよびマッピング設定をエクスポートしました', 'ok');
    } catch (e) {
      log(`エクスポート失敗: ${e.message}`, 'ng');
    }
  }

  function triggerIrImport() {
    const fileInput = $('irImportFile');
    if (fileInput) fileInput.click();
  }

  function handleIrImport(e) {
    const file = e.target.files[0];
    if (!file) return;

    const reader = new FileReader();
    reader.onload = function(evt) {
      try {
        const data = JSON.parse(evt.target.result);
        
        // 簡易バリデーション
        if (!data || typeof data !== 'object') {
          throw new Error('無効な JSON フォーマットです');
        }

        let irCount = 0;
        let mapCount = 0;

        // 1. 赤外線パターンの復元
        if (data.irPatterns && typeof data.irPatterns === 'object') {
          for (const [name, pattern] of Object.entries(data.irPatterns)) {
            localStorage.setItem(`notif_ir_${name}`, pattern);
            irCount++;
          }
        }

        // 2. 音声マッピングの復元 (マージ)
        if (Array.isArray(data.voiceMappings)) {
          data.voiceMappings.forEach(newMap => {
            if (!newMap.trigger) return;
            const index = mappings.findIndex(m => m.trigger === newMap.trigger);
            if (index !== -1) {
              mappings[index] = newMap;
            } else {
              mappings.push(newMap);
            }
            mapCount++;
          });
          localStorage.setItem(LOCAL_STORAGE_MAPPINGS_KEY, JSON.stringify(mappings));
        }

        // UIの再読み込み
        refreshIrSelects();
        renderMappings();
        
        alert(`インポートが完了しました！\n赤外線パターン: ${irCount} 件\n音声マッピング: ${mapCount} 件を復元/更新しました。`);
        log(`JSONバックアップをインポートしました (IR: ${irCount}件, マッピング: ${mapCount}件)`, 'ok');
        
        e.target.value = '';
      } catch (err) {
        alert(`インポートエラー: ${err.message}`);
        log(`インポートに失敗しました: ${err.message}`, 'ng');
      }
    };
    reader.readAsText(file);
  }

  // ===== 赤外線コードの読み込みと送信 =====
  async function sendStoredIrByName(name) {
    const key = `notif_ir_${name}`;
    const rawData = localStorage.getItem(key);
    if (!rawData) {
      log(`赤外線パターン 「${name}」 が localStorage に見つかりません`, 'ng');
      return false;
    }
    
    try {
      const pattern = JSON.parse(rawData);
      const hasRaw = Array.isArray(pattern.raw_timings) && pattern.raw_timings.length > 0;
      let protoId;
      let data;
      
      if (hasRaw) {
        protoId = 3; // RAW強制
        const buf = new ArrayBuffer(pattern.raw_timings.length * 2);
        const dv = new DataView(buf);
        pattern.raw_timings.forEach((t, i) => dv.setUint16(i * 2, t & 0xffff, true));
        data = new Uint8Array(buf);
      } else {
        protoId = pattern.proto_id & 0xff;
        data = parseHexBytes(pattern.value_hex || '');
      }

      const freq = pattern.freq_khz || 38;
      const headLen = 5;
      const hasPin = (typeof config.irTxPin === 'number') && !isNaN(config.irTxPin) && config.irTxPin !== null;
      const plLen = headLen + data.length + (hasPin ? 1 : 0);
      const pl = new Uint8Array(plLen);
      pl[0] = protoId;
      pl[1] = 0; // repeat 0
      pl[2] = freq;
      pl[3] = data.length & 0xff;
      pl[4] = (data.length >> 8) & 0xff;
      pl.set(data, headLen);
      if (hasPin) {
        pl[plLen - 1] = config.irTxPin & 0xff;
      }

      const pinLabel = hasPin ? `, Pin=${config.irTxPin}` : '';
      log(`赤外線送信: [${name}] (Proto=${protoId}, Freq=${freq}kHz, Len=${data.length}${pinLabel})`);
      return await sendCommand(CMD_IR_SEND, pl, `IR_SEND(${name}${pinLabel})`);
    } catch (e) {
      log(`赤外線データ送信失敗: ${e.message}`, 'ng');
      return false;
    }
  }

  // ===== 赤外線学習 (オプショナル) =====
  async function irRxStart() {
    if (!chars.irRx) return;
    try {
      if (chars.irRx.properties.notify) {
        await chars.irRx.startNotifications();
        chars.irRx.addEventListener('characteristicvaluechanged', onIrRxData);
      }
      await sendCommand(CMD_IR_RX_START, new Uint8Array(0), 'IR_RX_START');
      $('btnIrRxStart').disabled = true;
      $('btnIrRxStop').disabled = false;
      log('赤外線学習を開始しました。リモコンを押してください。', 'ok');
    } catch (e) {
      log(`学習開始エラー: ${e.message}`, 'ng');
    }
  }

  async function irRxStop() {
    try {
      await sendCommand(CMD_IR_RX_STOP, new Uint8Array(0), 'IR_RX_STOP');
      if (chars.irRx && chars.irRx.properties.notify) {
        await chars.irRx.stopNotifications();
      }
      $('btnIrRxStart').disabled = false;
      $('btnIrRxStop').disabled = true;
      log('赤外線学習を停止しました。');
    } catch (e) {
      log(`学習停止エラー: ${e.message}`, 'ng');
    }
  }

  function onIrRxData(ev) {
    const dv = ev.target.value;
    if (dv.byteLength < 7) return;

    const eventType = dv.getUint8(0);
    if (eventType !== CMD_IR_RX_DATA_EVENT) return;

    const protoId = dv.getUint8(1);
    const bits    = dv.getUint8(2);
    const repeat  = dv.getUint8(3);
    const dataLen = dv.getUint16(4, true);
    
    let off = 6;
    const data = new Uint8Array(dv.buffer, dv.byteOffset + off, dataLen);
    off += dataLen;

    const rawCount = dv.getUint16(off, true);
    off += 2;
    
    const rawTimings = [];
    for (let i = 0; i < rawCount && off + 1 < dv.byteLength; i++) {
      rawTimings.push(dv.getUint16(off, true));
      off += 2;
    }

    const protoNames = { 1: 'NEC', 2: 'Panasonic', 3: 'RAW', 4: 'Sony', 5: 'RC5' };
    const protoName = protoNames[protoId] || 'UNKNOWN';

    lastIrPattern = {
      protocol: protoName,
      proto_id: protoId,
      bits,
      repeat,
      value_hex: hex(data),
      raw_timings: rawTimings,
      freq_khz: 38
    };

    $('irRxView').textContent = JSON.stringify(lastIrPattern, null, 2);
    $('btnIrSave').disabled = false;
    log(`赤外線信号受信成功! [${protoName}] rawTimings=${rawCount}個`, 'ok');
  }

  function saveIrPattern() {
    if (!lastIrPattern) return;
    const name = $('irPatternName').value.trim();
    if (!name) {
      alert('赤外線パターンの名前を入力してください');
      return;
    }

    const key = `notif_ir_${name}`;
    localStorage.setItem(key, JSON.stringify(lastIrPattern));
    log(`赤外線パターンを保存しました: ${name}`, 'ok');

    $('irPatternName').value = '';
    $('btnIrSave').disabled = true;
    $('irRxView').textContent = '(未受信)';
    lastIrPattern = null;

    // マッピング登録用のセレクトボックスをリフレッシュ
    refreshIrSelects();
  }

  // ===== 音声-IRマッピングエディタ (CRUD) =====
  function loadMappings() {
    const raw = localStorage.getItem(LOCAL_STORAGE_MAPPINGS_KEY);
    if (raw) {
      try {
        mappings = JSON.parse(raw);
      } catch (e) {
        log('マッピングデータのパース失敗。初期化します。', 'ng');
        mappings = [];
      }
    } else {
      // デフォルトマッピングの設定
      mappings = [
        {
          id: 'def_1',
          trigger: 'テレビ.*(つけて|オン)',
          irCodeName: 'tv_power',
          response: 'テレビをつけますね。ピッと送信しました！',
          responseYomi: 'てれびお つけますね。ぴっと そうしんしました！'
        },
        {
          id: 'def_2',
          trigger: '電気.*(つけて|オン)',
          irCodeName: 'light_on',
          response: '電気をつけます。',
          responseYomi: 'でんきお つけます。'
        },
        {
          id: 'def_3',
          trigger: 'ロボット.*(前|進め)',
          irCodeName: 'toy_forward',
          response: '前へ進みます！トコトコ！',
          responseYomi: 'まええ すすみます！とことこ！'
        }
      ];
      saveMappingsToStorage();
    }
    renderMappings();
  }

  function saveMappingsToStorage() {
    localStorage.setItem(LOCAL_STORAGE_MAPPINGS_KEY, JSON.stringify(mappings));
  }

  function renderMappings() {
    const list = $('mappingList');
    if (!list) return;
    list.innerHTML = '';

    if (mappings.length === 0) {
      list.innerHTML = '<div style="color: var(--text-muted); font-size: 0.9rem; text-align: center; padding: 1rem;">登録されたマッピングはありません。</div>';
      return;
    }

    mappings.forEach((map) => {
      const item = document.createElement('div');
      item.className = 'mapping-item';
      
      const irExists = map.irCodeName ? localStorage.getItem(`notif_ir_${map.irCodeName}`) !== null : false;
      const irCodeHtml = map.irCodeName 
        ? (irExists 
            ? escapeHtml(map.irCodeName) 
            : `<span style="color: var(--danger); font-weight: bold;">${escapeHtml(map.irCodeName)} (⚠️ 未登録 / 削除済み)</span>`
          )
        : '(なし)';

      const isIrSendDisabled = map.irCodeName && irExists ? '' : 'disabled style="opacity: 0.3; cursor: not-allowed;"';

      item.innerHTML = `
        <div class="mapping-fields">
          <div>
            <span class="mapping-label">音声トリガー (正規表現):</span>
            <div class="mapping-value" style="color: var(--secondary);">${escapeHtml(map.trigger)}</div>
          </div>
          <div style="margin-top: 0.3rem;">
            <span class="mapping-label">赤外線コード:</span>
            <div class="mapping-value">${irCodeHtml}</div>
          </div>
        </div>
        <div class="mapping-fields">
          <div>
            <span class="mapping-label">返答テキスト:</span>
            <div class="mapping-value">${escapeHtml(map.response || '')}</div>
          </div>
          <div style="margin-top: 0.3rem;">
            <span class="mapping-label">発声読み (ひらがな):</span>
            <div class="mapping-value" style="font-size: 0.8rem; color: var(--text-muted);">${escapeHtml(map.responseYomi || '')}</div>
          </div>
        </div>
        <div class="mapping-actions">
          <button class="btn-accent btn-test-voice" data-id="${map.id}">テスト発声</button>
          <button class="btn-primary btn-test-ir" data-id="${map.id}" ${isIrSendDisabled}>テスト送信</button>
          <button style="background: rgba(6, 182, 212, 0.15); border: 1px solid var(--primary); color: var(--primary);" class="btn-edit" data-id="${map.id}">修正</button>
          <button class="btn-danger btn-delete" data-id="${map.id}">削除</button>
        </div>
      `;

      list.appendChild(item);
    });

    // 削除ボタンイベント設定
    list.querySelectorAll('.btn-delete').forEach((btn) => {
      btn.addEventListener('click', () => {
        const id = btn.dataset.id;
        deleteMapping(id);
      });
    });

    // 修正ボタンイベント設定
    list.querySelectorAll('.btn-edit').forEach((btn) => {
      btn.addEventListener('click', () => {
        const id = btn.dataset.id;
        startEditMapping(id);
      });
    });

    // テスト発声イベント設定
    list.querySelectorAll('.btn-test-voice').forEach((btn) => {
      btn.addEventListener('click', () => {
        const id = btn.dataset.id;
        const map = mappings.find((m) => m.id === id);
        if (map) {
          if (!isConnected) {
            alert('発声テストを行うには、先にBLEデバイスに接続してください。');
            return;
          }
          speakResponse(map.response, map.responseYomi);
        }
      });
    });

    // テスト送信イベント設定
    list.querySelectorAll('.btn-test-ir').forEach((btn) => {
      btn.addEventListener('click', async () => {
        const id = btn.dataset.id;
        const map = mappings.find((m) => m.id === id);
        if (map && map.irCodeName) {
          if (!isConnected) {
            alert('赤外線テスト送信を行うには、先にBLEデバイスに接続してください。');
            return;
          }
          const success = await sendStoredIrByName(map.irCodeName);
          if (success) {
            log(`テスト送信成功: ${map.irCodeName}`, 'ok');
          }
        }
      });
    });
  }

  function addMapping() {
    const trigger = $('newTrigger').value.trim();
    const irCodeName = $('newIrCode').value;
    const response = $('newResponse').value.trim();
    let responseYomi = $('newResponseYomi').value.trim();

    if (!trigger) {
      alert('音声トリガーを入力してください');
      return;
    }

    if (!responseYomi && response) {
      // 読み仮名が空の場合は自動変換
      responseYomi = convertToYomi(response);
    }

    if (editingMapId) {
      // 編集（修正）モード時の処理
      const index = mappings.findIndex((m) => m.id === editingMapId);
      if (index !== -1) {
        mappings[index].trigger = trigger;
        mappings[index].irCodeName = irCodeName || null;
        mappings[index].response = response || "わかりました";
        mappings[index].responseYomi = responseYomi || "わかりました";
        
        saveMappingsToStorage();
        renderMappings();
        log(`音声アクションを修正しました: 「${trigger}」`, 'ok');
      }
      cancelEditMapping();
    } else {
      // 新規登録モード時の処理
      const newMap = {
        id: 'map_' + Date.now(),
        trigger,
        irCodeName: irCodeName || null,
        response: response || "わかりました",
        responseYomi: responseYomi || "わかりました"
      };

      mappings.push(newMap);
      saveMappingsToStorage();
      renderMappings();

      // フォーム初期化
      $('newTrigger').value = '';
      $('newIrCode').value = '';
      $('newResponse').value = '';
      $('newResponseYomi').value = '';
      
      toggleAccordion($('addFormPanel'), $('addFormCaret'), false);
      
      log(`新しい音声アクションを登録しました: 「${trigger}」`, 'ok');
    }
  }

  function startEditMapping(id) {
    const map = mappings.find((m) => m.id === id);
    if (!map) return;

    editingMapId = id;
    
    // UIを編集状態に切り替え
    $('addFormTitle').textContent = '✍️ 音声アクションを修正';
    $('btnAddMapping').textContent = '修正を保存';
    $('btnCancelEdit').style.display = 'inline-block';
    
    // フォームに値を流し込み
    $('newTrigger').value = map.trigger || '';
    $('newIrCode').value = map.irCodeName || '';
    $('newResponse').value = map.response || '';
    $('newResponseYomi').value = map.responseYomi || '';

    // アコーディオンを強制的に開く
    toggleAccordion($('addFormPanel'), $('addFormCaret'), true);
    
    // フォームの先頭にスクロール
    $('addFormPanel').scrollIntoView({ behavior: 'smooth', block: 'center' });
  }

  function cancelEditMapping() {
    editingMapId = null;
    
    // UIを通常状態に戻す
    $('addFormTitle').textContent = '+ 新しい音声アクションを追加';
    $('btnAddMapping').textContent = 'マッピングを登録';
    $('btnCancelEdit').style.display = 'none';
    
    // フォームクリア
    $('newTrigger').value = '';
    $('newIrCode').value = '';
    $('newResponse').value = '';
    $('newResponseYomi').value = '';
    
    // アコーディオンを閉じる
    toggleAccordion($('addFormPanel'), $('addFormCaret'), false);
  }

  function deleteMapping(id) {
    if (confirm('このマッピングを削除してもよろしいですか？')) {
      if (editingMapId === id) {
        cancelEditMapping();
      }
      mappings = mappings.filter((m) => m.id !== id);
      saveMappingsToStorage();
      renderMappings();
      log('マッピングを削除しました');
    }
  }

  // 保存済赤外線コードのセレクトボックス反映
  function refreshIrSelects() {
    const select = $('newIrCode');
    if (!select) return;
    
    select.innerHTML = '<option value="">(赤外線なし - 対話のみ)</option>';
    
    const keys = Object.keys(localStorage).filter((k) => k.startsWith('notif_ir_')).sort();
    keys.forEach((key) => {
      const name = key.replace(/^notif_ir_/, '');
      const option = document.createElement('option');
      option.value = name;
      option.textContent = name;
      select.appendChild(option);
    });
  }

  // ===== UI制御 (アコーディオン、チャットなど) =====
  function toggleAccordion(panel, caret, forceOpen = null) {
    const isExpanded = forceOpen !== null ? forceOpen : panel.classList.contains('collapsed');
    
    if (isExpanded) {
      panel.classList.remove('collapsed');
      panel.classList.add('expanded');
      caret.classList.add('up');
    } else {
      panel.classList.remove('expanded');
      panel.classList.add('collapsed');
      caret.classList.remove('up');
    }
  }

  function appendChatMessage(text, role) {
    const feed = $('chatFeed');
    if (!feed) return;

    const msg = document.createElement('div');
    msg.className = `chat-msg ${role}`;
    
    const prefix = role === 'user' ? 'あなた: ' : 'おもちゃ: ';
    msg.textContent = role === 'system' ? text : `${prefix}${text}`;
    
    feed.appendChild(msg);
    feed.scrollTop = feed.scrollHeight;
  }

  function escapeHtml(str) {
    if (!str) return '';
    return str
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;')
      .replace(/"/g, '&quot;')
      .replace(/'/g, '&#039;');
  }

  // ===== デフォルトのAIシステムプロンプト =====
  const DEFAULT_SYSTEM_PROMPT = "あなたの名前は「のんきなの」ちゃんです。あなたはのんびり屋でおっとりしたおもちゃのロボットです。ユーザーの発言に対して、必ず30文字以内の非常に短いメッセージで、温かくのんびりとしたフレンドリーな口調（語尾に「〜なの」や「〜ですわ」を多用する）で応答してください。また、ロボットが正しく日本語で発音できるように、漢字は一切使わず、必ず【すべてひらがな、カタカナ、スペース】のみで出力してください。";

  // ===== 設定管理 =====
  function loadConfig() {
    const raw = localStorage.getItem(LOCAL_STORAGE_CONFIG_KEY);
    if (raw) {
      try {
        config = JSON.parse(raw);
        config.geminiKey = config.geminiKey || null;
        config.systemPrompt = config.systemPrompt || DEFAULT_SYSTEM_PROMPT;
      } catch (e) {
        log('設定パース失敗。初期化します。', 'ng');
      }
    } else {
      config.systemPrompt = DEFAULT_SYSTEM_PROMPT;
    }
  }

  function saveConfig() {
    localStorage.setItem(LOCAL_STORAGE_CONFIG_KEY, JSON.stringify(config));
  }

  function populateSettingsGpioSelects() {
    const select = $('settingsIrTxPin');
    if (!select) return;
    
    const currentVal = config.irTxPin;
    select.innerHTML = '<option value="">(デフォルト - ファーム標準)</option>';
    
    // デバイス接続済ならそのピンリスト、未接続なら全ピンをマージ
    let pins = [];
    if (cfg && cfg.type && DEVICE_GPIO[cfg.type]) {
      pins = DEVICE_GPIO[cfg.type];
    } else {
      // 両方のピンを重複排除してマージ
      pins = Array.from(new Set([...DEVICE_GPIO.atomlite, ...DEVICE_GPIO.atoms3ir])).sort((a,b) => a - b);
    }
    
    pins.forEach((p) => {
      const opt = document.createElement('option');
      opt.value = String(p);
      opt.textContent = `G${p}`;
      select.appendChild(opt);
    });
    
    if (currentVal !== null && pins.includes(Number(currentVal))) {
      select.value = String(currentVal);
    }

    // Gemini APIキーの復元
    const keyInput = $('settingsGeminiKey');
    if (keyInput) {
      keyInput.value = config.geminiKey || '';
    }

    // システムプロンプトの復元
    const promptInput = $('settingsSystemPrompt');
    if (promptInput) {
      promptInput.value = config.systemPrompt || DEFAULT_SYSTEM_PROMPT;
    }

    // ローカルAIステータスチェック
    checkLocalAiStatus();
  }

  async function checkLocalAiStatus() {
    const badge = $('localAiStatus');
    if (!badge) return;
    const guide = $('localAiGuide');
    
    try {
      const result = await LocalAiBridge.checkAvailability();
      if (result.available) {
        let statusJp = '利用可能';
        if (result.status === 'readily') {
          statusJp = '即時利用可能';
        } else if (result.status === 'after-download') {
          statusJp = 'ダウンロード完了後に利用可能';
        }
        badge.textContent = `対応 / ${statusJp} (Gemini Nano)`;
        badge.style.color = 'var(--success)';
        if (guide) guide.style.display = 'none';
        log(`ローカル AI が利用可能です (検出タイプ: ${result.type}, ステータス: ${result.status})`, 'ok');
        return;
      }
    } catch (e) {
      log(`ローカル AI 検出中にエラーが発生しました: ${e.message}`, 'error');
    }
    
    badge.textContent = '非対応 / 未検出';
    badge.style.color = 'var(--error)';
    if (guide) guide.style.display = 'block';
  }

  async function generateAiResponse(inputText) {
    const prompt = config.systemPrompt || DEFAULT_SYSTEM_PROMPT;

    // 1. Chrome Built-in AI (Gemini Nano) を優先使用
    try {
      const check = await LocalAiBridge.checkAvailability();
      if (check.available) {
        log(`ローカル AI (Gemini Nano) を起動中... (プロンプトサイズ: ${prompt.length} 文字)`);
        console.log('Sending system prompt to local AI:', prompt);
        const session = await LocalAiBridge.createSession({
          systemPrompt: prompt
        });
        const reply = await session.prompt(inputText);
        
        // 破棄メソッドの安全な呼び出し (destroy または close)
        if (typeof session.destroy === 'function') {
          session.destroy();
        } else if (typeof session.close === 'function') {
          session.close();
        }
        
        log(`ローカル AI 応答: 「${reply.trim()}」`, 'ok');
        return reply.trim();
      }
    } catch (e) {
      log(`ローカル AI 起動・実行失敗、フォールバックします: ${e.message}`);
    }

    // 2. 外部 Gemini API をフォールバックとして使用
    if (config.geminiKey) {
      log('外部 Gemini API を呼び出し中...');
      const url = `https://generativelanguage.googleapis.com/v1beta/models/gemini-2.5-flash:generateContent?key=${config.geminiKey}`;
      const payload = {
        contents: [
          {
            role: "user",
            parts: [{ text: `${prompt}\n\nユーザーの発言: "${inputText}"` }]
          }
        ],
        generationConfig: {
          maxOutputTokens: 50,
          temperature: 0.7
        }
      };
      
      const res = await fetch(url, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify(payload)
      });
      
      if (!res.ok) throw new Error(`Gemini API エラー (Status: ${res.status})`);
      const json = await res.json();
      const reply = json.candidates?.[0]?.content?.parts?.[0]?.text;
      if (reply) {
        log(`Gemini API 応答: 「${reply.trim()}」`, 'ok');
        return reply.trim();
      }
      throw new Error('Gemini API から有効な返答が得られませんでした');
    }

    throw new Error('利用可能な自然対話AIエンジンがありません（APIキー未設定、または非対応ブラウザ）');
  }

  // ===== 顔認識オート起動機能 (MediaPipe Face Detector) =====
  function updateFaceStatus(state) {
    const badge = $('faceStatusBadge');
    if (badge) {
      badge.textContent = state.toUpperCase();
      if (state === 'active' || state === 'detecting') {
        badge.style.background = 'rgba(16, 185, 129, 0.15)';
        badge.style.color = 'var(--success)';
      } else if (state === 'loading') {
        badge.style.background = 'rgba(245, 158, 11, 0.15)';
        badge.style.color = '#f59e0b';
      } else if (state === 'error') {
        badge.style.background = 'rgba(239, 68, 68, 0.15)';
        badge.style.color = 'var(--error)';
      } else {
        badge.style.background = 'rgba(255, 255, 255, 0.05)';
        badge.style.color = 'var(--text-muted)';
      }
    }
    
    const btn = $('btnToggleFaceDetection');
    if (btn) {
      if (state === 'active' || state === 'detecting') {
        btn.textContent = '顔認識を停止';
        btn.style.background = 'rgba(239, 68, 68, 0.15)';
        btn.style.border = '1px solid var(--error)';
        btn.style.color = 'var(--error)';
      } else if (state === 'loading') {
        btn.textContent = 'モデル読み込み中...';
        btn.disabled = true;
      } else {
        btn.textContent = '顔認識を起動';
        btn.disabled = false;
        btn.style.background = 'rgba(255, 255, 255, 0.08)';
        btn.style.border = '1px solid rgba(255, 255, 255, 0.1)';
        btn.style.color = 'var(--text-main)';
      }
    }
  }

  function updateFaceOverlayText(text) {
    const el = $('faceOverlayText');
    if (el) el.textContent = text;
  }

  async function initFaceDetector() {
    if (faceDetector) return faceDetector;
    
    updateFaceStatus('loading');
    updateFaceOverlayText('AIモデルをロード中...');
    
    try {
      visionModule = await import("https://cdn.jsdelivr.net/npm/@mediapipe/tasks-vision@0.10.0");
      const { FaceDetector, FilesetResolver } = visionModule;
      
      const vision = await FilesetResolver.forVisionTasks(
        "https://cdn.jsdelivr.net/npm/@mediapipe/tasks-vision@0.10.0/wasm"
      );
      
      faceDetector = await FaceDetector.createFromOptions(vision, {
        baseOptions: {
          modelAssetPath: "https://storage.googleapis.com/mediapipe-models/face_detector/blaze_face_short_range/float16/1/blaze_face_short_range.tflite",
          delegate: "GPU"
        },
        runningMode: "IMAGE"
      });
      
      updateFaceStatus('active');
      return faceDetector;
    } catch (err) {
      updateFaceStatus('error');
      updateFaceOverlayText('初期化エラー: ' + err.message);
      log('MediaPipe Face Detector初期化失敗: ' + err.message, 'ng');
      throw err;
    }
  }

  async function startCamera() {
    const video = $('faceVideo');
    if (!video) return;
    
    try {
      cameraStream = await navigator.mediaDevices.getUserMedia({
        video: {
          facingMode: 'user', // インカメラ優先
          width: { ideal: 320 },
          height: { ideal: 240 }
        },
        audio: false
      });
      video.srcObject = cameraStream;
      video.onloadedmetadata = () => {
        video.play();
        faceDetectionLoopActive = true;
        requestAnimationFrame(detectionLoop);
      };
    } catch (err) {
      updateFaceStatus('error');
      updateFaceOverlayText('カメラ起動失敗: ' + err.message);
      log('カメラの起動に失敗しました: ' + err.message, 'ng');
    }
  }

  function stopCamera() {
    faceDetectionLoopActive = false;
    if (cameraStream) {
      cameraStream.getTracks().forEach(track => track.stop());
      cameraStream = null;
    }
    const video = $('faceVideo');
    if (video) {
      video.srcObject = null;
    }
    const canvas = $('faceCanvas');
    if (canvas) {
      const ctx = canvas.getContext('2d');
      ctx.clearRect(0, 0, canvas.width, canvas.height);
    }
    isFaceDetectionActive = false;
    updateFaceStatus('off');
    updateFaceOverlayText('カメラ停止中');
  }

  async function toggleFaceDetection() {
    if (isFaceDetectionActive) {
      stopCamera();
    } else {
      try {
        await initFaceDetector();
        isFaceDetectionActive = true;
        await startCamera();
        updateFaceStatus('active');
      } catch (err) {
        console.error(err);
      }
    }
  }

  async function detectionLoop() {
    if (!faceDetectionLoopActive) return;
    
    const video = $('faceVideo');
    const canvas = $('faceCanvas');
    if (!video || !canvas || video.paused || video.ended) {
      requestAnimationFrame(detectionLoop);
      return;
    }
    
    if (canvas.width !== video.videoWidth || canvas.height !== video.videoHeight) {
      canvas.width = video.videoWidth;
      canvas.height = video.videoHeight;
    }
    
    const ctx = canvas.getContext('2d');
    ctx.clearRect(0, 0, canvas.width, canvas.height);
    
    if (faceDetector) {
      try {
        const results = faceDetector.detect(video);
        let maxFaceRatio = 0;
        let targetFace = null;
        
        if (results && results.detections && results.detections.length > 0) {
          for (const detection of results.detections) {
            const { originX, originY, width, height } = detection.boundingBox;
            
            // Draw box in cyan
            ctx.strokeStyle = '#06b6d4';
            ctx.lineWidth = 3;
            ctx.strokeRect(originX, originY, width, height);
            
            // Calculate ratio of face width relative to video width
            const ratio = (width / video.videoWidth) * 100;
            if (ratio > maxFaceRatio) {
              maxFaceRatio = ratio;
              targetFace = { originX, originY, width, height, ratio };
            }
          }
        }
        
        const threshold = parseInt($('faceSizeThreshold').value, 10);
        
        if (targetFace) {
          const isCloseEnough = maxFaceRatio >= threshold;
          
          // Draw label in success (green) or accent (magenta)
          ctx.fillStyle = isCloseEnough ? '#10b981' : '#ec4899';
          ctx.font = 'bold 14px sans-serif';
          ctx.fillText(
            `Face: ${maxFaceRatio.toFixed(1)}% (Threshold: ${threshold}%)`, 
            targetFace.originX, 
            targetFace.originY - 8
          );
          
          if (isCloseEnough) {
            ctx.strokeStyle = '#10b981';
            ctx.lineWidth = 5;
            ctx.strokeRect(targetFace.originX, targetFace.originY, targetFace.width, targetFace.height);
            
            triggerSpeechRecognitionFromFace(maxFaceRatio);
          }
          
          updateFaceOverlayText(`顔認識: ${maxFaceRatio.toFixed(1)}% / しきい値: ${threshold}%`);
        } else {
          updateFaceOverlayText('顔を探しています...');
        }
      } catch (err) {
        console.error(err);
      }
    }
    
    requestAnimationFrame(detectionLoop);
  }

  function triggerSpeechRecognitionFromFace(ratio) {
    if (!isConnected) {
      updateFaceOverlayText(`⚠️ デバイス未接続のため起動不可 (${ratio.toFixed(1)}%)`);
      return;
    }
    
    if (isSpeechActive || isMutedForSpeaking) {
      return;
    }
    
    const now = Date.now();
    if (now - lastFaceTriggerTime < 5000) { // Cooldown of 5 seconds to avoid repeated trigger during prompt handling
      return;
    }
    
    lastFaceTriggerTime = now;
    log(`顔認識オート起動検知: 顔の大きさ ${ratio.toFixed(1)}% >= しきい値 ${$('faceSizeThreshold').value}%`, 'ok');
    
    startSpeechRecognition();
  }

  // ===== 初期化 =====
  function init() {
    // Bluetooth イベント登録
    $('btnConnect').addEventListener('click', connect);
    $('btnDisconnect').addEventListener('click', disconnect);
    
    // ボリュームスライダー
    $('voiceVolume').addEventListener('input', (e) => {
      $('volLabel').textContent = e.target.value;
    });

    // 音声認識トグル
    $('btnToggleSpeech').addEventListener('click', () => {
      if (isSpeechActive) {
        stopSpeechRecognition();
      } else {
        if (!isConnected) {
          alert('先にBLEデバイスに接続してください。');
          return;
        }
        startSpeechRecognition();
      }
    });

    // 赤外線学習 (オプショナル)
    $('btnIrRxStart').addEventListener('click', irRxStart);
    $('btnIrRxStop').addEventListener('click', irRxStop);
    $('btnIrSave').addEventListener('click', saveIrPattern);

    // アコーディオン開閉
    $('toggleCfg').addEventListener('click', () => {
      toggleAccordion($('cfgPanel'), $('cfgCaret'));
    });
    $('toggleAddForm').addEventListener('click', () => {
      toggleAccordion($('addFormPanel'), $('addFormCaret'));
    });
    $('toggleMapping').addEventListener('click', () => {
      toggleAccordion($('mappingPanel'), $('mappingCaret'));
    });
    $('toggleLog').addEventListener('click', () => {
      toggleAccordion($('systemLogPanel'), $('logCaret'));
    });

    // 顔認識アコーディオン開閉
    $('toggleFaceAutoStart').addEventListener('click', () => {
      const panel = $('faceAutoStartPanel');
      const isCurrentlyExpanded = panel.classList.contains('expanded');
      toggleAccordion(panel, $('faceAutoStartCaret'));
      
      // 閉じた場合はプライバシーと電池節約のためにカメラを停止する
      if (isCurrentlyExpanded && isFaceDetectionActive) {
        stopCamera();
        log('顔認識パネルが閉じられたため、カメラを停止しました');
      }
    });

    // 顔認識起動トグルボタン
    $('btnToggleFaceDetection').addEventListener('click', toggleFaceDetection);

    // しきい値スライダー
    $('faceSizeThreshold').addEventListener('input', (e) => {
      $('thresholdLabel').textContent = e.target.value + '%';
    });

    // ログクリア
    $('btnClearLog').addEventListener('click', () => {
      $('log').innerHTML = '';
    });

    // 対話履歴をクリア
    const btnClearChat = $('btnClearChat');
    if (btnClearChat) {
      btnClearChat.addEventListener('click', () => {
        const feed = $('chatFeed');
        if (feed) {
          feed.innerHTML = '<div class="chat-msg system">対話履歴をクリアしました。</div>';
          log('対話履歴をクリアしました');
        }
      });
    }

    // マッピング登録
    $('btnAddMapping').addEventListener('click', addMapping);
    $('btnCancelEdit').addEventListener('click', cancelEditMapping);

    // バックアップ・移行 (JSON エクスポート/インポート)
    $('btnIrExport').addEventListener('click', exportIrBackup);
    $('btnIrImport').addEventListener('click', triggerIrImport);
    $('irImportFile').addEventListener('change', handleIrImport);

    // 漢字読み仮名自動入力補助
    $('newResponse').addEventListener('blur', (e) => {
      const responseVal = e.target.value.trim();
      const yomiInput = $('newResponseYomi');
      if (responseVal && !yomiInput.value.trim()) {
        yomiInput.value = convertToYomi(responseVal);
      }
    });

    // データロード
    loadConfig();
    loadMappings();
    refreshIrSelects();
    initSpeechRecognition();
    populateSettingsGpioSelects();

    // ポート設定ダイアログ制御
    $('btnOpenSettings').addEventListener('click', () => {
      populateSettingsGpioSelects();
      $('settingsModal').classList.add('show');
    });

    $('btnCancelSettings').addEventListener('click', () => {
      $('settingsModal').classList.remove('show');
    });

    $('btnSaveSettings').addEventListener('click', () => {
      const txVal = $('settingsIrTxPin').value;
      const keyVal = $('settingsGeminiKey').value.trim();
      const promptVal = $('settingsSystemPrompt').value.trim();
      
      config.irTxPin = txVal === '' ? null : parseInt(txVal, 10);
      config.geminiKey = keyVal === '' ? null : keyVal;
      config.systemPrompt = promptVal === '' ? DEFAULT_SYSTEM_PROMPT : promptVal;
      
      saveConfig();
      $('settingsModal').classList.remove('show');
      log(`設定を保存しました: IR TX=${config.irTxPin !== null ? 'G' + config.irTxPin : 'デフォルト'}, AI=${config.geminiKey ? '有効' : '無効'}`, 'ok');
    });

    // モーダル外側クリックで閉じる
    $('settingsModal').addEventListener('click', (e) => {
      if (e.target === $('settingsModal')) {
        $('settingsModal').classList.remove('show');
      }
    });

    // Chrome特権URLクリック時の自動コピー＆トースト通知
    document.querySelectorAll('.chrome-link').forEach(link => {
      link.addEventListener('click', (e) => {
        e.preventDefault();
        const url = link.getAttribute('data-url');
        if (url) {
          navigator.clipboard.writeText(url).then(() => {
            const toast = $('copyToast');
            if (toast) {
              toast.style.display = 'block';
              // 4秒後に自動消去
              setTimeout(() => {
                toast.style.display = 'none';
              }, 4000);
            }
          }).catch(err => {
            console.error('URLコピー失敗:', err);
          });
        }
      });
    });

    log('システム準備完了。Android Chrome または PC Chrome にて BLE 接続を開始してください。');
  }

  return { init };
})();

if (document.readyState === 'loading') {
  document.addEventListener('DOMContentLoaded', VoiceControl.init);
} else {
  VoiceControl.init();
}
