'use strict';
// notif Web BLE Control — control.js
//
// notif v10 ファーム (atomlite / atoms3-ir / atomlite-voice / atoms3-voice) の BLE GATT に Web Bluetooth API で接続し、
// CFG caps に応じて UI タブを動的に有効化、 各 char (CMD/STS/CFG/IR_RX) で
// wire コマンド送受信する。
//
// wire 仕様の一次情報源:
//   - v10/src/atom-fw/include/protocol.h (CommandType / ErrorCode / Packet 構造)
//   - v10/src/atom-fw/include/device_config.h (UUID / DEVICE_GPIO_ALLOWED)
//   - v10/src/atom-fw/src/ble_handler.cpp (case 分岐、 STS/CFG/IR_RX char 動作)

const NotifControl = (() => {
  // ===== BLE UUID (両機種共通、 device_config.h) =====
  const SERVICE_UUID    = '12345678-1234-5678-1234-56789abcdef0';
  const CMD_CHAR_UUID   = '12345678-1234-5678-1234-56789abcdef1';
  const STS_CHAR_UUID   = '12345678-1234-5678-1234-56789abcdef2';
  const CFG_CHAR_UUID   = '12345678-1234-5678-1234-56789abcdef3';
  const IR_RX_CHAR_UUID = '12345678-1234-5678-1234-56789abcdef4';

  // ===== CommandType opcode (protocol.h) =====
  // CMD_TEXT       : payload [x:u8][y:u8][size:u8][r:u8][g:u8][b:u8][len:u8][text...]
  // CMD_GPIO       : payload [pin:u8][op:u8][val_lo:u8][val_hi:u8] (val は PULSE 時 LE u16 ms)
  // CMD_IR_SEND    : payload [proto_id:u8][repeat:u8][freq:u8][len_lo:u16 LE][data...][opt_pin?]
  // CMD_IR_RX_START: payload なし
  // CMD_IR_RX_STOP : payload なし
  // CMD_RGB_LED    : payload [index:u8][r:u8][g:u8][b:u8]
  // CMD_STEPPER_*  : 0x50 ROTATE [angle:f32 LE][speed:u8] / 0x51 SET_HOME (空) /
  //                  0x52 GO_HOME [speed:u8] / 0x53 RESET (空) /
  //                  0x54 SET_PINS [p1:u8][p2:u8][p3:u8][p4:u8]
  const CMD_TEXT             = 0x02;
  const CMD_GPIO             = 0x30;
  const CMD_IR_SEND          = 0x40;
  const CMD_IR_RX_START      = 0x41;
  const CMD_IR_RX_STOP       = 0x42;
  const CMD_IR_RX_DATA_EVENT = 0x43; // IR_RX char notify 先頭 byte
  const CMD_RGB_LED          = 0x44;
  const CMD_STEPPER_ROTATE   = 0x50;
  const CMD_STEPPER_SET_HOME = 0x51;
  const CMD_STEPPER_GO_HOME  = 0x52;
  const CMD_STEPPER_RESET    = 0x53;
  const CMD_STEPPER_SET_PINS = 0x54;
  // voice fw 段階 2、 payload = utf8、 MTU 244 byte 上限
  const CMD_VOICE            = 0x60;
  const VOICE_MTU_MAX        = 244;
  // voice 音量調整 (sticky)、 payload = [volume:u8] (0-100)
  const CMD_VOICE_VOLUME     = 0x61;

  // ===== ErrorCode 名前マップ (protocol.h L78-87) =====
  const ERR_NAMES = {
    0x00: 'SUCCESS',
    0x01: 'INVALID_COMMAND',
    0x02: 'INVALID_PAYLOAD',
    0x03: 'OUT_OF_BOUNDS',
    0x04: 'MEMORY_FULL',
    0x05: 'UNSUPPORTED_FMT',
    0x06: 'UNSUPPORTED_CAP',
    0x07: 'PIN_BUSY'
  };

  // ===== 機種別有効 GPIO pin (device_config.h DEVICE_GPIO_ALLOWED) =====
  const DEVICE_GPIO = {
    atomlite: [12, 19, 21, 22, 23, 25, 26, 32, 33, 39],
    atoms3ir: [1, 2, 5, 6, 7, 8, 38, 39]
  };

  // ===== 状態 =====
  let device = null;
  let server = null;
  let chars = { cmd: null, sts: null, cfg: null, irRx: null };
  let cfg = null; // { type, fw, caps: [] }
  let userInitiatedDisconnect = false;
  let reconnectAttempts = 0;
  const RECONNECT_MAX = 5;
  const RECONNECT_INTERVAL_MS = 1000;
  let lastIrPattern = null; // {protocol, bits, repeat, value_hex, raw_timings, freq_khz}

  // ===== ユーティリティ =====
  const $ = (id) => document.getElementById(id);

  function log(msg, cls) {
    const el = $('log');
    const ts = new Date().toLocaleTimeString();
    const line = document.createElement('div');
    if (cls) line.className = cls;
    line.textContent = `[${ts}] ${msg}`;
    el.insertBefore(line, el.firstChild);
  }

  function hex(bytes) {
    return Array.from(bytes, (b) => b.toString(16).padStart(2, '0')).join(' ');
  }

  function hexToRgb(h) {
    const m = h.match(/^#([0-9a-f]{2})([0-9a-f]{2})([0-9a-f]{2})$/i);
    return m ? [parseInt(m[1], 16), parseInt(m[2], 16), parseInt(m[3], 16)] : [0, 0, 0];
  }

  function parseHexBytes(txt) {
    const parts = txt.trim().split(/[\s,]+/).filter(Boolean);
    const bytes = parts.map((p) => parseInt(p, 16));
    if (bytes.some(isNaN)) throw new Error('hex parse 失敗');
    return new Uint8Array(bytes);
  }

  // ===== パケット組立 / 送信 (protocol.h L108-122) =====
  // [opcode:u8][length:u16 LE][payload...]
  function buildPacket(opcode, payload) {
    const pl = payload instanceof Uint8Array ? payload : new Uint8Array(payload);
    const pkt = new Uint8Array(3 + pl.length);
    pkt[0] = opcode;
    pkt[1] = pl.length & 0xff;
    pkt[2] = (pl.length >> 8) & 0xff;
    pkt.set(pl, 3);
    return pkt;
  }

  // sendCommand: CMD char へ writeValueWithResponse (STS notify で結果確認)
  async function sendCommand(opcode, payload, label) {
    if (!chars.cmd) {
      log(`CMD char 未取得、 送信スキップ (${label})`, 'ng');
      return;
    }
    const pkt = buildPacket(opcode, payload);
    try {
      log(`send ${label}: ${hex(pkt)}`);
      await chars.cmd.writeValueWithResponse(pkt);
    } catch (e) {
      log(`send NG (${label}): ${e.message}`, 'ng');
    }
  }

  // ===== UI 状態 =====
  function setConnected(connected) {
    $('btnConnect').disabled = connected;
    $('btnDisconnect').disabled = !connected;
    if (!connected) {
      $('cfgView').textContent = '未接続';
      document.querySelectorAll('fieldset[data-cap]').forEach((el) => {
        el.disabled = true;
      });
    }
  }

  // CFG caps に基づいて fieldset[data-cap] を enable/disable する
  function applyCapsToUi() {
    if (!cfg || !Array.isArray(cfg.caps)) return;
    document.querySelectorAll('fieldset[data-cap]').forEach((el) => {
      const cap = el.dataset.cap;
      el.disabled = !cfg.caps.includes(cap);
    });
    populateGpioPinSelects();
  }

  // CFG.type に基づいて GPIO pin select の option を生成
  // (DEVICE_GPIO_ALLOWED と整合)
  function populateGpioPinSelects() {
    if (!cfg || !cfg.type) return;
    const pins = DEVICE_GPIO[cfg.type] || [];
    const fill = (sel, prepend) => {
      if (!sel) return;
      const current = sel.value;
      sel.innerHTML = '';
      (prepend || []).forEach((opt) => {
        const o = document.createElement('option');
        o.value = opt.value;
        o.textContent = opt.label;
        sel.appendChild(o);
      });
      pins.forEach((p) => {
        const o = document.createElement('option');
        o.value = String(p);
        o.textContent = `G${p}`;
        sel.appendChild(o);
      });
      // 直前値を復元 (range 内なら)
      if (current && Array.from(sel.options).some((o) => o.value === current)) {
        sel.value = current;
      }
    };
    fill($('gpioPin'));
    fill($('irOptPin'), [{ value: '', label: '(default)' }]);
    fill($('irReplayPin'), [{ value: '', label: '(default)' }]);
  }

  // ===== 機能別ハンドラ =====

  // テキスト (CMD_TEXT 0x02)
  // payload: [x:u8][y:u8][size:u8][r:u8][g:u8][b:u8][len:u8][text...]
  async function sendText() {
    const x = parseInt($('textX').value, 10) & 0xff;
    const y = parseInt($('textY').value, 10) & 0xff;
    const size = parseInt($('textSize').value, 10) & 0xff;
    const [r, g, b] = hexToRgb($('textColor').value);
    const textBytes = new TextEncoder().encode($('textBody').value);
    if (textBytes.length > 255) {
      log('text 長すぎ (>255 bytes)', 'ng');
      return;
    }
    const pl = new Uint8Array(7 + textBytes.length);
    pl[0] = x; pl[1] = y; pl[2] = size;
    pl[3] = r; pl[4] = g; pl[5] = b;
    pl[6] = textBytes.length;
    pl.set(textBytes, 7);
    await sendCommand(CMD_TEXT, pl, `TEXT(${x},${y},sz${size},"${$('textBody').value}")`);
  }

  // GPIO (CMD_GPIO 0x30)
  // payload: [pin:u8][op:u8][val_lo:u8][val_hi:u8]
  async function sendGpio() {
    const pin = parseInt($('gpioPin').value, 10) & 0xff;
    const op  = parseInt($('gpioOp').value, 10) & 0xff;
    const val = parseInt($('gpioVal').value, 10) & 0xffff;
    const pl = new Uint8Array([pin, op, val & 0xff, (val >> 8) & 0xff]);
    await sendCommand(CMD_GPIO, pl, `GPIO(pin=${pin},op=${op},val=${val})`);
  }

  // IR Send (CMD_IR_SEND 0x40)
  // payload: [proto_id:u8][repeat:u8][freq:u8][len:u16 LE][data...][opt_pin?]
  async function sendIrSend() {
    const proto = parseInt($('irProto').value, 10) & 0xff;
    const repeat = parseInt($('irRepeat').value, 10) & 0xff;
    const freq = parseInt($('irFreq').value, 10) & 0xff;
    let data;
    try {
      data = parseHexBytes($('irData').value);
    } catch (e) {
      log(`IR data hex parse NG: ${e.message}`, 'ng');
      return;
    }
    const optPinTxt = $('irOptPin').value;
    const optPin = optPinTxt === '' ? null : (parseInt(optPinTxt, 10) & 0xff);
    const headLen = 5;
    const plLen = headLen + data.length + (optPin !== null ? 1 : 0);
    const pl = new Uint8Array(plLen);
    pl[0] = proto;
    pl[1] = repeat;
    pl[2] = freq;
    pl[3] = data.length & 0xff;
    pl[4] = (data.length >> 8) & 0xff;
    pl.set(data, headLen);
    if (optPin !== null) pl[plLen - 1] = optPin;
    await sendCommand(CMD_IR_SEND, pl, `IR(proto=${proto},rep=${repeat},f=${freq}kHz,len=${data.length}${optPin !== null ? `,pin=${optPin}` : ''})`);
  }

  // RGB LED (CMD_RGB_LED 0x44)
  // payload: [index:u8][r:u8][g:u8][b:u8]
  async function sendRgbLed(rOverride, gOverride, bOverride) {
    const index = parseInt($('rgbIndex').value, 10) & 0xff;
    let r, g, b;
    if (rOverride !== undefined) {
      r = rOverride; g = gOverride; b = bOverride;
    } else {
      [r, g, b] = hexToRgb($('rgbColor').value);
    }
    await sendCommand(CMD_RGB_LED, new Uint8Array([index, r, g, b]), `RGB(idx=${index},${r},${g},${b})`);
  }

  // Stepper (CMD_STEPPER_* 0x50-0x54)
  async function sendStepperRotate() {
    const angle = parseFloat($('stepAngle').value);
    const speed = parseInt($('stepSpeed').value, 10) & 0xff;
    const buf = new ArrayBuffer(5);
    const dv = new DataView(buf);
    dv.setFloat32(0, angle, true); // LE
    dv.setUint8(4, speed);
    await sendCommand(CMD_STEPPER_ROTATE, new Uint8Array(buf), `STEP_ROTATE(${angle}°,sp=${speed})`);
  }
  async function sendStepperSetHome() {
    await sendCommand(CMD_STEPPER_SET_HOME, new Uint8Array(0), 'STEP_SET_HOME');
  }
  async function sendStepperGoHome() {
    const speed = parseInt($('stepSpeed').value, 10) & 0xff;
    await sendCommand(CMD_STEPPER_GO_HOME, new Uint8Array([speed]), `STEP_GO_HOME(sp=${speed})`);
  }
  async function sendStepperReset() {
    await sendCommand(CMD_STEPPER_RESET, new Uint8Array(0), 'STEP_RESET');
  }
  async function sendStepperSetPins() {
    const p1 = parseInt($('stepP1').value, 10) & 0xff;
    const p2 = parseInt($('stepP2').value, 10) & 0xff;
    const p3 = parseInt($('stepP3').value, 10) & 0xff;
    const p4 = parseInt($('stepP4').value, 10) & 0xff;
    await sendCommand(CMD_STEPPER_SET_PINS, new Uint8Array([p1, p2, p3, p4]), `STEP_SET_PINS(${p1},${p2},${p3},${p4})`);
  }

  // Voice テキスト再生 (CMD_VOICE 0x60)
  // payload: utf8 bytes、 MTU 244 byte 上限 (= 247 - opcode 1 - length 2)
  async function sendVoice() {
    const text = $('voiceText').value || '';
    if (text.length === 0) {
      log('voice text 空、 送信スキップ', 'ng');
      return;
    }
    const bytes = new TextEncoder().encode(text);
    if (bytes.length > VOICE_MTU_MAX) {
      log(`voice text MTU 超過 (${bytes.length} > ${VOICE_MTU_MAX} byte)`, 'ng');
      return;
    }
    // 音量を先に sticky 設定してから再生する
    await sendVoiceVolume();
    await sendCommand(CMD_VOICE, bytes, `VOICE("${text}", ${bytes.length}B)`);
  }

  // Voice 音量調整 (CMD_VOICE_VOLUME 0x61)
  // payload: [volume:u8] (0-100、 範囲外は clamp)
  async function sendVoiceVolume() {
    let vol = parseInt($('voiceVolume').value, 10);
    if (Number.isNaN(vol)) vol = 70;
    if (vol < 0) vol = 0;
    if (vol > 100) vol = 100;
    await sendCommand(CMD_VOICE_VOLUME, new Uint8Array([vol]), `VOICE_VOLUME(${vol})`);
  }

  // ===== IR Recv 学習 =====
  // IR_RX char notify payload (ir_handler.cpp):
  // [type=0x43][proto_id:u8][bits:u8][repeat:u8][data_len:u16 LE][data...:data_len]
  //  [raw_count:u16 LE][raw_timings:u16 LE...:raw_count]
  const IR_PROTO_NAMES = { 1: 'NEC', 2: 'Panasonic', 3: 'RAW', 4: 'Sony', 5: 'RC5' };

  async function irRxStart() {
    if (!chars.irRx) {
      log('IR_RX char 未取得', 'ng');
      return;
    }
    try {
      if (chars.irRx.properties.notify) {
        await chars.irRx.startNotifications();
        chars.irRx.addEventListener('characteristicvaluechanged', onIrRxData);
      }
      await sendCommand(CMD_IR_RX_START, new Uint8Array(0), 'IR_RX_START');
    } catch (e) {
      log(`IR_RX start NG: ${e.message}`, 'ng');
    }
  }

  async function irRxStop() {
    try {
      await sendCommand(CMD_IR_RX_STOP, new Uint8Array(0), 'IR_RX_STOP');
      if (chars.irRx && chars.irRx.properties.notify) {
        await chars.irRx.stopNotifications();
      }
    } catch (e) {
      log(`IR_RX stop NG: ${e.message}`, 'ng');
    }
  }

  function onIrRxData(ev) {
    const dv = ev.target.value;
    if (dv.byteLength < 7) {
      log(`IR_RX notify 短すぎ (${dv.byteLength} bytes)`, 'ng');
      return;
    }
    const eventType = dv.getUint8(0);
    if (eventType !== CMD_IR_RX_DATA_EVENT) {
      log(`IR_RX event_type 不一致 (0x${eventType.toString(16)})`, 'ng');
      return;
    }
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
    const protoName = IR_PROTO_NAMES[protoId] || `UNKNOWN(0x${protoId.toString(16)})`;
    lastIrPattern = {
      protocol: protoName,
      proto_id: protoId,
      bits,
      repeat,
      value_hex: hex(data),
      raw_timings: rawTimings,
      freq_khz: 38 // 受信時は freq 情報なし、 送信時 NEC/Panasonic 想定で 38kHz 固定
    };
    $('irRxView').textContent = JSON.stringify(lastIrPattern, null, 2);
    log(`IR_RX: ${protoName} bits=${bits} repeat=${repeat} data=[${hex(data)}] raw=${rawCount}個`, 'ok');
  }

  function saveIrPattern() {
    if (!lastIrPattern) {
      log('保存対象の受信パターンなし', 'ng');
      return;
    }
    const name = $('irPatternName').value.trim();
    if (!name) {
      log('name を入力してください', 'ng');
      return;
    }
    const key = `notif_ir_${name}`;
    localStorage.setItem(key, JSON.stringify(lastIrPattern));
    log(`保存: ${key}`, 'ok');
    refreshIrPatterns();
  }

  function refreshIrPatterns() {
    const ul = $('irPatterns');
    ul.innerHTML = '';
    const keys = Object.keys(localStorage).filter((k) => k.startsWith('notif_ir_')).sort();
    if (keys.length === 0) {
      const li = document.createElement('li');
      li.textContent = '(なし)';
      li.className = 'note';
      ul.appendChild(li);
      return;
    }
    keys.forEach((k) => {
      const pattern = JSON.parse(localStorage.getItem(k));
      const li = document.createElement('li');
      const name = k.replace(/^notif_ir_/, '');
      const summary = `${name} [${pattern.protocol} bits=${pattern.bits} data=${pattern.value_hex}]`;
      li.appendChild(document.createTextNode(summary + ' '));
      const btnSend = document.createElement('button');
      btnSend.textContent = '送信';
      btnSend.addEventListener('click', () => {
        const pinTxt = $('irReplayPin').value;
        const optPin = pinTxt === '' ? null : (parseInt(pinTxt, 10) & 0xff);
        sendStoredIrPattern(pattern, name, optPin);
      });
      li.appendChild(btnSend);
      const btnDel = document.createElement('button');
      btnDel.textContent = '削除';
      btnDel.addEventListener('click', () => {
        localStorage.removeItem(k);
        log(`削除: ${k}`, 'ok');
        refreshIrPatterns();
      });
      li.appendChild(btnDel);
      ul.appendChild(li);
    });
  }

  // 登録済パターンを CMD_IR_SEND に変換して送信
  // 方針: raw_timings が記録されていれば必ず RAW (0x03) で送る (decode UNKNOWN な信号
  // = pattern.proto_id=0xff の場合も raw_timings は埋まっているため、 そちらを優先する)。
  // raw_timings が無く value_hex がある場合のみ pattern.proto_id をそのまま使う。
  // (fw 側 ble_handler.cpp は proto_id 0x01-0x05 範囲外を ERR_UNSUPPORTED_FMT で拒否)
  async function sendStoredIrPattern(pattern, name, optPin) {
    const hasRaw = Array.isArray(pattern.raw_timings) && pattern.raw_timings.length > 0;
    let protoId;
    let data;
    if (hasRaw) {
      protoId = 3; // RAW 強制 (UNKNOWN 学習データもここに集約)
      const buf = new ArrayBuffer(pattern.raw_timings.length * 2);
      const dv = new DataView(buf);
      pattern.raw_timings.forEach((t, i) => dv.setUint16(i * 2, t & 0xffff, true));
      data = new Uint8Array(buf);
    } else {
      protoId = pattern.proto_id & 0xff;
      try {
        data = parseHexBytes(pattern.value_hex || '');
      } catch (e) {
        log(`stored pattern data parse NG: ${e.message}`, 'ng');
        return;
      }
      if (data.length === 0) {
        log(`stored pattern ${name}: raw_timings も value_hex も空、 送信スキップ`, 'ng');
        return;
      }
    }
    const freq = pattern.freq_khz || 38;
    const headLen = 5;
    const hasPin = (typeof optPin === 'number') && !isNaN(optPin);
    const plLen = headLen + data.length + (hasPin ? 1 : 0);
    const pl = new Uint8Array(plLen);
    pl[0] = protoId;
    pl[1] = 0; // repeat 0 (再生時は単発)
    pl[2] = freq;
    pl[3] = data.length & 0xff;
    pl[4] = (data.length >> 8) & 0xff;
    pl.set(data, headLen);
    if (hasPin) pl[plLen - 1] = optPin & 0xff;
    const protoLabel = hasRaw ? `RAW(forced from ${pattern.protocol})` : pattern.protocol;
    const pinLabel = hasPin ? `,pin=${optPin}` : '';
    await sendCommand(CMD_IR_SEND, pl, `IR_REPLAY(${name},${protoLabel}${pinLabel})`);
  }

  // ===== 自動再接続 =====
  async function autoReconnect() {
    if (userInitiatedDisconnect) return;
    if (reconnectAttempts >= RECONNECT_MAX) {
      log(`自動再接続あきらめ (${RECONNECT_MAX}回 連続失敗)`, 'ng');
      device = null;
      reconnectAttempts = 0;
      return;
    }
    reconnectAttempts += 1;
    log(`自動再接続 attempt ${reconnectAttempts}/${RECONNECT_MAX} (${RECONNECT_INTERVAL_MS}ms 待機)`);
    await new Promise((r) => setTimeout(r, RECONNECT_INTERVAL_MS));
    if (!device) {
      log('device 参照消失、 再接続中止', 'ng');
      return;
    }
    try {
      await acquireGattAndChars();
      setConnected(true);
      reconnectAttempts = 0;
      log('自動再接続 OK', 'ok');
    } catch (e) {
      log(`自動再接続 attempt ${reconnectAttempts} 失敗: ${e.message}`, 'ng');
      autoReconnect();
    }
  }

  // ===== GATT 接続 =====
  async function connect() {
    if (!navigator.bluetooth) {
      log('Web Bluetooth API が使えません (HTTPS / Chrome 系が必要)', 'ng');
      return;
    }
    try {
      log('requestDevice (service filter) ...');
      device = await navigator.bluetooth.requestDevice({
        filters: [{ services: [SERVICE_UUID] }]
      });
      log(`device 選択: name="${device.name || '(no name)'}" id=${device.id}`, 'ok');
      device.addEventListener('gattserverdisconnected', onDisconnected);

      await acquireGattAndChars();
      setConnected(true);
      userInitiatedDisconnect = false;
      reconnectAttempts = 0;
    } catch (e) {
      log(`接続エラー: ${e.message}`, 'ng');
    }
  }

  async function acquireGattAndChars() {
    log('GATT 接続 ...');
    server = await device.gatt.connect();
    log('GATT connect OK', 'ok');

    const service = await server.getPrimaryService(SERVICE_UUID);
    log('primary service OK', 'ok');

    // 4 chars 取得 (個別に try / catch、 欠落でも続行)
    chars = { cmd: null, sts: null, cfg: null, irRx: null };
    const charSpec = [
      ['cmd',  CMD_CHAR_UUID,   'CMD'],
      ['sts',  STS_CHAR_UUID,   'STS'],
      ['cfg',  CFG_CHAR_UUID,   'CFG'],
      ['irRx', IR_RX_CHAR_UUID, 'IR_RX']
    ];
    for (const [slot, uuid, name] of charSpec) {
      try {
        chars[slot] = await service.getCharacteristic(uuid);
        log(`char ${name} OK`, 'ok');
      } catch (e) {
        log(`char ${name} なし: ${e.message}`);
      }
    }

    // STS notify 購読 (STS は 1 byte ErrorCode を毎コマンド後に notify、 ble_handler.cpp L363)
    if (chars.sts && chars.sts.properties.notify) {
      await chars.sts.startNotifications();
      chars.sts.addEventListener('characteristicvaluechanged', onStsNotify);
      log('STS notify subscribed', 'ok');
    }

    // CFG 読込 + 動的有効化
    await readCfg();
    applyCapsToUi();
  }

  // CFG char を read → JSON parse して cfg state に格納、 UI 反映 (ble_handler.cpp L333)
  // 期待形式: {"type":"atomlite|atoms3ir","fw":"v10.X.Y","caps":[...]}
  async function readCfg() {
    if (!chars.cfg || !chars.cfg.properties.read) {
      log('CFG char 未取得 or read 不可', 'ng');
      cfg = null;
      return;
    }
    try {
      const dv = await chars.cfg.readValue();
      const bytes = new Uint8Array(dv.buffer);
      const txt = new TextDecoder().decode(bytes);
      cfg = JSON.parse(txt);
      log(`CFG: type=${cfg.type} fw=${cfg.fw} caps=[${(cfg.caps || []).join(',')}]`, 'ok');
      $('cfgView').textContent = JSON.stringify(cfg, null, 2);
    } catch (e) {
      log(`CFG read/parse NG: ${e.message}`, 'ng');
      cfg = null;
    }
  }

  // STS notify ハンドラ: 1 byte ErrorCode を ERR_NAMES でラベル化して log
  function onStsNotify(ev) {
    const dv = ev.target.value;
    const bytes = new Uint8Array(dv.buffer);
    if (bytes.length === 0) {
      log('STS notify (0 bytes)');
      return;
    }
    const code = bytes[0];
    const name = ERR_NAMES[code] || `UNKNOWN(0x${code.toString(16)})`;
    log(`STS: ${name} (0x${code.toString(16).padStart(2, '0')})`, code === 0 ? 'ok' : 'ng');
  }

  function onDisconnected() {
    log('gattserverdisconnected event', 'ng');
    setConnected(false);
    if (!userInitiatedDisconnect) {
      autoReconnect();
    }
  }

  async function disconnect() {
    userInitiatedDisconnect = true;
    if (device && device.gatt.connected) {
      device.gatt.disconnect();
      log('手動 disconnect');
    }
    setConnected(false);
  }

  // ===== 初期化 =====
  function init() {
    $('btnConnect').addEventListener('click', connect);
    $('btnDisconnect').addEventListener('click', disconnect);
    $('btnClearLog').addEventListener('click', () => {
      $('log').textContent = '';
    });
    // 機能タブ ハンドラ
    $('btnSendText').addEventListener('click', sendText);
    $('btnSendGpio').addEventListener('click', sendGpio);
    $('btnSendIr').addEventListener('click', sendIrSend);
    $('btnSendRgb').addEventListener('click', () => sendRgbLed());
    $('btnRgbOff').addEventListener('click', () => sendRgbLed(0, 0, 0));
    $('btnStepRotate').addEventListener('click', sendStepperRotate);
    $('btnStepSetHome').addEventListener('click', sendStepperSetHome);
    $('btnStepGoHome').addEventListener('click', sendStepperGoHome);
    $('btnStepReset').addEventListener('click', sendStepperReset);
    $('btnStepSetPins').addEventListener('click', sendStepperSetPins);
    $('btnSendVoice').addEventListener('click', sendVoice);
    $('btnSendVoiceVolume').addEventListener('click', sendVoiceVolume);
    // IR Recv 学習 (stage 3)
    $('btnIrRxStart').addEventListener('click', irRxStart);
    $('btnIrRxStop').addEventListener('click', irRxStop);
    $('btnIrSave').addEventListener('click', saveIrPattern);
    refreshIrPatterns();
    log('ready. 「Scan & Connect」で接続を開始してください');
  }

  return { init };
})();

if (document.readyState === 'loading') {
  document.addEventListener('DOMContentLoaded', NotifControl.init);
} else {
  NotifControl.init();
}
