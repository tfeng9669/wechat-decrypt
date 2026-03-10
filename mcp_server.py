r"""
WeChat MCP Server - query WeChat messages, contacts via Claude

Based on FastMCP (stdio transport), reuses existing decryption.
Runs on Windows Python (needs access to D:\ WeChat databases).
"""

import os, sys, json, time, sqlite3, tempfile, struct, hashlib, atexit, re
import xml.etree.ElementTree as ET
import hmac as hmac_mod
from datetime import datetime
from Crypto.Cipher import AES
from mcp.server.fastmcp import FastMCP
import zstandard as zstd
from decode_image import ImageResolver
from key_utils import get_key_info, key_path_variants, strip_key_metadata

# ============ 加密常量 ============
PAGE_SZ = 4096
KEY_SZ = 32
SALT_SZ = 16
RESERVE_SZ = 80
SQLITE_HDR = b'SQLite format 3\x00'
WAL_HEADER_SZ = 32
WAL_FRAME_HEADER_SZ = 24

# ============ 配置加载 ============
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
CONFIG_FILE = os.path.join(SCRIPT_DIR, "config.json")

with open(CONFIG_FILE) as f:
    _cfg = json.load(f)
for _key in ("keys_file", "decrypted_dir"):
    if _key in _cfg and not os.path.isabs(_cfg[_key]):
        _cfg[_key] = os.path.join(SCRIPT_DIR, _cfg[_key])

DB_DIR = _cfg["db_dir"]
KEYS_FILE = _cfg["keys_file"]
DECRYPTED_DIR = _cfg["decrypted_dir"]

# 图片相关路径
_db_dir = _cfg["db_dir"]
if os.path.basename(_db_dir) == "db_storage":
    WECHAT_BASE_DIR = os.path.dirname(_db_dir)
else:
    WECHAT_BASE_DIR = _db_dir

DECODED_IMAGE_DIR = _cfg.get("decoded_image_dir")
if not DECODED_IMAGE_DIR:
    DECODED_IMAGE_DIR = os.path.join(SCRIPT_DIR, "decoded_images")
elif not os.path.isabs(DECODED_IMAGE_DIR):
    DECODED_IMAGE_DIR = os.path.join(SCRIPT_DIR, DECODED_IMAGE_DIR)

with open(KEYS_FILE) as f:
    ALL_KEYS = strip_key_metadata(json.load(f))

# ============ 解密函数 ============

def decrypt_page(enc_key, page_data, pgno):
    iv = page_data[PAGE_SZ - RESERVE_SZ : PAGE_SZ - RESERVE_SZ + 16]
    if pgno == 1:
        encrypted = page_data[SALT_SZ : PAGE_SZ - RESERVE_SZ]
        cipher = AES.new(enc_key, AES.MODE_CBC, iv)
        decrypted = cipher.decrypt(encrypted)
        return bytes(bytearray(SQLITE_HDR + decrypted + b'\x00' * RESERVE_SZ))
    else:
        encrypted = page_data[: PAGE_SZ - RESERVE_SZ]
        cipher = AES.new(enc_key, AES.MODE_CBC, iv)
        decrypted = cipher.decrypt(encrypted)
        return decrypted + b'\x00' * RESERVE_SZ


def full_decrypt(db_path, out_path, enc_key):
    file_size = os.path.getsize(db_path)
    total_pages = file_size // PAGE_SZ
    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    with open(db_path, 'rb') as fin, open(out_path, 'wb') as fout:
        for pgno in range(1, total_pages + 1):
            page = fin.read(PAGE_SZ)
            if len(page) < PAGE_SZ:
                if len(page) > 0:
                    page = page + b'\x00' * (PAGE_SZ - len(page))
                else:
                    break
            fout.write(decrypt_page(enc_key, page, pgno))
    return total_pages


def decrypt_wal(wal_path, out_path, enc_key):
    if not os.path.exists(wal_path):
        return 0
    wal_size = os.path.getsize(wal_path)
    if wal_size <= WAL_HEADER_SZ:
        return 0
    frame_size = WAL_FRAME_HEADER_SZ + PAGE_SZ
    patched = 0
    with open(wal_path, 'rb') as wf, open(out_path, 'r+b') as df:
        wal_hdr = wf.read(WAL_HEADER_SZ)
        wal_salt1 = struct.unpack('>I', wal_hdr[16:20])[0]
        wal_salt2 = struct.unpack('>I', wal_hdr[20:24])[0]
        while wf.tell() + frame_size <= wal_size:
            fh = wf.read(WAL_FRAME_HEADER_SZ)
            if len(fh) < WAL_FRAME_HEADER_SZ:
                break
            pgno = struct.unpack('>I', fh[0:4])[0]
            frame_salt1 = struct.unpack('>I', fh[8:12])[0]
            frame_salt2 = struct.unpack('>I', fh[12:16])[0]
            ep = wf.read(PAGE_SZ)
            if len(ep) < PAGE_SZ:
                break
            if pgno == 0 or pgno > 1000000:
                continue
            if frame_salt1 != wal_salt1 or frame_salt2 != wal_salt2:
                continue
            dec = decrypt_page(enc_key, ep, pgno)
            df.seek((pgno - 1) * PAGE_SZ)
            df.write(dec)
            patched += 1
    return patched


# ============ DB 缓存 ============

class DBCache:
    """缓存解密后的 DB，通过 mtime 检测变化。使用固定文件名，重启后可复用。"""

    CACHE_DIR = os.path.join(tempfile.gettempdir(), "wechat_mcp_cache")
    MTIME_FILE = os.path.join(tempfile.gettempdir(), "wechat_mcp_cache", "_mtimes.json")

    def __init__(self):
        self._cache = {}  # rel_key -> (db_mtime, wal_mtime, tmp_path)
        os.makedirs(self.CACHE_DIR, exist_ok=True)
        self._load_persistent_cache()

    def _cache_path(self, rel_key):
        """rel_key -> 固定的缓存文件路径"""
        h = hashlib.md5(rel_key.encode()).hexdigest()[:12]
        return os.path.join(self.CACHE_DIR, f"{h}.db")

    def _load_persistent_cache(self):
        """启动时从磁盘恢复缓存映射，验证 mtime 后复用"""
        if not os.path.exists(self.MTIME_FILE):
            return
        try:
            with open(self.MTIME_FILE) as f:
                saved = json.load(f)
        except (json.JSONDecodeError, OSError):
            return
        reused = 0
        for rel_key, info in saved.items():
            tmp_path = info["path"]
            if not os.path.exists(tmp_path):
                continue
            rel_path = rel_key.replace('\\', os.sep)
            db_path = os.path.join(DB_DIR, rel_path)
            wal_path = db_path + "-wal"
            try:
                db_mtime = os.path.getmtime(db_path)
                wal_mtime = os.path.getmtime(wal_path) if os.path.exists(wal_path) else 0
            except OSError:
                continue
            if db_mtime == info["db_mt"] and wal_mtime == info["wal_mt"]:
                self._cache[rel_key] = (db_mtime, wal_mtime, tmp_path)
                reused += 1
        if reused:
            print(f"[DBCache] reused {reused} cached decrypted DBs from previous run", flush=True)

    def _save_persistent_cache(self):
        """持久化缓存映射到磁盘"""
        data = {}
        for rel_key, (db_mt, wal_mt, path) in self._cache.items():
            data[rel_key] = {"db_mt": db_mt, "wal_mt": wal_mt, "path": path}
        try:
            with open(self.MTIME_FILE, 'w') as f:
                json.dump(data, f)
        except OSError:
            pass

    def get(self, rel_key):
        key_info = get_key_info(ALL_KEYS, rel_key)
        if not key_info:
            return None
        rel_path = rel_key.replace('\\', '/').replace('/', os.sep)
        db_path = os.path.join(DB_DIR, rel_path)
        wal_path = db_path + "-wal"
        if not os.path.exists(db_path):
            return None

        try:
            db_mtime = os.path.getmtime(db_path)
            wal_mtime = os.path.getmtime(wal_path) if os.path.exists(wal_path) else 0
        except OSError:
            return None

        if rel_key in self._cache:
            c_db_mt, c_wal_mt, c_path = self._cache[rel_key]
            if c_db_mt == db_mtime and c_wal_mt == wal_mtime and os.path.exists(c_path):
                return c_path

        tmp_path = self._cache_path(rel_key)
        enc_key = bytes.fromhex(key_info["enc_key"])
        full_decrypt(db_path, tmp_path, enc_key)
        if os.path.exists(wal_path):
            decrypt_wal(wal_path, tmp_path, enc_key)
        self._cache[rel_key] = (db_mtime, wal_mtime, tmp_path)
        self._save_persistent_cache()
        return tmp_path

    def cleanup(self):
        """正常退出时保存缓存映射（不删文件，下次启动可复用）"""
        self._save_persistent_cache()


_cache = DBCache()
atexit.register(_cache.cleanup)


# ============ 联系人缓存 ============

_contact_names = None  # {username: display_name}
_contact_full = None   # [{username, nick_name, remark}]
_self_username = None
_XML_UNSAFE_RE = re.compile(r'<!DOCTYPE|<!ENTITY', re.IGNORECASE)
_XML_PARSE_MAX_LEN = 20000


def _load_contacts_from(db_path):
    names = {}
    full = []
    conn = sqlite3.connect(db_path)
    try:
        for r in conn.execute("SELECT username, nick_name, remark FROM contact").fetchall():
            uname, nick, remark = r
            display = remark if remark else nick if nick else uname
            names[uname] = display
            full.append({'username': uname, 'nick_name': nick or '', 'remark': remark or ''})
    finally:
        conn.close()
    return names, full


def get_contact_names():
    global _contact_names, _contact_full
    if _contact_names is not None:
        return _contact_names

    # 优先用已解密的 contact.db
    pre_decrypted = os.path.join(DECRYPTED_DIR, "contact", "contact.db")
    if os.path.exists(pre_decrypted):
        try:
            _contact_names, _contact_full = _load_contacts_from(pre_decrypted)
            return _contact_names
        except Exception:
            pass

    # 实时解密
    path = _cache.get(os.path.join("contact", "contact.db"))
    if path:
        try:
            _contact_names, _contact_full = _load_contacts_from(path)
            return _contact_names
        except Exception:
            pass

    return {}


def get_contact_full():
    global _contact_full
    if _contact_full is None:
        get_contact_names()
    return _contact_full or []


# ============ 辅助函数 ============

def format_msg_type(t):
    base_type = t % 4294967296 if t > 4294967296 else t
    return {
        1: '文本', 3: '图片', 34: '语音', 42: '名片',
        43: '视频', 47: '表情', 48: '位置', 49: '链接/文件',
        50: '通话', 10000: '系统', 10002: '撤回',
    }.get(base_type, f'type={t}')


def resolve_username(chat_name):
    """将聊天名/备注名/wxid 解析为 username"""
    names = get_contact_names()

    # 直接是 username
    if chat_name in names or chat_name.startswith('wxid_') or '@chatroom' in chat_name:
        return chat_name

    # 模糊匹配(优先精确包含)
    chat_lower = chat_name.lower()
    for uname, display in names.items():
        if chat_lower == display.lower():
            return uname
    for uname, display in names.items():
        if chat_lower in display.lower():
            return uname

    return None


_zstd_dctx = zstd.ZstdDecompressor()


def _decompress_content(content, ct):
    """解压 zstd 压缩的消息内容"""
    if ct and ct == 4 and isinstance(content, bytes):
        try:
            return _zstd_dctx.decompress(content).decode('utf-8', errors='replace')
        except Exception:
            return None
    if isinstance(content, bytes):
        try:
            return content.decode('utf-8', errors='replace')
        except Exception:
            return None
    return content


def _parse_message_content(content, local_type, is_group):
    """解析消息内容，返回 (sender_id, text)"""
    if content is None:
        return '', ''
    if isinstance(content, bytes):
        return '', '(二进制内容)'

    sender = ''
    text = content
    if is_group and ':\n' in content:
        sender, text = content.split(':\n', 1)

    return sender, text


def _parse_xml_safe(content):
    """安全解析 XML，防止 XXE 注入和超长内容。"""
    if not content or len(content) > _XML_PARSE_MAX_LEN or _XML_UNSAFE_RE.search(content):
        return None
    try:
        return ET.fromstring(content)
    except ET.ParseError:
        return None


def _get_self_username():
    """自动识别当前用户的 username（从 DB_DIR 路径推断）。"""
    global _self_username
    if _self_username:
        return _self_username
    if not DB_DIR:
        return ''
    names = get_contact_names()
    account_dir = os.path.basename(os.path.dirname(DB_DIR))
    candidates = [account_dir]
    m = re.fullmatch(r'(.+)_([0-9a-fA-F]{4,})', account_dir)
    if m:
        candidates.insert(0, m.group(1))
    for candidate in candidates:
        if candidate and candidate in names:
            _self_username = candidate
            return _self_username
    return ''


def _is_safe_msg_table_name(table_name):
    """校验消息表名格式，防止 SQL 注入。"""
    return bool(re.fullmatch(r'Msg_[0-9a-f]{32}', table_name))


def _load_name2id_maps(conn):
    """从消息 DB 的 Name2Id 表加载 rowid → username 映射。"""
    id_to_username = {}
    try:
        rows = conn.execute("SELECT rowid, user_name FROM Name2Id").fetchall()
    except sqlite3.Error:
        return id_to_username
    for rowid, user_name in rows:
        if user_name:
            id_to_username[rowid] = user_name
    return id_to_username


def _normalize_speaker_filter(speaker):
    aliases = {
        'all': 'all',
        'both': 'all',
        '全部': 'all',
        'me': 'me',
        'self': 'me',
        '我': 'me',
        'other': 'other',
        'them': 'other',
        'contact': 'other',
        '对方': 'other',
    }
    key = (speaker or 'all').strip().lower()
    return aliases.get(key)


def _classify_private_speaker(status, local_type, display_name, real_sender_id=None, my_sender_id=None):
    """私聊消息归类为我 / 对方 / 系统，避免下游分析混淆发言人。

    优先使用 real_sender_id（可靠），status 仅作为回退。
    macOS 微信数据库中 status 字段在部分消息上不准确（如同步后全部变为 3），
    而 real_sender_id 始终能正确区分发送方。
    """
    if local_type in (10000, 10002) or status == 4:
        return 'system', '系统'
    # 优先用 real_sender_id 判断
    if real_sender_id is not None and my_sender_id is not None:
        if real_sender_id == my_sender_id:
            return 'me', '我'
        return 'other', display_name
    # 回退到 status（不完全可靠）
    if status in (2, 5):
        return 'me', '我'
    return 'other', display_name


_my_sender_id_cache = {}  # db_path -> my_sender_id


def _detect_my_sender_id(db_path, table_name):
    """推断当前用户在该 DB 中的 real_sender_id。

    优先从当前表的 status=2 消息推断；若无 status=2，
    则扫描同一 DB 的所有消息表，取跨表出现次数最多的 real_sender_id。
    结果按 db_path 缓存。
    """
    if db_path in _my_sender_id_cache:
        return _my_sender_id_cache[db_path]

    conn = sqlite3.connect(db_path)
    try:
        # 方法1：当前表的 status=2
        rows = conn.execute(f"""
            SELECT DISTINCT real_sender_id FROM [{table_name}]
            WHERE status = 2 AND real_sender_id IS NOT NULL
            LIMIT 5
        """).fetchall()
        if rows and len(set(r[0] for r in rows)) == 1:
            _my_sender_id_cache[db_path] = rows[0][0]
            return rows[0][0]

        # 方法2：扫描同 DB 所有表，跨表出现最多的 status=2 sender
        all_tables = [r[0] for r in conn.execute(
            "SELECT name FROM sqlite_master WHERE type='table' AND name LIKE 'Msg_%'"
        ).fetchall()]
        from collections import Counter
        status2_counter = Counter()
        for t in all_tables:
            try:
                for r in conn.execute(f"""
                    SELECT DISTINCT real_sender_id FROM [{t}]
                    WHERE status = 2 AND real_sender_id IS NOT NULL
                """).fetchall():
                    status2_counter[r[0]] += 1
            except Exception:
                pass
        if status2_counter:
            winner = status2_counter.most_common(1)[0][0]
            _my_sender_id_cache[db_path] = winner
            return winner

        # 方法3：无 status=2 消息，取跨表出现频率最高的 real_sender_id
        freq_counter = Counter()
        for t in all_tables:
            try:
                seen = set()
                for r in conn.execute(f"""
                    SELECT DISTINCT real_sender_id FROM [{t}]
                    WHERE real_sender_id IS NOT NULL
                """).fetchall():
                    seen.add(r[0])
                for sid in seen:
                    freq_counter[sid] += 1
            except Exception:
                pass
        if freq_counter:
            winner = freq_counter.most_common(1)[0][0]
            # 只有在明显领先时才信任（出现在 >30% 的表中）
            if freq_counter[winner] > len(all_tables) * 0.3:
                _my_sender_id_cache[db_path] = winner
                return winner
    except Exception:
        pass
    finally:
        conn.close()

    _my_sender_id_cache[db_path] = None
    return None


def _format_appmsg(xml_text):
    """解析 appmsg XML，根据子类型返回可读文本。"""
    root = _parse_xml_safe(xml_text)
    if root is None:
        return "[链接/文件]"

    title = root.findtext('.//title') or ""
    appmsg_type = root.findtext('.//type') or ""

    # type=57: 引用回复
    if appmsg_type == '57':
        refer = root.find('.//refermsg')
        if refer is not None:
            # 优先用 fromusr 精确解析被引用人
            ref_user = (refer.findtext('fromusr') or '').strip()
            ref_display = refer.findtext('displayname') or ""
            if ref_user:
                names = get_contact_names()
                self_user = _get_self_username()
                if self_user and ref_user == self_user:
                    ref_name = "我"
                else:
                    ref_name = names.get(ref_user, ref_display or ref_user)
            else:
                ref_name = ref_display
            ref_content = refer.findtext('content') or ""
            # 被引用内容本身可能是 XML（如 appmsg），提取纯文本
            if ref_content.lstrip().startswith('<'):
                ref_root = _parse_xml_safe(ref_content)
                if ref_root is not None:
                    ref_content = ref_root.findtext('.//title') or ref_content
            if len(ref_content) > 50:
                ref_content = ref_content[:50] + "..."
            return f"[引用 {ref_name}: \"{ref_content}\"] {title}"
        return title or "[引用回复]"

    # type=33/36/44: 小程序
    if appmsg_type in ('33', '36', '44'):
        return f"[小程序] {title}" if title else "[小程序]"

    # type=19: 合并转发的聊天记录
    if appmsg_type == '19':
        des = root.findtext('.//des') or ""
        if len(des) > 100:
            des = des[:100] + "..."
        return f"[聊天记录] {title}: {des}" if des else f"[聊天记录] {title}"

    # type=6: 文件
    if appmsg_type == '6':
        return f"[文件] {title}" if title else "[文件]"

    # type=5: 链接文章 / 其他: 默认提取标题和URL
    url = root.findtext('.//url') or ""
    if title:
        return f"[链接] {title}" + (f" ({url})" if url else "")
    return "[链接/文件]"


def _load_chat_messages(username, display_name, limit, since_ts=0, until_ts=0):
    """读取并解析聊天消息，按时间正序返回。since_ts/until_ts 用于时间范围过滤。"""
    is_group = '@chatroom' in username
    db_path, table_name = _find_msg_table_for_user(username)
    if not db_path:
        return None, f"找不到 {display_name} 的消息记录（可能在未解密的DB中或无消息）"

    # 私聊时，先检测当前用户的 real_sender_id
    my_sender_id = None
    if not is_group:
        my_sender_id = _detect_my_sender_id(db_path, table_name)

    conn = sqlite3.connect(db_path)
    try:
        # 加载 Name2Id 映射，用于通过 real_sender_id 精确解析群聊发言人
        id_to_username = _load_name2id_maps(conn)

        if since_ts > 0 and until_ts > 0:
            rows = conn.execute(f"""
                SELECT local_id, local_type, create_time, message_content,
                       WCDB_CT_message_content, status, real_sender_id
                FROM [{table_name}]
                WHERE create_time >= ? AND create_time < ?
                ORDER BY create_time DESC
                LIMIT ?
            """, (since_ts, until_ts, limit)).fetchall()
        elif since_ts > 0:
            rows = conn.execute(f"""
                SELECT local_id, local_type, create_time, message_content,
                       WCDB_CT_message_content, status, real_sender_id
                FROM [{table_name}]
                WHERE create_time >= ?
                ORDER BY create_time DESC
                LIMIT ?
            """, (since_ts, limit)).fetchall()
        else:
            rows = conn.execute(f"""
                SELECT local_id, local_type, create_time, message_content,
                       WCDB_CT_message_content, status, real_sender_id
                FROM [{table_name}]
                ORDER BY create_time DESC
                LIMIT ?
            """, (limit,)).fetchall()
    except Exception as e:
        conn.close()
        return None, f"查询失败: {e}"
    conn.close()

    names = get_contact_names()
    messages = []
    for local_id, local_type, create_time, content, ct, status, real_sender_id in reversed(rows):
        content = _decompress_content(content, ct)
        if content is None:
            content = '(无法解压)'

        # 新版微信用高位编码消息类型，取低32位还原基础类型
        base_type = local_type % 4294967296 if local_type > 4294967296 else local_type

        sender, text = _parse_message_content(content, base_type, is_group)
        if base_type == 3:
            text = f"[图片] (local_id={local_id})"
        elif base_type == 34:
            # 语音：从 XML 提取时长
            dur_str = ""
            root = _parse_xml_safe(text or content)
            if root is not None:
                voice = root.find('.//voicemsg')
                if voice is not None:
                    ms = int(voice.get('voicelength') or 0)
                    dur_str = f" {round(ms / 1000, 1)}s"
            text = f"[语音{dur_str}] (local_id={local_id})"
        elif base_type == 49:
            text = _format_appmsg(text or content)
        elif base_type == 50:
            # 通话：从 CDATA msg 提取描述
            _voip_status_map = {
                'Canceled': '已取消', 'Line busy': '对方忙线',
                'Already answered elsewhere': '已在其他设备接听',
                'Declined on other device': '已在其他设备拒接',
                'Call canceled by caller': '主叫已取消',
                'Call not answered': '未接听', "Call wasn't answered": '未接听',
            }
            desc = ""
            root = _parse_xml_safe(text or content)
            if root is not None:
                raw = (root.findtext('.//msg') or "").strip()
                if raw.startswith("通话时长"):
                    desc = raw.replace("通话时长", "").strip()
                elif raw.startswith("Duration:"):
                    desc = "通话时长 " + raw.split(":", 1)[1].strip()
                elif raw:
                    desc = _voip_status_map.get(raw, raw)
            text = f"[通话 {desc}]" if desc else "[通话]"
        elif base_type == 47:
            text = "[表情]"
        elif base_type != 1:
            type_label = format_msg_type(base_type)
            text = f"[{type_label}] {text}" if text else f"[{type_label}]"

        if text and len(text) > 500:
            text = text[:500] + "..."

        if is_group:
            # 优先用 real_sender_id 通过 Name2Id 表精确解析发言人
            sender_username = id_to_username.get(real_sender_id, '')
            if sender_username and sender_username != username:
                speaker_kind = 'other'
                speaker_label = names.get(sender_username, sender_username)
            elif sender:
                # 回退到 content 前缀解析
                speaker_kind = 'other'
                speaker_label = names.get(sender, sender)
            else:
                speaker_kind = 'system'
                speaker_label = "系统"
        else:
            speaker_kind, speaker_label = _classify_private_speaker(
                status, local_type, display_name,
                real_sender_id=real_sender_id, my_sender_id=my_sender_id,
            )

        messages.append({
            'local_id': local_id,
            'local_type': local_type,
            'create_time': create_time,
            'status': status,
            'speaker_kind': speaker_kind,
            'speaker_label': speaker_label,
            'text': text,
        })

    return messages, None


def _format_message_line(msg):
    time_str = datetime.fromtimestamp(msg['create_time']).strftime('%m-%d %H:%M')
    return f"[{time_str}] {msg['speaker_label']}: {msg['text']}"


# 消息 DB 的 rel_keys
# 用 message_\d+\.db$ 匹配，自然排除 message_resource.db / message_fts_*.db
MSG_DB_KEYS = sorted([
    k for k in ALL_KEYS
    if any(v.startswith("message/") for v in key_path_variants(k))
    and any(re.search(r"message_\d+\.db$", v) for v in key_path_variants(k))
])


def _find_msg_table_for_user(username):
    """在所有 message_N.db 中查找用户的消息表，返回 (db_path, table_name)"""
    table_hash = hashlib.md5(username.encode()).hexdigest()
    table_name = f"Msg_{table_hash}"
    if not _is_safe_msg_table_name(table_name):
        return None, None

    for rel_key in MSG_DB_KEYS:
        path = _cache.get(rel_key)
        if not path:
            continue
        conn = sqlite3.connect(path)
        try:
            exists = conn.execute(
                "SELECT 1 FROM sqlite_master WHERE type='table' AND name=?",
                (table_name,)
            ).fetchone()
            if exists:
                conn.close()
                return path, table_name
        except Exception:
            pass
        finally:
            conn.close()

    return None, None


# ============ MCP Server ============

mcp = FastMCP("wechat", instructions="查询微信消息、联系人等数据")

# 新消息追踪
_last_check_state = {}  # {username: last_timestamp}


@mcp.tool()
def get_recent_sessions(limit: int = 20) -> str:
    """获取微信最近会话列表，包含最新消息摘要、未读数、时间等。
    用于了解最近有哪些人/群在聊天。

    Args:
        limit: 返回的会话数量，默认20
    """
    path = _cache.get(os.path.join("session", "session.db"))
    if not path:
        return "错误: 无法解密 session.db"

    names = get_contact_names()
    conn = sqlite3.connect(path)
    rows = conn.execute("""
        SELECT username, unread_count, summary, last_timestamp,
               last_msg_type, last_msg_sender, last_sender_display_name
        FROM SessionTable
        WHERE last_timestamp > 0
        ORDER BY last_timestamp DESC
        LIMIT ?
    """, (limit,)).fetchall()
    conn.close()

    results = []
    for r in rows:
        username, unread, summary, ts, msg_type, sender, sender_name = r
        display = names.get(username, username)
        is_group = '@chatroom' in username

        if isinstance(summary, bytes):
            try:
                summary = _zstd_dctx.decompress(summary).decode('utf-8', errors='replace')
            except Exception:
                summary = '(压缩内容)'
        if isinstance(summary, str) and ':\n' in summary:
            summary = summary.split(':\n', 1)[1]

        sender_display = ''
        if is_group and sender:
            sender_display = names.get(sender, sender_name or sender)

        time_str = datetime.fromtimestamp(ts).strftime('%m-%d %H:%M')

        entry = f"[{time_str}] {display}"
        if is_group:
            entry += " [群]"
        if unread and unread > 0:
            entry += f" ({unread}条未读)"
        entry += f"\n  {format_msg_type(msg_type)}: "
        if sender_display:
            entry += f"{sender_display}: "
        entry += str(summary or "(无内容)")

        results.append(entry)

    return f"最近 {len(results)} 个会话:\n\n" + "\n\n".join(results)


@mcp.tool()
def get_chat_history(chat_name: str, limit: int = 50, speaker: str = "all", days: int = 0, date: str = "") -> str:
    """获取指定聊天的消息记录。

    Args:
        chat_name: 聊天对象的名字、备注名或wxid，自动模糊匹配
        limit: 返回的消息数量，默认50
        speaker: 发言人过滤，支持 all / me / other。做人画像建议用 other
        days: 只返回最近N天的消息（0=不限，1=今天，3=最近3天）
        date: 指定具体日期，格式 YYYY-MM-DD（如 2026-03-05），查该天的消息
    """
    username = resolve_username(chat_name)
    if not username:
        return f"找不到聊天对象: {chat_name}\n提示: 可以用 get_contacts(query='{chat_name}') 搜索联系人"

    speaker_filter = _normalize_speaker_filter(speaker)
    if not speaker_filter:
        return "speaker 参数无效，支持: all / me / other"

    names = get_contact_names()
    display_name = names.get(username, username)
    is_group = '@chatroom' in username

    if is_group and speaker_filter != 'all':
        return "群聊暂不支持 speaker 过滤，请使用 speaker='all'"

    since_ts = 0
    until_ts = 0
    if date:
        try:
            day_start = datetime.strptime(date, "%Y-%m-%d")
            from datetime import timedelta
            since_ts = int(day_start.timestamp())
            until_ts = int((day_start + timedelta(days=1)).timestamp())
            limit = max(limit, 500)
        except ValueError:
            return "date 格式无效，请用 YYYY-MM-DD（如 2026-03-05）"
    elif days and days > 0:
        from datetime import timedelta
        today_start = datetime.now().replace(hour=0, minute=0, second=0, microsecond=0)
        since_ts = int((today_start - timedelta(days=days - 1)).timestamp())
        limit = max(limit, 500)

    messages, error = _load_chat_messages(username, display_name, limit, since_ts=since_ts, until_ts=until_ts)
    if error:
        return error
    if not messages:
        return f"{display_name} 无消息记录"

    lines = []
    for msg in messages:
        if speaker_filter != 'all' and msg['speaker_kind'] != speaker_filter:
            continue
        lines.append(_format_message_line(msg))

    if not lines:
        return f"{display_name} 无符合条件的消息记录 (speaker={speaker_filter})"

    header = f"{display_name} 的最近 {len(lines)} 条消息"
    if is_group:
        header += " [群聊]"
    elif speaker_filter != 'all':
        header += f" [speaker={speaker_filter}]"
    return header + ":\n\n" + "\n".join(lines)


@mcp.tool()
def search_messages(keyword: str, limit: int = 20, days: int = 0, date: str = "") -> str:
    """在所有聊天记录中搜索包含关键词的消息。

    Args:
        keyword: 搜索关键词
        limit: 返回的结果数量，默认20
        days: 只搜索最近N天（0=不限，1=今天，7=最近一周）
        date: 指定具体日期，格式 YYYY-MM-DD
    """
    if not keyword or len(keyword) < 1:
        return "请提供搜索关键词"

    # 时间范围
    since_ts, until_ts = 0, 0
    if date:
        try:
            from datetime import timedelta
            day_start = datetime.strptime(date, "%Y-%m-%d")
            since_ts = int(day_start.timestamp())
            until_ts = int((day_start + timedelta(days=1)).timestamp())
        except ValueError:
            return "date 格式无效，请用 YYYY-MM-DD"
    elif days and days > 0:
        from datetime import timedelta
        today_start = datetime.now().replace(hour=0, minute=0, second=0, microsecond=0)
        since_ts = int((today_start - timedelta(days=days - 1)).timestamp())

    names = get_contact_names()
    results = []

    for rel_key in MSG_DB_KEYS:
        if len(results) >= limit:
            break

        path = _cache.get(rel_key)
        if not path:
            continue

        conn = sqlite3.connect(path)
        try:
            # 获取所有 Msg_ 表
            tables = conn.execute(
                "SELECT name FROM sqlite_master WHERE type='table' AND name LIKE 'Msg_%'"
            ).fetchall()

            # 获取 Name2Id 映射（hash -> username 反查）
            name2id = {}
            try:
                for r in conn.execute("SELECT user_name FROM Name2Id").fetchall():
                    h = hashlib.md5(r[0].encode()).hexdigest()
                    name2id[f"Msg_{h}"] = r[0]
            except Exception:
                pass

            for (tname,) in tables:
                if len(results) >= limit:
                    break
                username = name2id.get(tname, '')
                is_group = '@chatroom' in username
                display = names.get(username, username) if username else tname

                try:
                    time_clause = ""
                    params = [f'%{keyword}%']
                    if since_ts > 0 and until_ts > 0:
                        time_clause = " AND create_time >= ? AND create_time < ?"
                        params.extend([since_ts, until_ts])
                    elif since_ts > 0:
                        time_clause = " AND create_time >= ?"
                        params.append(since_ts)
                    params.append(limit - len(results))

                    rows = conn.execute(f"""
                        SELECT local_type, create_time, message_content,
                               WCDB_CT_message_content
                        FROM [{tname}]
                        WHERE message_content LIKE ?{time_clause}
                        ORDER BY create_time DESC
                        LIMIT ?
                    """, params).fetchall()
                except Exception:
                    continue

                for local_type, ts, content, ct in rows:
                    content = _decompress_content(content, ct)
                    if content is None:
                        continue
                    sender, text = _parse_message_content(content, local_type, is_group)
                    time_str = datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M')
                    sender_name = ''
                    if is_group and sender:
                        sender_name = names.get(sender, sender)

                    entry = f"[{time_str}] [{display}]"
                    if sender_name:
                        entry += f" {sender_name}:"
                    entry += f" {text}"
                    if len(entry) > 300:
                        entry = entry[:300] + "..."
                    results.append((ts, entry))
        finally:
            conn.close()

    results.sort(key=lambda x: x[0], reverse=True)
    entries = [r[1] for r in results[:limit]]

    if not entries:
        return f"未找到包含 \"{keyword}\" 的消息"

    return f"搜索 \"{keyword}\" 找到 {len(entries)} 条结果:\n\n" + "\n\n".join(entries)


@mcp.tool()
def get_contacts(query: str = "", limit: int = 50) -> str:
    """搜索或列出微信联系人。

    Args:
        query: 搜索关键词（匹配昵称、备注名、wxid），留空列出所有
        limit: 返回数量，默认50
    """
    contacts = get_contact_full()
    if not contacts:
        return "错误: 无法加载联系人数据"

    if query:
        q = query.lower()
        filtered = [
            c for c in contacts
            if q in c['nick_name'].lower()
            or q in c['remark'].lower()
            or q in c['username'].lower()
        ]
    else:
        filtered = contacts

    filtered = filtered[:limit]

    if not filtered:
        return f"未找到匹配 \"{query}\" 的联系人"

    lines = []
    for c in filtered:
        line = c['username']
        if c['remark']:
            line += f"  备注: {c['remark']}"
        if c['nick_name']:
            line += f"  昵称: {c['nick_name']}"
        lines.append(line)

    header = f"找到 {len(filtered)} 个联系人"
    if query:
        header += f"（搜索: {query}）"
    return header + ":\n\n" + "\n".join(lines)


@mcp.tool()
def get_new_messages() -> str:
    """获取自上次调用以来的新消息。首次调用返回最近的会话状态。"""
    global _last_check_state

    path = _cache.get(os.path.join("session", "session.db"))
    if not path:
        return "错误: 无法解密 session.db"

    names = get_contact_names()
    conn = sqlite3.connect(path)
    rows = conn.execute("""
        SELECT username, unread_count, summary, last_timestamp,
               last_msg_type, last_msg_sender, last_sender_display_name
        FROM SessionTable
        WHERE last_timestamp > 0
        ORDER BY last_timestamp DESC
    """).fetchall()
    conn.close()

    curr_state = {}
    for r in rows:
        username, unread, summary, ts, msg_type, sender, sender_name = r
        curr_state[username] = {
            'unread': unread, 'summary': summary, 'timestamp': ts,
            'msg_type': msg_type, 'sender': sender or '', 'sender_name': sender_name or '',
        }

    if not _last_check_state:
        _last_check_state = {u: s['timestamp'] for u, s in curr_state.items()}
        # 首次调用，返回有未读的会话
        unread_msgs = []
        for username, s in curr_state.items():
            if s['unread'] and s['unread'] > 0:
                display = names.get(username, username)
                is_group = '@chatroom' in username
                summary = s['summary']
                if isinstance(summary, bytes):
                    try:
                        summary = _zstd_dctx.decompress(summary).decode('utf-8', errors='replace')
                    except Exception:
                        summary = '(压缩内容)'
                if isinstance(summary, str) and ':\n' in summary:
                    summary = summary.split(':\n', 1)[1]
                time_str = datetime.fromtimestamp(s['timestamp']).strftime('%H:%M')
                tag = "[群]" if is_group else ""
                unread_msgs.append(f"[{time_str}] {display}{tag} ({s['unread']}条未读): {summary}")

        if unread_msgs:
            return f"当前 {len(unread_msgs)} 个未读会话:\n\n" + "\n".join(unread_msgs)
        return "当前无未读消息（已记录状态，下次调用将返回新消息）"

    # 对比上次状态
    new_msgs = []
    for username, s in curr_state.items():
        prev_ts = _last_check_state.get(username, 0)
        if s['timestamp'] > prev_ts:
            display = names.get(username, username)
            is_group = '@chatroom' in username
            summary = s['summary']
            if isinstance(summary, bytes):
                try:
                    summary = _zstd_dctx.decompress(summary).decode('utf-8', errors='replace')
                except Exception:
                    summary = '(压缩内容)'
            if isinstance(summary, str) and ':\n' in summary:
                summary = summary.split(':\n', 1)[1]

            sender_display = ''
            if is_group and s['sender']:
                sender_display = names.get(s['sender'], s['sender_name'] or s['sender'])

            time_str = datetime.fromtimestamp(s['timestamp']).strftime('%H:%M:%S')
            entry = f"[{time_str}] {display}"
            if is_group:
                entry += " [群]"
            entry += f": {format_msg_type(s['msg_type'])}"
            if sender_display:
                entry += f" ({sender_display})"
            entry += f" - {summary}"
            new_msgs.append((s['timestamp'], entry))

    _last_check_state = {u: s['timestamp'] for u, s in curr_state.items()}

    if not new_msgs:
        return "无新消息"

    new_msgs.sort(key=lambda x: x[0])
    entries = [m[1] for m in new_msgs]
    return f"{len(entries)} 条新消息:\n\n" + "\n".join(entries)


# ============ 图片解密 ============

_image_resolver = ImageResolver(WECHAT_BASE_DIR, DECODED_IMAGE_DIR, _cache)


@mcp.tool()
def decode_image(chat_name: str, local_id: int) -> str:
    """解密微信聊天中的一张图片。

    先用 get_chat_history 查看消息，图片消息会显示 local_id，
    然后用此工具解密对应图片。

    Args:
        chat_name: 聊天对象的名字、备注名或wxid
        local_id: 图片消息的 local_id（从 get_chat_history 获取）
    """
    username = resolve_username(chat_name)
    if not username:
        return f"找不到聊天对象: {chat_name}"

    result = _image_resolver.decode_image(username, local_id)
    if result['success']:
        return (
            f"解密成功!\n"
            f"  文件: {result['path']}\n"
            f"  格式: {result['format']}\n"
            f"  大小: {result['size']:,} bytes\n"
            f"  MD5: {result['md5']}"
        )
    else:
        error = result['error']
        if 'md5' in result:
            error += f"\n  MD5: {result['md5']}"
        return f"解密失败: {error}"


@mcp.tool()
def get_chat_images(chat_name: str, limit: int = 20) -> str:
    """列出某个聊天中的图片消息。

    返回图片的时间、local_id、MD5、文件大小等信息。
    可以配合 decode_image 工具解密指定图片。

    Args:
        chat_name: 聊天对象的名字、备注名或wxid
        limit: 返回数量，默认20
    """
    username = resolve_username(chat_name)
    if not username:
        return f"找不到聊天对象: {chat_name}"

    names = get_contact_names()
    display_name = names.get(username, username)

    db_path, table_name = _find_msg_table_for_user(username)
    if not db_path:
        return f"找不到 {display_name} 的消息记录"

    images = _image_resolver.list_chat_images(db_path, table_name, username, limit)
    if not images:
        return f"{display_name} 无图片消息"

    lines = []
    for img in images:
        time_str = datetime.fromtimestamp(img['create_time']).strftime('%Y-%m-%d %H:%M')
        line = f"[{time_str}] local_id={img['local_id']}"
        if img.get('md5'):
            line += f"  MD5={img['md5']}"
        if img.get('size'):
            size_kb = img['size'] / 1024
            line += f"  {size_kb:.0f}KB"
        if not img.get('md5'):
            line += "  (无资源信息)"
        lines.append(line)

    return f"{display_name} 的 {len(lines)} 张图片:\n\n" + "\n".join(lines)


# ============ 语音转写 ============

_whisper_model = None
_media_db_cache = {}  # db_path -> (mtime, tmp_path)


def _get_whisper_model():
    global _whisper_model
    if _whisper_model is None:
        from faster_whisper import WhisperModel
        _whisper_model = WhisperModel("base", device="cpu", compute_type="int8")
    return _whisper_model


def _get_media_db_conn():
    """解密并缓存 media_0.db，返回 sqlite3 连接。"""
    media_rel = "message/media_0.db"
    db_path = os.path.join(DB_DIR, media_rel)
    if not os.path.exists(db_path):
        return None

    mtime = os.path.getmtime(db_path)
    wal_path = db_path + "-wal"
    wal_mtime = os.path.getmtime(wal_path) if os.path.exists(wal_path) else 0

    cached = _media_db_cache.get(db_path)
    if cached and cached[0] == (mtime, wal_mtime):
        return sqlite3.connect(cached[1])

    keys_file = _cfg["keys_file"]
    with open(keys_file) as f:
        keys = json.load(f)
    key_entry = keys.get(media_rel)
    if not key_entry:
        return None
    enc_key = bytes.fromhex(key_entry["enc_key"])

    tmp_path = os.path.join(tempfile.gettempdir(), "wechat_mcp_cache", "media_0.db")
    os.makedirs(os.path.dirname(tmp_path), exist_ok=True)
    full_decrypt(db_path, tmp_path, enc_key)
    if os.path.exists(wal_path):
        decrypt_wal(wal_path, tmp_path, enc_key)

    _media_db_cache[db_path] = ((mtime, wal_mtime), tmp_path)
    return sqlite3.connect(tmp_path)


def _silk_to_text(voice_data):
    """SILK voice data -> transcribed text."""
    import pilk
    import wave

    silk_path = tempfile.mktemp(suffix=".silk")
    pcm_path = tempfile.mktemp(suffix=".pcm")
    wav_path = tempfile.mktemp(suffix=".wav")
    try:
        # Strip WeChat SILK header byte (0x02)
        with open(silk_path, "wb") as f:
            f.write(voice_data[1:] if voice_data[0:1] == b"\x02" else voice_data)

        pilk.decode(silk_path, pcm_path)

        # PCM -> WAV (16-bit, 24000 Hz mono)
        with open(pcm_path, "rb") as f:
            pcm_data = f.read()
        with wave.open(wav_path, "wb") as wf:
            wf.setnchannels(1)
            wf.setsampwidth(2)
            wf.setframerate(24000)
            wf.writeframes(pcm_data)

        model = _get_whisper_model()
        segments, _ = model.transcribe(wav_path, language="zh")
        return "".join(s.text for s in segments).strip()
    finally:
        for p in (silk_path, pcm_path, wav_path):
            if os.path.exists(p):
                os.unlink(p)


@mcp.tool()
def transcribe_voice(chat_name: str, local_id: int = 0, limit: int = 0) -> str:
    """转写微信语音消息为文字。

    两种用法：
    1. 指定 local_id：转写单条语音
    2. 指定 limit（不指定 local_id）：转写该聊天最近 N 条语音

    Args:
        chat_name: 聊天对象的名字、备注名或wxid
        local_id: 语音消息的 local_id（从 get_chat_history 获取），0 表示不指定
        limit: 批量转写最近 N 条语音（默认 0，即不批量；建议不超过 10）
    """
    username = resolve_username(chat_name)
    if not username:
        return f"找不到聊天对象: {chat_name}"

    names = get_contact_names()
    display_name = names.get(username, username)

    conn = _get_media_db_conn()
    if not conn:
        return "无法打开语音数据库 (media_0.db)"

    try:
        # 找到 chat_name_id
        row = conn.execute(
            "SELECT rowid FROM Name2Id WHERE user_name = ?", (username,)
        ).fetchone()
        if not row:
            return f"{display_name} 无语音记录"
        chat_name_id = row[0]

        if local_id:
            # 单条转写
            row = conn.execute(
                "SELECT voice_data FROM VoiceInfo WHERE chat_name_id = ? AND local_id = ?",
                (chat_name_id, local_id),
            ).fetchone()
            if not row or not row[0]:
                return f"找不到 local_id={local_id} 的语音数据"
            text = _silk_to_text(row[0])
            return f"[语音转写] {text}" if text else "[语音转写] (无法识别)"

        elif limit and limit > 0:
            # 批量转写
            limit = min(limit, 20)
            rows = conn.execute(
                """SELECT local_id, create_time, voice_data FROM VoiceInfo
                   WHERE chat_name_id = ?
                   ORDER BY create_time DESC LIMIT ?""",
                (chat_name_id, limit),
            ).fetchall()
            if not rows:
                return f"{display_name} 无语音记录"

            # 获取发言人信息
            is_group = '@chatroom' in username
            msg_db_path, msg_table = _find_msg_table_for_user(username)
            my_sender_id = None
            if msg_db_path and not is_group:
                my_sender_id = _detect_my_sender_id(msg_db_path, msg_table)

            results = []
            for lid, ctime, vdata in reversed(rows):
                ts = datetime.fromtimestamp(ctime).strftime("%m-%d %H:%M")
                # 判断发言人
                speaker = display_name
                if msg_db_path:
                    msg_conn = sqlite3.connect(msg_db_path)
                    try:
                        msg_row = msg_conn.execute(
                            f"SELECT message_content, WCDB_CT_message_content, real_sender_id FROM [{msg_table}] WHERE local_id = ?",
                            (lid,),
                        ).fetchone()
                        if msg_row:
                            if is_group:
                                # 群聊：从 "wxid:\n" 前缀提取发言人
                                mc = _decompress_content(msg_row[0], msg_row[1]) or ""
                                if ':\n' in mc:
                                    sender_wxid = mc.split(':\n', 1)[0]
                                    speaker = names.get(sender_wxid, sender_wxid)
                            elif my_sender_id is not None and msg_row[2] == my_sender_id:
                                speaker = "我"
                    except Exception:
                        pass
                    finally:
                        msg_conn.close()

                try:
                    text = _silk_to_text(vdata)
                    results.append(f"[{ts}] {speaker}: {text}" if text else f"[{ts}] {speaker}: (无法识别)")
                except Exception as e:
                    results.append(f"[{ts}] {speaker}: (转写失败: {e})")

            return f"{display_name} 最近 {len(results)} 条语音转写:\n\n" + "\n".join(results)

        else:
            return "请指定 local_id（单条转写）或 limit（批量转写）"
    finally:
        conn.close()


@mcp.tool()
def get_group_stats(chat_name: str, days: int = 1, limit: int = 500, date: str = "") -> str:
    """统计群聊发言排行和活跃度。

    Args:
        chat_name: 群聊名称
        days: 统计最近N天（默认1=今天）
        limit: 最多扫描的消息数（默认500）
        date: 指定具体日期，格式 YYYY-MM-DD（如 2026-03-05）
    """
    username = resolve_username(chat_name)
    if not username:
        return f"找不到聊天对象: {chat_name}"
    if '@chatroom' not in username:
        return "此工具仅支持群聊"

    names = get_contact_names()
    display_name = names.get(username, username)

    from datetime import timedelta
    since_ts = 0
    until_ts = 0
    time_label = f"最近 {days} 天"
    if date:
        try:
            day_start = datetime.strptime(date, "%Y-%m-%d")
            since_ts = int(day_start.timestamp())
            until_ts = int((day_start + timedelta(days=1)).timestamp())
            time_label = date
        except ValueError:
            return "date 格式无效，请用 YYYY-MM-DD"
    else:
        today_start = datetime.now().replace(hour=0, minute=0, second=0, microsecond=0)
        since_ts = int((today_start - timedelta(days=days - 1)).timestamp())

    messages, error = _load_chat_messages(username, display_name, limit, since_ts=since_ts, until_ts=until_ts)
    if error:
        return error
    if not messages:
        return f"{display_name} {time_label}无消息"

    from collections import Counter
    speaker_counter = Counter()
    for msg in messages:
        if msg['speaker_kind'] != 'system':
            speaker_counter[msg['speaker_label']] += 1

    total = len(messages)
    lines = [f"{display_name} {time_label}发言统计 (共 {total} 条):\n"]
    for rank, (name, count) in enumerate(speaker_counter.most_common(20), 1):
        pct = count / total * 100
        lines.append(f"{rank}. {name}: {count}条 ({pct:.0f}%)")

    return "\n".join(lines)


if __name__ == "__main__":
    mcp.run()
