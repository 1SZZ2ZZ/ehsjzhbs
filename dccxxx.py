# -*- coding: utf-8 -*-
import os
import socket
import http.server
import socketserver
import urllib.parse
import html
import logging
import time
import subprocess
from functools import partial
import platform
import json
import uuid
import re
import hashlib  # 添加hashlib用于密码哈希
from datetime import datetime, timedelta
from http import HTTPStatus
import threading
import psutil  # 添加psutil用于获取系统信息

# 配置日志系统
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('server.log'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

# 局域网域名配置
LAN_DOMAIN = "localapp.update"
DEFAULT_PORT = 8000  # 默认端口改为8000避免权限问题
MAX_RETRIES = 3

# ngrok配置
NGROK_DOMAIN = "sound-amazed-poodle.ngrok-free.app"
NGROK_CMD = f"ngrok http --url={NGROK_DOMAIN} {DEFAULT_PORT}"

# 数据持久化文件 - 使用绝对路径确保一致性
MESSAGES_FILE = os.path.abspath("chat_messages.json")
USERNAMES_FILE = os.path.abspath("used_usernames.json")  # 存储已使用的用户名
SESSIONS_FILE = os.path.abspath("user_sessions.json")    # 存储用户会话数据
PASSWORDS_FILE = os.path.abspath("user_passwords.json")  # 存储用户密码哈希

# 全局变量存储用户密码哈希
user_passwords = {}


# 全局变量存储聊天消息和在线用户
chat_messages = []
private_messages = []  # 存储私信消息
online_users = {}  # 存储客户端IP与用户名的映射: {ip: username}
used_usernames = set()  # 存储已使用的用户名，确保唯一性
MAX_CHAT_MESSAGES = 200  # 限制最大公开消息数量

# 添加获取系统信息的函数
def get_system_info():
    """获取并返回当前电脑的详细配置信息"""
    try:
        # 获取CPU信息
        cpu_info = {
            "physical_cores": psutil.cpu_count(logical=False),
            "logical_cores": psutil.cpu_count(logical=True),
            "max_frequency": f"{psutil.cpu_freq().max:.2f} MHz",
            "current_frequency": f"{psutil.cpu_freq().current:.2f} MHz",
            "usage_percent": f"{psutil.cpu_percent(interval=1)}%"
        }
        
        # 获取内存信息
        mem = psutil.virtual_memory()
        swap = psutil.swap_memory()
        memory_info = {
            "total": f"{mem.total / (1024 ** 3):.2f} GB",
            "available": f"{mem.available / (1024 ** 3):.2f} GB",
            "used": f"{mem.used / (1024 ** 3):.2f} GB",
            "usage_percent": f"{mem.percent}%",
            "swap_total": f"{swap.total / (1024 ** 3):.2f} GB",
            "swap_used": f"{swap.used / (1024 ** 3):.2f} GB"
        }
        
        # 获取磁盘信息
        disk_info = []
        for part in psutil.disk_partitions(all=False):
            if part.fstype:
                try:
                    usage = psutil.disk_usage(part.mountpoint)
                    disk_info.append({
                        "device": part.device,
                        "mountpoint": part.mountpoint,
                        "fstype": part.fstype,
                        "total": f"{usage.total / (1024 ** 3):.2f} GB",
                        "used": f"{usage.used / (1024 ** 3):.2f} GB",
                        "free": f"{usage.free / (1024 ** 3):.2f} GB",
                        "percent": f"{usage.percent}%"
                    })
                except Exception as e:
                    logger.error(f"获取磁盘 {part.device} 使用情况失败: {e}")
        
        # 获取网络信息
        net_info = []
        net_io = psutil.net_io_counters()
        net_info.append({
            "bytes_sent": f"{net_io.bytes_sent / (1024 ** 2):.2f} MB",
            "bytes_recv": f"{net_io.bytes_recv / (1024 ** 2):.2f} MB"
        })
        
        # 获取系统信息
        boot_time = datetime.fromtimestamp(psutil.boot_time())
        system_info = {
            "system": platform.system(),
            "node": platform.node(),
            "release": platform.release(),
            "version": platform.version(),
            "machine": platform.machine(),
            "processor": platform.processor(),
            "architecture": platform.architecture()[0],
            "boot_time": boot_time.strftime("%Y-%m-%d %H:%M:%S"),
            "uptime": str(datetime.now() - boot_time).split('.')[0]
        }
        
        # 获取进程信息
        process_info = []
        for proc in psutil.process_iter(['pid', 'name', 'username', 'cpu_percent', 'memory_percent']):
            try:
                process_info.append({
                    "pid": proc.info['pid'],
                    "name": proc.info['name'],
                    "user": proc.info['username'],
                    "cpu": f"{proc.info['cpu_percent']}%",
                    "memory": f"{proc.info['memory_percent']}%"
                })
            except (psutil.NoSuchProcess, psutil.AccessDenied, psutil.ZombieProcess):
                pass
        
        # 按内存使用排序并取前10个
        process_info.sort(key=lambda x: float(x['memory'].rstrip('%')), reverse=True)
        top_processes = process_info[:10]
        
        return {
            "system": system_info,
            "cpu": cpu_info,
            "memory": memory_info,
            "disks": disk_info,
            "network": net_info,
            "top_processes": top_processes
        }
        
    except Exception as e:
        # 简化错误处理，不记录详细异常信息
        return {"error": str(e)}

MAX_PRIVATE_MESSAGES = 500  # 限制最大私信数量

# 会话管理配置 - 修改为永久有效
USER_SESSIONS = {}  # {session_id: {username}} - 移除过期时间字段


def load_messages():
    """从文件加载聊天消息（包括私信）"""
    global chat_messages, private_messages
    try:
        logger.info(f"开始加载聊天消息文件: {MESSAGES_FILE}")
        
        if os.path.exists(MESSAGES_FILE) and os.path.getsize(MESSAGES_FILE) > 0:
            with open(MESSAGES_FILE, 'r', encoding='utf-8') as f:
                data = json.load(f)
                chat_messages = data.get('public', [])
                private_messages = data.get('private', [])
            
            # 确保不超过最大消息数量
            if len(chat_messages) > MAX_CHAT_MESSAGES:
                chat_messages = chat_messages[-MAX_CHAT_MESSAGES:]
            if len(private_messages) > MAX_PRIVATE_MESSAGES:
                private_messages = private_messages[-MAX_PRIVATE_MESSAGES:]
                
            logger.info(f"从文件加载了 {len(chat_messages)} 条公开消息和 {len(private_messages)} 条私信")
        else:
            logger.info("聊天消息文件不存在或为空，将初始化空列表")
            chat_messages = []
            private_messages = []
    except Exception as e:
        # 简化错误处理，不记录详细异常信息
        chat_messages = []
        private_messages = []


def save_messages():
    """将聊天消息（包括私信）保存到文件"""
    try:
        # 确保目录存在
        dir_path = os.path.dirname(MESSAGES_FILE)
        if not os.path.exists(dir_path):
            os.makedirs(dir_path)
        
        with open(MESSAGES_FILE, 'w', encoding='utf-8') as f:
            json.dump({
                'public': chat_messages,
                'private': private_messages
            }, f, ensure_ascii=False, indent=2)
        logger.debug(f"已保存 {len(chat_messages)} 条公开消息和 {len(private_messages)} 条私信到文件")
    except Exception as e:
        logger.error(f"保存聊天消息失败: {str(e)}", exc_info=True)


def load_passwords():
    """从文件加载用户密码哈希"""
    global user_passwords
    try:
        logger.info(f"开始加载用户密码文件: {PASSWORDS_FILE}")
        
        if os.path.exists(PASSWORDS_FILE) and os.path.getsize(PASSWORDS_FILE) > 0:
            with open(PASSWORDS_FILE, 'r', encoding='utf-8') as f:
                data = json.load(f)
                user_passwords = data.get('users', {})
            logger.info(f"从文件加载了 {len(user_passwords)} 个用户密码")
        else:
            logger.info("密码文件不存在或为空，将初始化空字典")
            user_passwords = {}
    except Exception as e:
        logger.error(f"加载密码失败: {str(e)}", exc_info=True)
        user_passwords = {}


def save_passwords():
    """将用户密码哈希保存到文件"""
    try:
        # 确保目录存在
        dir_path = os.path.dirname(PASSWORDS_FILE)
        if not os.path.exists(dir_path):
            os.makedirs(dir_path)
        
        with open(PASSWORDS_FILE, 'w', encoding='utf-8') as f:
            json.dump({
                'users': user_passwords
            }, f, ensure_ascii=False, indent=2)
        logger.debug(f"已保存 {len(user_passwords)} 个用户密码到文件")
    except Exception as e:
        logger.error(f"保存密码失败: {str(e)}", exc_info=True)


def load_usernames():
    """从文件加载已使用的用户名"""
    global used_usernames
    try:
        logger.info(f"开始加载已使用用户名文件: {USERNAMES_FILE}")
        
        if os.path.exists(USERNAMES_FILE) and os.path.getsize(USERNAMES_FILE) > 0:
            with open(USERNAMES_FILE, 'r', encoding='utf-8') as f:
                used_usernames = set(json.load(f))
            logger.info(f"从文件加载了 {len(used_usernames)} 个已使用用户名")
        else:
            logger.info("用户名文件不存在或为空，将初始化空集合")
            used_usernames = set()
    except Exception as e:
        logger.error(f"加载用户名失败: {str(e)}", exc_info=True)
        used_usernames = set()


def save_usernames():
    """将已使用的用户名保存到文件"""
    try:
        # 确保目录存在
        dir_path = os.path.dirname(USERNAMES_FILE)
        if not os.path.exists(dir_path):
            os.makedirs(dir_path)
        
        with open(USERNAMES_FILE, 'w', encoding='utf-8') as f:
            json.dump(list(used_usernames), f, ensure_ascii=False, indent=2)
        logger.debug(f"已保存 {len(used_usernames)} 个已使用用户名到文件")
    except Exception as e:
        logger.error(f"保存用户名失败: {str(e)}", exc_info=True)


# 会话持久化函数
def save_sessions():
    """将会话数据保存到文件"""
    try:
        # 确保目录存在
        dir_path = os.path.dirname(SESSIONS_FILE)
        if not os.path.exists(dir_path):
            os.makedirs(dir_path)
        
        with open(SESSIONS_FILE, 'w', encoding='utf-8') as f:
            json.dump(USER_SESSIONS, f, ensure_ascii=False, indent=2)
        logger.debug(f"已保存 {len(USER_SESSIONS)} 个会话到文件")
    except Exception as e:
        logger.error(f"保存会话失败: {str(e)}", exc_info=True)


def load_sessions():
    """从文件加载会话数据"""
    global USER_SESSIONS
    try:
        logger.info(f"开始加载会话文件: {SESSIONS_FILE}")
        
        if os.path.exists(SESSIONS_FILE) and os.path.getsize(SESSIONS_FILE) > 0:
            with open(SESSIONS_FILE, 'r', encoding='utf-8') as f:
                USER_SESSIONS = json.load(f)
            logger.info(f"从文件加载了 {len(USER_SESSIONS)} 个会话")
        else:
            logger.info("会话文件不存在或为空，将初始化空字典")
            USER_SESSIONS = {}
    except Exception as e:
        logger.error(f"加载会话失败: {str(e)}", exc_info=True)
        USER_SESSIONS = {}


# 会话管理函数 - 修改为永久有效
def create_session(username):
    """创建用户会话并返回会话ID，有效期为24小时"""
    session_id = str(uuid.uuid4())  # 生成唯一会话ID
    csrf_token = str(uuid.uuid4())  # 生成CSRF令牌
    USER_SESSIONS[session_id] = {
        "username": username,
        "created_at": time.time(),  # 添加创建时间
        "csrf_token": csrf_token    # 添加CSRF令牌
    }
    save_sessions()  # 创建新会话后保存
    return session_id, csrf_token


def get_username_from_session(session_id):
    """通过会话ID获取用户名，检查会话是否过期"""
    if not session_id or session_id not in USER_SESSIONS:
        return None
    
    # 检查会话是否过期（24小时）
    session_data = USER_SESSIONS[session_id]
    if time.time() - session_data.get("created_at", 0) > 86400:
        del USER_SESSIONS[session_id]
        save_sessions()
        return None
    
    return session_data["username"]


def validate_csrf_token(self, session_id):
    """验证CSRF令牌"""
    # 获取CSRF令牌（从请求头或表单数据）
    csrf_token = self.headers.get('X-CSRF-Token')
    if not csrf_token:
        # 尝试从表单数据中获取
        try:
            content_length = int(self.headers.get('Content-Length', 0))
            post_data = self.rfile.read(content_length).decode('utf-8')
            data = json.loads(post_data)
            csrf_token = data.get('csrf_token')
        except:
            pass
    
    # 检查CSRF令牌是否存在且有效
    if not csrf_token or session_id not in USER_SESSIONS:
        return False
    
    session_data = USER_SESSIONS[session_id]
    if csrf_token != session_data.get("csrf_token"):
        return False
    
    return True


def clean_expired_sessions():
    """清理过期的会话 (每小时运行一次)"""
    current_time = time.time()
    expired_sessions = []
    
    for session_id, session_data in USER_SESSIONS.items():
        # 检查会话是否超过24小时
        if current_time - session_data.get("created_at", 0) > 86400:
            expired_sessions.append(session_id)
    
    for session_id in expired_sessions:
        del USER_SESSIONS[session_id]
    
    if expired_sessions:
        save_sessions()
        logger.info(f"已清理 {len(expired_sessions)} 个过期会话")

# 启动会话清理线程
import threading
def start_session_cleaner():
    def cleaner_thread():
        while True:
            clean_expired_sessions()
            time.sleep(3600)  # 每小时运行一次
    
    thread = threading.Thread(target=cleaner_thread, daemon=True)
    thread.start()
    logger.info("会话清理线程已启动")

# 启动会话清理服务
start_session_cleaner()


# 初始化时加载数据 - 增加重试机制
load_success = False
for attempt in range(3):
    try:
        load_messages()
        load_usernames()
        load_passwords()  # 加载密码数据
        load_sessions()  # 加载会话数据
        load_success = True
        break
    except Exception as e:
        logger.error(f"第 {attempt+1} 次初始化数据加载失败: {str(e)}")
        if attempt < 2:
            time.sleep(1)  # 等待1秒后重试

if not load_success:
    logger.error("数据加载失败，将使用初始空数据")
    chat_messages = []
    private_messages = []
    used_usernames = set()
    USER_SESSIONS = {}


def is_username_available(username):
    """检查用户名是否可用 (不为空且未被使用)"""
    # 基本验证
    if not username or len(username.strip()) == 0:
        return False, "用户名不能为空"
    
    # 长度验证
    if len(username) < 2 or len(username) > 20:
        return False, "用户名长度必须在2-20个字符之间"
    
    # 字符验证（只允许字母、数字、下划线和中文）
    if not re.match(r'^[a-zA-Z0-9_\u4e00-\u9fa5]+$', username):
        return False, "用户名只能包含字母、数字、下划线和中文"
    
    # 唯一性验证
    if username in used_usernames:
        return False, "该用户名已被使用，请选择其他名字"
    
    return True, "用户名可用"


import secrets

def hash_password(password):
    """对密码进行哈希处理, 使用随机盐值增强安全性"""
    # 生成随机盐值
    salt = secrets.token_hex(16)
    # 组合盐值和密码，然后进行哈希
    hashed = hashlib.sha256((salt + password).encode('utf-8')).hexdigest()
    # 返回盐值和哈希值的组合
    return f"{salt}${hashed}"


def get_salt_and_hash(stored_password):
    """从存储的密码中提取盐值和哈希值"""
    parts = stored_password.split('$')
    if len(parts) != 2:
        # 兼容旧格式的密码（没有盐值）
        return '', stored_password
    return parts[0], parts[1]


def verify_user_credentials(username, password):
    """验证用户的用户名和密码"""
    if username not in user_passwords:
        return False, "用户不存在"
    
    stored_password = user_passwords[username]
    salt, hashed = get_salt_and_hash(stored_password)
    
    # 组合盐值和密码，然后进行哈希
    new_hashed = hashlib.sha256((salt + password).encode('utf-8')).hexdigest()
    
    if hashed != new_hashed:
        return False, "密码错误"
    
    return True, "验证成功"


def register_username(client_ip, username, password):
    """注册用户名和密码, 将IP与用户名关联"""
    global online_users, used_usernames, user_passwords
    
    # 先检查用户名是否可用
    available, message = is_username_available(username)
    if not available:
        return False, message
    
    # 验证密码强度
    if len(password) < 6:
        return False, "密码长度必须至少为6个字符"
    
    # 验证是否包含大小写字母
    if not re.search(r'[A-Z]', password) or not re.search(r'[a-z]', password):
        return False, "密码必须包含大小写字母"
    
    # 如果该IP已注册过其他用户名，先移除旧用户名
    if client_ip in online_users:
        old_username = online_users[client_ip]
        if old_username in used_usernames:
            used_usernames.remove(old_username)
        # 同时删除旧用户的密码
        if old_username in user_passwords:
            del user_passwords[old_username]
            save_passwords()
    
    # 注册新用户名和密码
    online_users[client_ip] = username
    used_usernames.add(username)
    user_passwords[username] = hash_password(password)
    
    # 保存用户名和密码到文件
    save_usernames()
    save_passwords()
    
    logger.info(f"用户 {username} (IP: {client_ip}) 注册成功")
    return True, "用户名注册成功"


def unregister_username(username):
    """注销用户名, 释放用户名资源."""
    global online_users, used_usernames
    
    # 从在线用户中移除
    for ip, uname in list(online_users.items()):
        if uname == username:
            del online_users[ip]
    
    # 从已使用用户名中移除
    if username in used_usernames:
        used_usernames.remove(username)
    
    # 保存更新
    save_usernames()
    
    logger.info(f"用户名 {username} 已注销")


class StableUnicodeHTTPRequestHandler(http.server.SimpleHTTPRequestHandler):
    """增强稳定性的HTTP请求处理器, 包含手动输入唯一用户名的聊天功能和私信功能"""

    TIMEOUT = 30
    MUSIC_DIR = os.path.join("D:\\", "code", "audio")  # 更新音乐目录路径
    BINARY_EXTENSIONS = ('.exe', '.zip', '.7z', '.rar', '.bin', '.msi',
                         '.iso', '.tar', '.gz', '.bz2', '.pkg', '.dmg')

    def setup(self):
        """设置连接超时"""
        super().setup()
        self.connection.settimeout(self.TIMEOUT)
        logger.info(f"新连接来自 {self.client_address[0]}")

    def handle(self):
        """增强的请求处理, 添加完整异常捕获"""
        try:
            start_time = time.time()
            super().handle()
            logger.info(
                f"处理请求 {self.path} 来自 {self.client_address[0]} "
                f"耗时 {time.time() - start_time:.2f}秒"
            )
        except socket.timeout:
            logger.warning(f"连接超时 {self.client_address[0]} - {self.path}")
            self.send_error(408, "请求超时")
        except ConnectionResetError:
            logger.warning(f"连接被重置 {self.client_address[0]} - {self.path}")
        except Exception as e:
            logger.error(f"处理请求出错 {self.path}: {str(e)}", exc_info=True)
            try:
                self.send_error(500, "服务器错误: 处理请求时出错")
            except:
                pass

    def finish(self):
        """确保连接正确关闭"""
        try:
            super().finish()
        except Exception as e:
            logger.warning(f"完成请求时出错: {str(e)}")

    def do_POST(self):
        """处理POST请求, 包括聊天消息, 私信和用户名注册"""
        # 不需要CSRF验证的特殊接口
        no_csrf_needed = ['/api/login', '/api/register-username', '/api/check-username']
        
        # 如果不是不需要CSRF验证的接口，则进行验证
        if self.path not in no_csrf_needed:
            # 获取会话ID
            session_id = None
            cookies = self.headers.get('Cookie', '')
            for cookie in cookies.split(';'):
                cookie = cookie.strip()
                if cookie.startswith('session_id='):
                    session_id = cookie[len('session_id='):]
                    break
            
            # 验证CSRF令牌
            if not self.validate_csrf_token(session_id):
                self.send_error(HTTPStatus.FORBIDDEN, "CSRF token invalid or missing")
                return
        
        if self.path == '/api/chat':
            self.handle_chat_post()
        elif self.path == '/api/private-chat':  # 新增私信处理
            self.handle_private_chat_post()
        elif self.path == '/api/register-username':
            self.handle_username_registration()
        elif self.path == '/api/check-username':
            self.handle_username_check()
        elif self.path == '/api/logout':  # 新增退出登录接口
            self.handle_logout()
        elif self.path == '/api/login':  # 新增登录接口
            self.handle_login()
        elif self.path == '/api/submit-feedback':  # 新增反馈提交接口
            self.handle_feedback_submit()
        else:
            self.send_error(HTTPStatus.NOT_FOUND, "Not Found")

    def handle_username_check(self):
        """检查用户名是否可用"""
        try:
            content_length = int(self.headers.get('Content-Length', 0))
            post_data = self.rfile.read(content_length).decode('utf-8')
            data = json.loads(post_data)
            
            if not data or 'username' not in data:
                self.send_error(HTTPStatus.BAD_REQUEST, "无效的请求数据")
                return
                
            username = data['username'].strip()
            available, message = is_username_available(username)
            
            self.send_response(HTTPStatus.OK)
            self.send_header('Content-type', 'application/json')
            self.end_headers()
            self.wfile.write(json.dumps({
                'available': available,
                'message': message
            }).encode('utf-8'))
            
        except json.JSONDecodeError:
            self.send_error(HTTPStatus.BAD_REQUEST, "无效的JSON格式")
        except Exception as e:
            logger.error(f"检查用户名出错: {str(e)}", exc_info=True)
            self.send_error(HTTPStatus.INTERNAL_SERVER_ERROR, "检查用户名时出错")

    def handle_username_registration(self):
        """处理用户名注册 (添加会话Cookie)"""
        try:
            client_ip = self.client_address[0]
            content_length = int(self.headers.get('Content-Length', 0))
            post_data = self.rfile.read(content_length).decode('utf-8')
            data = json.loads(post_data)
            
            if not data or 'username' not in data or 'password' not in data:
                self.send_error(HTTPStatus.BAD_REQUEST, "无效的请求数据，必须包含用户名和密码")
                return
            
            username = data['username'].strip()
            password = data['password']
            
            # 调用注册函数，传入用户名和密码
            success, message = register_username(client_ip, username, password)
            
            if success:
                # 注册成功，创建会话
                session_id, csrf_token = create_session(username)
                
                # 设置会话Cookie和CSRF Cookie
                self.send_response(HTTPStatus.OK)
                self.send_header('Content-type', 'application/json')
                self.send_header('Set-Cookie', f'session_id={session_id}; Path=/; Expires={expires}; HttpOnly; Secure; SameSite=Strict')
                self.send_header('Set-Cookie', f'csrf_token={csrf_token}; Path=/; Expires={expires}; HttpOnly; Secure; SameSite=Strict')
                self.end_headers()
                self.wfile.write(json.dumps({
                    'success': True,
                    'username': username,
                    'message': message
                }).encode('utf-8'))
            else:
                # 注册失败
                self.send_response(HTTPStatus.BAD_REQUEST)
                self.send_header('Content-type', 'application/json')
                self.end_headers()
                self.wfile.write(json.dumps({
                    'success': False,
                    'message': message
                }).encode('utf-8'))
            
        except json.JSONDecodeError:
            self.send_error(HTTPStatus.BAD_REQUEST, "无效的JSON格式")
        except Exception as e:
            logger.error(f"注册用户名出错: {str(e)}", exc_info=True)
            self.send_error(HTTPStatus.INTERNAL_SERVER_ERROR, "注册用户名时出错")
            self.send_header('Set-Cookie', 
                               f'session_id={session_id}; expires={expires}; Path=/; HttpOnly')
            
            self.end_headers()
            self.wfile.write(json.dumps({
                'success': success,
                'message': message,
                'username': username if success else None
            }).encode('utf-8'))
            
        except json.JSONDecodeError:
            self.send_error(HTTPStatus.BAD_REQUEST, "无效的JSON格式")
        except Exception as e:
            logger.error(f"注册用户名出错: {str(e)}", exc_info=True)
            self.send_error(HTTPStatus.INTERNAL_SERVER_ERROR, "注册用户名时出错")

    def handle_feedback_submit(self):
        """处理反馈提交请求"""
        try:
            content_length = int(self.headers.get('Content-Length', 0))
            post_data = self.rfile.read(content_length).decode('utf-8')
            data = json.loads(post_data)

            if not data or 'email' not in data or 'content' not in data or 'name' not in data or 'phone' not in data:
                self.send_error(HTTPStatus.BAD_REQUEST, "无效的请求数据")
                return

            name = data['name'].strip()
            phone = data['phone'].strip()
            email = data['email'].strip()
            content = data['content'].strip()

            # 验证邮箱格式
            import re
            email_regex = r'^[^\s@]+@[^\s@]+\.[^\s@]+$'
            if not re.match(email_regex, email):
                self.send_response(HTTPStatus.BAD_REQUEST)
                self.send_header('Content-type', 'application/json')
                self.end_headers()
                self.wfile.write(json.dumps({
                    'success': False,
                    'message': '无效的邮箱格式'
                }).encode('utf-8'))
                return

            # 验证反馈内容
            if len(content) < 10:
                self.send_response(HTTPStatus.BAD_REQUEST)
                self.send_header('Content-type', 'application/json')
                self.end_headers()
                self.wfile.write(json.dumps({
                    'success': False,
                    'message': '反馈内容至少需要10个字符'
                }).encode('utf-8'))
                return

            # 保存反馈到文件
            import os
            import datetime
            feedback_dir = os.path.join('D:\\', 'code', 'gama-aves')
            if not os.path.exists(feedback_dir):
                os.makedirs(feedback_dir)

            # 创建文本文档
            timestamp = datetime.datetime.now().strftime('%Y%m%d_%H%M%S')
            feedback_file = os.path.join(feedback_dir, f'反馈_{timestamp}.txt')

            with open(feedback_file, 'w', encoding='utf-8') as f:
                f.write(f'姓名: {name}\n')
                f.write(f'手机号: {phone}\n')
                f.write(f'邮箱: {email}\n')
                f.write(f'时间: {datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")}\n')
                f.write('\n反馈内容:\n')
                f.write(content)

            self.send_response(HTTPStatus.OK)
            self.send_header('Content-type', 'application/json')
            self.end_headers()
            self.wfile.write(json.dumps({
                'success': True,
                'message': '反馈提交成功'
            }).encode('utf-8'))

        except json.JSONDecodeError:
            self.send_error(HTTPStatus.BAD_REQUEST, "无效的JSON格式")
        except Exception as e:
            logger.error(f"处理反馈提交出错: {str(e)}", exc_info=True)
            self.send_error(HTTPStatus.INTERNAL_SERVER_ERROR, "处理反馈时出错")

    def handle_login(self):
        """处理用户登录请求"""
        try:
            client_ip = self.client_address[0]
            content_length = int(self.headers.get('Content-Length', 0))
            post_data = self.rfile.read(content_length).decode('utf-8')
            data = json.loads(post_data)
            
            if not data or 'username' not in data or 'password' not in data:
                self.send_error(HTTPStatus.BAD_REQUEST, "无效的请求数据，必须包含用户名和密码")
                return
            
            username = data['username'].strip()
            password = data['password']
            
            # 验证用户凭据
            success, message = verify_user_credentials(username, password)
            
            if success:
                # 登录成功，创建会话
                session_id, csrf_token = create_session(username)
                
                # 更新在线用户
                online_users[client_ip] = username
                used_usernames.add(username)
                save_usernames()
                
                self.send_response(HTTPStatus.OK)
                self.send_header('Content-type', 'application/json')
                self.send_header('Set-Cookie', f'session_id={session_id}; Path=/; Expires={expires}; HttpOnly; Secure; SameSite=Strict')
                self.send_header('Set-Cookie', f'csrf_token={csrf_token}; Path=/; Expires={expires}; HttpOnly; Secure; SameSite=Strict')
                self.send_header('Content-type', 'application/json')
                # 设置为24小时后过期
                expires = (datetime.now() + timedelta(days=1)).strftime(
                    "%a, %d %b %Y %H:%M:%S GMT"
                )
                self.send_header('Set-Cookie', f'session_id={session_id}; Path=/; Expires={expires}; HttpOnly; Secure; SameSite=Strict')
                self.end_headers()
                self.wfile.write(json.dumps({
                    'success': True,
                    'username': username,
                    'message': "登录成功"
                }).encode('utf-8'))
            else:
                # 登录失败
                self.send_response(HTTPStatus.UNAUTHORIZED)
                self.send_header('Content-type', 'application/json')
                self.end_headers()
                self.wfile.write(json.dumps({
                    'success': False,
                    'message': message
                }).encode('utf-8'))
            
        except json.JSONDecodeError:
            self.send_error(HTTPStatus.BAD_REQUEST, "无效的JSON格式")
        except Exception as e:
            logger.error(f"用户登录出错: {str(e)}", exc_info=True)
            self.send_error(HTTPStatus.INTERNAL_SERVER_ERROR, "登录时出错")

    def clear_user_messages(self, username):
        """清空特定用户的聊天记录但不影响其他用户"""
        global chat_messages, private_messages
        
        # 保留其他用户的公开消息，删除该用户的公开消息
        chat_messages = [msg for msg in chat_messages if msg['username'] != username]
        
        # 删除该用户的所有私信（发送和接收）
        private_messages = [msg for msg in private_messages 
                           if msg['sender'] != username and msg['recipient'] != username]
        
        # 保存更新后的消息
        save_messages()
        logger.info(f"已清空用户 {username} 的聊天记录")

    def handle_logout(self):
        """处理用户退出登录"""
        try:
            # 获取当前会话ID
            cookies = self.headers.get('Cookie', '')
            session_id = None
            for cookie in cookies.split(';'):
                if cookie.strip().startswith('session_id='):
                    session_id = cookie.split('=', 1)[1].strip()
                    break
            
            if session_id:
                # 获取用户名
                username = get_username_from_session(session_id)
                
                # 从会话中移除
                if session_id in USER_SESSIONS:
                    del USER_SESSIONS[session_id]
                    save_sessions()
                
                # 注销用户名前先清空该用户的聊天记录
                if username:
                    self.clear_user_messages(username)
                    unregister_username(username)
                
                logger.info(f"用户 {username} 已退出")
                
                # 清除Cookie
                self.send_response(HTTPStatus.OK)
                self.send_header('Content-type', 'application/json')
                self.send_header('Set-Cookie', 
                               'session_id=; expires=Thu, 01 Jan 1970 00:00:00 GMT; Path=/; HttpOnly')
                self.end_headers()
                self.wfile.write(json.dumps({
                    'success': True,
                    'message': '退出成功'
                }).encode('utf-8'))
            else:
                self.send_response(HTTPStatus.BAD_REQUEST)
                self.send_header('Content-type', 'application/json')
                self.end_headers()
                self.wfile.write(json.dumps({
                    'success': False,
                    'message': '未找到会话'
                }).encode('utf-8'))
                
        except Exception as e:
            logger.error(f"退出登录出错: {str(e)}", exc_info=True)
            self.send_error(HTTPStatus.INTERNAL_SERVER_ERROR, "退出登录时出错")

    def get_username(self):
        """从会话Cookie或IP映射获取用户名"""
        # 1. 先检查Cookie中的会话ID
        cookies = self.headers.get('Cookie', '')
        session_id = None
        for cookie in cookies.split(';'):
            if cookie.strip().startswith('session_id='):
                session_id = cookie.split('=', 1)[1].strip()
                break
        
        username = get_username_from_session(session_id) if session_id else None
        return username  # 只返回有效的会话用户名，不回退到IP映射

    def handle_chat_post(self):
        """处理聊天消息提交 (需要已注册用户名)"""
        try:
            username = self.get_username()
            
            # 验证用户是否已注册
            if not username:
                self.send_error(HTTPStatus.UNAUTHORIZED, "请先注册用户名")
                return
                
            content_length = int(self.headers.get('Content-Length', 0))
            post_data = self.rfile.read(content_length).decode('utf-8')
            data = json.loads(post_data)
            
            # 验证消息内容
            if not data or 'message' not in data:
                self.send_error(HTTPStatus.BAD_REQUEST, "无效的请求数据")
                return
                
            message = data['message'].strip()[:500]   # 限制消息长度
            
            if not message:
                self.send_error(HTTPStatus.BAD_REQUEST, "消息不能为空")
                return
                
            # 添加消息到全局列表
            timestamp = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
            chat_message = {
                'username': username,
                'message': message,
                'timestamp': timestamp
            }
            
            global chat_messages
            chat_messages.append(chat_message)
            
            # 限制消息数量
            if len(chat_messages) > MAX_CHAT_MESSAGES:
                chat_messages = chat_messages[-MAX_CHAT_MESSAGES:]
            
            # 保存消息到文件
            save_messages()
                
            # 返回成功响应
            self.send_response(HTTPStatus.OK)
            self.send_header('Content-type', 'application/json')
            self.end_headers()
            self.wfile.write(json.dumps({'status': 'success'}).encode('utf-8'))
            
        except json.JSONDecodeError:
            self.send_error(HTTPStatus.BAD_REQUEST, "无效的JSON格式")
        except Exception as e:
            logger.error(f"处理聊天消息出错: {str(e)}", exc_info=True)
            self.send_error(HTTPStatus.INTERNAL_SERVER_ERROR, "处理聊天消息时出错")

    def handle_private_chat_post(self):
        """处理私信发送"""
        try:
            username = self.get_username()
            
            # 验证用户是否已注册
            if not username:
                self.send_error(HTTPStatus.UNAUTHORIZED, "请先注册用户名")
                return
                
            content_length = int(self.headers.get('Content-Length', 0))
            post_data = self.rfile.read(content_length).decode('utf-8')
            data = json.loads(post_data)
            
            # 验证消息内容和接收人
            if not data or 'message' not in data or 'recipient' not in data:
                self.send_error(HTTPStatus.BAD_REQUEST, "无效的请求数据")
                return
                
            message = data['message'].strip()[:500]   # 限制消息长度
            recipient = data['recipient'].strip()
            
            if not message:
                self.send_error(HTTPStatus.BAD_REQUEST, "消息不能为空")
                return
                
            # 验证接收人是否存在
            if recipient not in used_usernames:
                self.send_error(HTTPStatus.BAD_REQUEST, "接收用户不存在")
                return
                
            # 添加私信到全局列表
            timestamp = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
            private_message = {
                'sender': username,
                'recipient': recipient,
                'message': message,
                'timestamp': timestamp
            }
            
            global private_messages
            private_messages.append(private_message)
            
            # 限制私信数量
            if len(private_messages) > MAX_PRIVATE_MESSAGES:
                private_messages = private_messages[-MAX_PRIVATE_MESSAGES:]
            
            # 保存消息到文件
            save_messages()
                
            # 返回成功响应
            self.send_response(HTTPStatus.OK)
            self.send_header('Content-type', 'application/json')
            self.end_headers()
            self.wfile.write(json.dumps({'status': 'success'}).encode('utf-8'))
            
        except json.JSONDecodeError:
            self.send_error(HTTPStatus.BAD_REQUEST, "无效的JSON格式")
        except Exception as e:
            logger.error(f"处理私信消息出错: {str(e)}", exc_info=True)
            self.send_error(HTTPStatus.INTERNAL_SERVER_ERROR, "处理私信消息时出错")

    def handle_get_online_users(self):
        """获取在线用户列表"""
        try:
            # 验证用户是否已注册
            username = self.get_username()
            if not username:
                self.send_error(HTTPStatus.UNAUTHORIZED, "请先注册用户名")
                return
                
            # 返回排除自己的在线用户列表
            online_users_list = [user for user in used_usernames if user != username]
            
            self.send_response(HTTPStatus.OK)
            self.send_header('Content-type', 'application/json')
            self.end_headers()
            self.wfile.write(json.dumps({
                'users': online_users_list
            }).encode('utf-8'))
            
        except Exception as e:
            # 简化错误处理，不记录详细异常信息
            self.send_error(HTTPStatus.INTERNAL_SERVER_ERROR, "获取在线用户时出错")
            
    # 添加获取系统信息的方法
    def handle_system_info(self):
        """处理获取系统信息的请求"""
        try:
            system_info = get_system_info()
            self.send_response(HTTPStatus.OK)
            self.send_header('Content-type', 'application/json')
            self.end_headers()
            self.wfile.write(json.dumps(system_info, ensure_ascii=False).encode('utf-8'))
        except Exception as e:
            # 简化错误处理，不记录详细异常信息
            self.send_error(HTTPStatus.INTERNAL_SERVER_ERROR, "获取系统信息时出错")

    def do_GET(self):
        """处理GET请求, 支持内容片段返回, 二进制文件下载和聊天功能"""
        # 处理获取聊天消息的请求
        if self.path.startswith('/api/chat'):
            self.handle_chat_get()
            return
        # 处理获取在线用户的请求（GET方法）
        elif self.path == '/api/get-online-users':
            self.handle_get_online_users()
            return
        # 处理获取系统信息的请求
        elif self.path == '/api/system-info':  # 新增系统信息接口
            self.handle_system_info()
            return
        # 处理聊天页面请求
        elif self.path == '/chat':
            self.handle_chat_page()
            return
        # 处理系统信息页面请求
        elif self.path == '/system-info':  # 新增系统信息页面
            self.handle_system_info_page()
            return
            
        if self.headers.get('X-Requested-With') == 'XMLHttpRequest':
            path = self.translate_path(self.path)
            if os.path.isfile(path) and path.lower().endswith(self.BINARY_EXTENSIONS):
                return self.handle_binary_download()
            return self.handle_ajax_request()

        path = self.translate_path(self.path)

        if os.path.isdir(path):
            if not self.path.endswith('/'):
                self.send_response(301)
                self.send_header('Location', self.path + '/')
                self.end_headers()
                return
            return self.list_directory(path)
        else:
            try:
                with open(path, 'rb') as f:
                    self.send_response(200)
                    self.send_header('Content-type', self.guess_type(path))
                    fs = os.fstat(f.fileno())
                    self.send_header('Content-Length', str(fs[6]))
                    self.send_header('Last-Modified', self.date_time_string(fs.st_mtime))

                    if path.lower().endswith(self.BINARY_EXTENSIONS):
                        filename = os.path.basename(path)
                        self._send_content_disposition_header(filename)

                    self.end_headers()
                    self._send_file_in_chunks(f)
                    return
            except FileNotFoundError:
                logger.warning(f"文件未找到: {path} 来自 {self.client_address[0]}")
                self.send_error(404, "文件未找到")
            except Exception as e:
                logger.error(f"处理文件时出错 {path}: {str(e)}")
                self.send_error(500, "服务器错误: 处理文件时出错")

    def handle_chat_get(self):
        """处理获取聊天消息的请求 (包括公开消息和有权查看的私信)"""
        try:
            username = self.get_username()
            if not username:
                # 未登录用户只能看到公开消息
                messages = chat_messages.copy()
                private = []
            else:
                # 已登录用户能看到公开消息和相关私信
                messages = chat_messages.copy()
                # 筛选出自己发送的或发给自己的私信
                private = [
                    msg for msg in private_messages 
                    if msg['sender'] == username or msg['recipient'] == username
                ]
            
            # 支持获取指定时间之后的消息，实现增量更新
            parsed_url = urllib.parse.urlparse(self.path)
            params = urllib.parse.parse_qs(parsed_url.query)
            last_timestamp = params.get('last', [None])[0]
            
            # 过滤公开消息
            if last_timestamp:
                filtered_messages = [msg for msg in messages if msg['timestamp'] > last_timestamp]
                filtered_private = [msg for msg in private if msg['timestamp'] > last_timestamp]
            else:
                filtered_messages = messages
                filtered_private = private
                
            # 返回消息
            self.send_response(HTTPStatus.OK)
            self.send_header('Content-type', 'application/json')
            self.end_headers()
            self.wfile.write(json.dumps({
                'public': filtered_messages,
                'private': filtered_private
            }).encode('utf-8'))
            
        except Exception as e:
            logger.error(f"获取聊天消息出错: {str(e)}", exc_info=True)
            self.send_error(HTTPStatus.INTERNAL_SERVER_ERROR, "获取聊天消息时出错")

    def handle_chat_page(self):
        """返回带用户名注册功能的聊天页面 (自动检测会话状态)"""
        try:
            # 检查用户是否已通过会话登录
            username = self.get_username()
            show_modal = not username  # 未登录则显示注册弹窗
            
            response = []
            response.append('<!DOCTYPE HTML PUBLIC "-//W3C//DTD HTML 4.01//EN" '
                            '"http://www.w3.org/TR/html4/strict.dtd">')
            response.append('<html>\n<head>')
            response.append('<meta http-equiv="Content-Type" content="text/html; charset=utf-8">')
            response.append('<title>世界聊天 - 程序网站</title>')
            response.append(
                '<link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/6.0.0/css/all.min.css">')
            response.append('''
                <style>
                    :root {
                        --primary: #3498db;
                        --primary-dark: #2980b9;
                        --primary-dark: #2980b9;
                        --secondary: #e74c3c;
                        --light-bg: #f0f0f0;
                        --chat-bg: #e5ddd5;
                        --my-bubble: #95ec69;
                        --other-bubble: #ffffff;
                        --private-bg: #e1bee7;
                        --text-primary: #2c3e50;
                        --text-secondary: #7f8c8d;
                        --border-light: #eee;
                        --radius: 8px;
                    }
                    
                    body {
                        font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif;
                        max-width: 95%;
                        margin: 0 auto;
                        padding: 20px;
                        background-color: var(--light-bg);
                        color: var(--text-primary);
                    }
                    
                    #chat-container {
                        background-color: white;
                        border-radius: var(--radius);
                        box-shadow: 0 5px 15px rgba(0,0,0,0.1);
                        overflow: hidden;
                        display: none; /* 初始隐藏聊天界面，直到用户名注册完成 */
                    }
                    
                    #chat-header {
                        background-color: var(--primary);
                        color: white;
                        padding: 15px 20px;
                        font-size: 1.2em;
                        font-weight: bold;
                        display: flex;
                        justify-content: space-between;
                        align-items: center;
                    }
                    
                    .user-info {
                        font-size: 0.8em;
                        background-color: rgba(255,255,255,0.2);
                        padding: 3px 8px;
                        border-radius: 12px;
                    }
                    
                    #chat-container {
                        max-width: 900px;
                        width: 100%;
                        margin: 0 auto;
                    }

                    #messages-container {
                        display: flex;
                        flex-direction: column;
                        height: 675px; /* 宽度900px的4:3比例 */
                    }
                    
                    .message-tabs {
                        display: flex;
                        border-bottom: 1px solid #e0e0e0;
                    }
                    
                    .message-tab {
                        flex: 1;
                        padding: 10px;
                        background-color: #f5f5f5;
                        border: none;
                        cursor: pointer;
                        font-weight: 500;
                        transition: all 0.3s;
                    }
                    
                    .message-tab.active {
                        background-color: white;
                        border-bottom: 3px solid var(--primary);
                    }
                    
                    .message-tab:hover:not(.active) {
                        background-color: #e9e9e9;
                    }
                    
                    .message-area {
                        flex: 1;
                        overflow-y: auto;
                        padding: 20px;
                        background-color: var(--chat-bg);
                        background-image: url("data:image/svg+xml,%3Csvg width='60' height='60' viewBox='0 0 60 60' xmlns='http://www.w3.org/2000/svg'%3E%3Cg fill='none' fill-rule='evenodd'%3E%3Cg fill='%239C92AC' fill-opacity='0.05'%3E%3Cpath d='M36 34v-4h-2v4h-4v2h4v4h2v-4h4v-2h-4zm0-30V0h-2v4h-4v2h4v4h2V6h4V4h-4zM6 34v-4H4v4H0v2h4v4h2v-4h4v-2H6zM6 4V0H4v4H0v2h4v4h2V6h4V4H6z'/%3E%3C/g%3E%3C/g%3E%3C/svg%3E");
                        display: none;
                    }
                    
                    .message-area.active {
                        display: block;
                    }
                    
                    .message {
                        margin-bottom: 15px;
                        max-width: 70%;
                        clear: both;
                        animation: fadeIn 0.3s ease;
                    }
                    
                    @keyframes fadeIn {
                        from { opacity: 0; transform: translateY(10px); }
                        to { opacity: 1; transform: translateY(0); }
                    }
                    
                    .my-message {
                        float: right;
                    }
                    
                    .other-message {
                        float: left;
                    }
                    
                    .message .username {
                        font-size: 0.8em;
                        font-weight: 500;
                        margin: 0 10px 3px;
                    }
                    
                    .message .bubble {
                        padding: 10px 15px;
                        border-radius: 18px;
                        position: relative;
                        word-wrap: break-word;
                        line-height: 1.5;
                    }
                    
                    .my-message .bubble {
                        background-color: var(--my-bubble);
                        border-top-right-radius: 4px;
                    }
                    
                    .other-message .bubble {
                        background-color: var(--other-bubble);
                        border-top-left-radius: 4px;
                    }
                    
                    .private-message .bubble {
                        background-color: var(--private-bg);
                    }
                    
                    .message .meta {
                        font-size: 0.7em;
                        color: var(--text-secondary);
                        margin: 4px 15px;
                    }
                    
                    .my-message .meta {
                        text-align: right;
                    }
                    
                    .other-message .meta {
                        text-align: left;
                    }
                    
                    #input-area {
                        padding: 15px;
                        background-color: white;
                        border-top: 1px solid #e0e0e0;
                    }
                    
                    .input-container {
                        display: flex;
                        gap: 10px;
                    }
                    
                    #message-input {
                        flex: 1;
                        padding: 12px 15px;
                        border: 1px solid #ddd;
                        border-radius: 25px;
                        resize: none;
                        min-height: 40px;
                        max-height: 120px;
                        font-family: inherit;
                        font-size: 1em;
                        box-shadow: inset 0 1px 2px rgba(0,0,0,0.05);
                    }
                    
                    #message-input:focus {
                        outline: none;
                        border-color: var(--primary);
                    }
                    
                    #send-button {
                        background-color: var(--primary);
                        color: white;
                        border: none;
                        padding: 0 20px;
                        border-radius: 25px;
                        cursor: pointer;
                        font-weight: bold;
                        transition: background-color 0.3s, transform 0.1s;
                        display: inline-flex;
                        align-items: center;
                        justify-content: center;
                    }
                    
                    #send-button:hover {
                        background-color: var(--primary-dark);
                    }
                    
                    #send-button:active {
                        transform: scale(0.95);
                    }
                    
                    .status {
                        color: var(--text-secondary);
                        font-size: 0.9em;
                        text-align: center;
                        margin: 10px 0;
                        padding: 8px;
                        border-radius: var(--radius);
                        background-color: #f0f7ff;
                    }
                    
                    .back-link {
                        display: inline-block;
                        margin-bottom: 15px;
                        color: var(--primary);
                        text-decoration: none;
                        font-weight: 500;
                    }
                    
                    .back-link:hover {
                        text-decoration: underline;
                    }

                    #feedback-button:hover {
                        background-color: var(--primary-dark);
                        transform: translateY(-2px);
                        box-shadow: 0 4px 8px rgba(0,0,0,0.1);
                        transition: all 0.3s ease;
                    }
                    
                    .message-count {
                        font-size: 0.8em;
                        background-color: rgba(255,255,255,0.2);
                        padding: 3px 8px;
                        border-radius: 12px;
                    }
                    
                    /* 用户名注册弹窗 */
                    #username-modal {
                        position: fixed;
                        top: 0;
                        left: 0;
                        width: 100%;
                        height: 100%;
                        background-color: rgba(0,0,0,0.5);
                        display: flex;
                        justify-content: center;
                        align-items: center;
                        z-index: 1000;
                    }
                    
                    .modal-content {
                        background-color: white;
                        padding: 30px;
                        border-radius: var(--radius);
                        width: 90%;
                        max-width: 400px;
                        box-shadow: 0 5px 25px rgba(0,0,0,0.2);
                    }
                    
                    .modal-content h2 {
                        margin-top: 0;
                        color: var(--text-primary);
                        text-align: center;
                    }
                    
                    .username-input-group {
                        margin-bottom: 20px;
                    }

                    .form-input {
                        padding: 12px 15px;
                        border: 1px solid #ddd;
                        border-radius: var(--radius);
                        font-size: 1em;
                        width: 100%;
                        box-sizing: border-box;
                        margin-bottom: 8px;
                    }
                    
                    .form-input:focus {
                        outline: none;
                        border-color: var(--primary);
                    }
                    
                    .username-hint {
                        font-size: 0.85em;
                        color: var(--text-secondary);
                        margin-bottom: 15px;
                        text-align: center;
                    }
                    
                    .username-message {
                    font-size: 0.9em;
                    height: 24px;
                    margin-bottom: 20px;
                    text-align: center;
                    padding: 4px 0;
                    border-radius: 4px;
                }
                    
                    .username-error {
                        color: var(--secondary);
                    }
                    
                    .username-success {
                        color: #27ae60;
                    }
                    
                    #register-button {
                        width: 100%;
                        padding: 12px;
                        background-color: var(--primary);
                        color: white;
                        border: none;
                        border-radius: var(--radius);
                        font-size: 1em;
                        font-weight: 500;
                        cursor: pointer;
                        transition: background-color 0.3s;
                    }
                    
                    #register-button:hover {
                        background-color: var(--primary-dark);
                    }
                    
                    #register-button:disabled {
                        background-color: #bdc3c7;
                        cursor: not-allowed;
                    }
                    
                    /* 滚动条美化 */
                    .message-area::-webkit-scrollbar {
                        width: 6px;
                    }
                    
                    .message-area::-webkit-scrollbar-track {
                        background: transparent;
                    }
                    
                    .message-area::-webkit-scrollbar-thumb {
                        background-color: rgba(0,0,0,0.2);
                        border-radius: 3px;
                    }
                    
                    .message-area::-webkit-scrollbar-thumb:hover {
                        background-color: rgba(0,0,0,0.3);
                    }

                    /* 私信样式 */
                    .private-indicator {
                        font-size: 0.7em;
                        color: #9c27b0;
                        margin-right: 5px;
                    }

                    .message .recipient {
                        font-size: 0.7em;
                        color: #9c27b0;
                        margin-left: 5px;
                    }

                    /* 消息类型选择器 */
                    .message-type-selector {
                        display: flex;
                        margin-bottom: 10px;
                        border: 1px solid #ddd;
                        border-radius: 20px;
                        overflow: hidden;
                    }

                    .message-type-button {
                        flex: 1;
                        padding: 5px 0;
                        background-color: white;
                        border: none;
                        cursor: pointer;
                        font-size: 0.9em;
                        transition: background-color 0.2s;
                    }

                    .message-type-button.active {
                        background-color: var(--primary);
                        color: white;
                    }

                    .recipient-selector {
                        display: none;
                        margin-bottom: 10px;
                    }

                    .recipient-selector.active {
                        display: block;
                    }

                    #recipient-select {
                        width: 100%;
                        padding: 8px 10px;
                        border: 1px solid #ddd;
                        border-radius: 20px;
                        font-size: 0.9em;
                    }

                    /* 退出按钮样式 */
                    #logout-button {
                        background-color: transparent;
                        color: white;
                        border: none;
                        margin-left: 10px;
                        cursor: pointer;
                        font-size: 0.8em;
                        opacity: 0.7;
                        transition: opacity 0.3s;
                    }

                    #logout-button:hover {
                        opacity: 1;
                        text-decoration: underline;
                    }
                /* 反馈弹窗样式 */
                #feedback-modal {
                    position: fixed;
                    top: 0;
                    left: 0;
                    width: 100%;
                    height: 100%;
                    background-color: rgba(0,0,0,0.5);
                    display: flex;
                    justify-content: center;
                    align-items: center;
                    z-index: 1000;
                }

                .modal-content {
                    background-color: white;
                    padding: 30px;
                    width: 80%;
                    max-width: 500px;
                    border-radius: 12px;
                    box-shadow: 0 10px 25px rgba(0, 0, 0, 0.1);
                    transition: transform 0.3s ease;
                }

                .modal-content:hover {
                    transform: translateY(-5px);
                }

                .modal-content h2 {
                    color: #2c3e50;
                    margin-top: 0;
                    margin-bottom: 25px;
                    font-size: 1.5rem;
                    text-align: center;
                    font-weight: 600;
                    padding-bottom: 15px;
                    border-bottom: 1px solid #f0f0f0;
                }

                .form-input-container {
                    margin-bottom: 20px;
                    position: relative;
                }

                .form-input {
                    width: 100%;
                    padding: 12px 15px;
                    border: 1px solid #e0e0e0;
                    border-radius: 8px;
                    box-sizing: border-box;
                    font-size: 14px;
                    transition: all 0.3s ease;
                }

                .form-input:focus {
                    border-color: var(--primary);
                    outline: none;
                    box-shadow: 0 0 0 3px rgba(34, 167, 240, 0.1);
                }

                textarea.form-input {
                    resize: vertical;
                    min-height: 100px;
                }

                #submit-feedback {
                    width: 100%;
                    padding: 12px;
                    background-color: var(--primary);
                    color: white;
                    border: none;
                    border-radius: 8px;
                    cursor: pointer;
                    font-size: 16px;
                    font-weight: 500;
                    transition: all 0.3s ease;
                }

                #submit-feedback:hover {
                    background-color: var(--primary-dark);
                    transform: translateY(-2px);
                    box-shadow: 0 4px 12px rgba(34, 167, 240, 0.2);
                }

                #cancel-feedback {
                    width: 100%;
                    padding: 12px;
                    background-color: #f8f9fa;
                    color: #495057;
                    border: 1px solid #e9ecef;
                    border-radius: 8px;
                    cursor: pointer;
                    margin-top: 15px;
                    font-size: 16px;
                    transition: all 0.3s ease;
                }

                #cancel-feedback:hover {
                    background-color: #e9ecef;
                    border-color: #dee2e6;
                }

                /* 登录弹窗样式 */
                #login-modal {
                    position: fixed;
                    top: 0;
                    left: 0;
                    width: 100%;
                    height: 100%;
                    background-color: rgba(0,0,0,0.5);
                    display: none;
                    justify-content: center;
                    align-items: center;
                    z-index: 1000;
                }

                .login-message {
                    font-size: 0.9em;
                    height: 20px;
                    margin-bottom: 15px;
                    text-align: center;
                }

                .login-error {
                    color: var(--secondary);
                }

                .login-success {
                    color: #27ae60;
                }

                #login-button {
                    width: 100%;
                    padding: 12px;
                    background-color: var(--primary);
                    color: white;
                    border: none;
                    border-radius: var(--radius);
                    font-size: 1em;
                    font-weight: 500;
                    cursor: pointer;
                    transition: background-color 0.3s;
                }

                #login-button:hover {
                    background-color: var(--primary-dark);
                }

                #login-button:disabled {
                    background-color: #bdc3c7;
                    cursor: not-allowed;
                }
            </style>
            ''')
            response.append('</head>')
            response.append('<body>')
            response.append('')
            
            # 用户名注册弹窗（根据会话状态决定是否显示）
            response.append(f'''
                <div id="username-modal" style="display: {'flex' if show_modal else 'none'}">
                    <div class="modal-content">
                        <h2>请设置您的用户名</h2>
                        <div class="username-input-group">
                            <div class="form-input-container">
                                <input type="text" id="username-input" placeholder="请输入用户名" 
                                       minlength="2" maxlength="20" autocomplete="off" class="form-input">
                                <div class="input-right-space"></div>
                            </div>
                            <div class="username-hint">
                                用户名长度为2-20个字符，可包含字母、数字、下划线和中文
                            </div>
                            <div class="form-input-container">
                                <input type="password" id="password-input" placeholder="请输入密码" 
                                       minlength="6" autocomplete="new-password" class="form-input">
                                <div class="input-right-space"></div>
                            </div>
                            <div class="username-hint">
                                密码长度至少为6个字符，且必须包含大小写字母
                            </div>
                            <div class="username-message" id="username-message"></div>
                            <button id="register-button">确认注册</button>
                        </div>
                    </div>
                </div>
            ''')

            # 反馈弹窗
            response.append('''
                <div id="feedback-modal" style="display: none;">
                    <div class="modal-content">
                        <h2>意见反馈</h2>
                        <div class="username-input-group">
                            <div class="form-input-container">
                                <input type="text" id="feedback-name" placeholder="请输入您的姓名" 
                                       required class="form-input">
                                <div class="input-right-space"></div>
                            </div>
                            <div class="form-input-container">
                                <input type="tel" id="feedback-phone" placeholder="请输入您的手机号" 
                                       required class="form-input" pattern="^1[3-9]\\d{9}$">
                                <div class="input-right-space"></div>
                            </div>
                            <div class="form-input-container">
                                <input type="email" id="feedback-email" placeholder="请输入您的邮箱" 
                                       required class="form-input">
                                <div class="input-right-space"></div>
                            </div>
                            <div class="form-input-container">
                                <textarea id="feedback-content" placeholder="请输入您的反馈内容" 
                                          rows="5" required class="form-input"></textarea>
                                <div class="input-right-space"></div>
                            </div>
                            <div class="username-message" id="feedback-message"></div>
                            <button id="submit-feedback">提交反馈</button>
                            <button id="cancel-feedback" style="margin-top: 10px; background-color: #bdc3c7;">取消</button>
                        </div>
                    </div>
                </div>
            ''')

            # 登录弹窗
            response.append('''
                <div id="login-modal" style="display: none;">
                    <div class="modal-content">
                        <h2>请登录</h2>
                        <div class="username-input-group">
                            <div class="form-input-container">
                                <input type="text" id="login-username-input" placeholder="请输入用户名" 
                                       minlength="2" maxlength="20" autocomplete="off" class="form-input">
                                <div class="input-right-space"></div>
                            </div>
                            <div class="form-input-container">
                                <input type="password" id="login-password-input" placeholder="请输入密码" 
                                       minlength="6" autocomplete="current-password" class="form-input">
                                <div class="input-right-space"></div>
                            </div>
                            <div class="login-message" id="login-message"></div>
                            <button id="login-button">登录</button>
                        </div>
                    </div>
                </div>
            ''')
            
            # 聊天界面（初始隐藏）
            response.append('<div id="chat-container">')
            response.append('''  <div id="chat-header">
      <a href="/" class="back-link" style="color: white; margin-right: 10px; text-decoration: none;"><i class="fas fa-arrow-left"></i> 返回主页</a>''')
            response.append('      <div>')
            response.append(f'          <button id="feedback-button" style="margin-right: 10px; background-color: var(--primary); color: white; border: none; padding: 8px 16px; border-radius: 4px; cursor: pointer; font-weight: bold;"><i class="fas fa-comment-dots"></i> 反馈</button>')
            response.append(f'          <span class="message-count" id="message-count">{len(chat_messages) + len(private_messages)}</span>')
            response.append('          <span class="user-info" id="current-user"></span>')
            response.append('          <button id="logout-button" title="退出登录"><i class="fas fa-sign-out-alt"></i> 退出</button>')
            response.append('      </div>')
            response.append('  </div>')
            response.append('  <div id="messages-container">')
            response.append('      <div class="message-tabs">')
            response.append('          <button class="message-tab active" data-tab="public" disabled>公开消息</button>')
            response.append('          <button class="message-tab" data-tab="private" disabled>私信</button>')
            response.append('      </div>')
            response.append('      <div class="message-area active" id="public-messages"></div>')
            response.append('      <div class="message-area" id="private-messages"></div>')
            response.append('  </div>')
            response.append('  <div class="chat-title" style="padding: 10px 20px; font-size: 1.2em; font-weight: bold; color: var(--text-primary);">世界聊天</div>')
            response.append('  <div id="input-area">')
            response.append('      <div class="message-type-selector">')
            response.append('          <button class="message-type-button active" data-type="public">公开消息</button>')
            response.append('          <button class="message-type-button" data-type="private">私信</button>')
            response.append('      </div>')
            response.append('      <div class="recipient-selector">')
            response.append('          <select id="recipient-select">')
            response.append('              <option value="">选择接收人...</option>')
            response.append('              <!-- 由JavaScript动态填充 -->')
            response.append('          </select>')
            response.append('      </div>')
            response.append('      <div class="input-container">')
            response.append('          <textarea id="message-input" placeholder="请输入消息内容..."></textarea>')
            response.append('          <button id="send-button"><i class="fas fa-paper-plane"></i></button>')
            response.append('      </div>')
            response.append('  </div>')
            response.append('</div>')
            response.append('''
                <script>
                    let lastTimestamp = null;
                    let isConnected = false;
                    let checkInterval;
                    let currentUsername = null;
                    
                    // 私信相关变量
                    let messageType = 'public'; // 默认发送公开消息
                    let selectedRecipient = '';
                    
                    // 初始化页面
                    window.onload = function() {
                        // 绑定用户名注册相关事件
                        bindUsernameEvents();
                        
                        // 绑定登录相关事件
                        bindLoginEvents();
                        
                        // 绑定消息类型选择事件
                        bindMessageTypeEvents();
                        
                        // 绑定消息标签切换事件
                        bindMessageTabEvents();
                        
                        // 绑定退出按钮事件
                    document.getElementById('logout-button').addEventListener('click', logoutUser);

                    // 绑定反馈按钮事件
                    document.getElementById('feedback-button').addEventListener('click', function() {
                        const feedbackModal = document.getElementById('feedback-modal');
                        feedbackModal.style.display = 'flex';
                    });

                    // 绑定取消反馈按钮事件
                    document.getElementById('cancel-feedback').addEventListener('click', function() {
                        const feedbackModal = document.getElementById('feedback-modal');
                        feedbackModal.style.display = 'none';
                    });

                    // 绑定取消反馈按钮事件
                    document.getElementById('cancel-feedback').addEventListener('click', function() {
                        const feedbackModal = document.getElementById('feedback-modal');
                        feedbackModal.classList.remove('active');
                        document.getElementById('feedback-message').textContent = '';
                    });

                    // 绑定提交反馈按钮事件
                    document.getElementById('submit-feedback').addEventListener('click', submitFeedback);
                    };

                    // 绑定登录相关事件
                    function bindLoginEvents() {
                        const loginUsernameInput = document.getElementById('login-username-input');
                        const loginPasswordInput = document.getElementById('login-password-input');
                        const loginButton = document.getElementById('login-button');
                        const loginMessage = document.getElementById('login-message');
                        
                        // 实时检查登录用户名
                        loginUsernameInput.addEventListener('input', function() {
                            const username = this.value.trim();
                            
                            if (username.length < 2 || username.length > 20) {
                                loginMessage.textContent = '用户名长度必须在2-20个字符之间';
                                loginMessage.className = 'login-message login-error';
                                loginButton.disabled = true;
                                return;
                            }
                            
                            // 字符验证
                            const regex = /^[a-zA-Z0-9_一-龥]+$/;
                            if (!regex.test(username)) {
                                loginMessage.textContent = '用户名只能包含字母、数字、下划线和中文';
                                loginMessage.className = 'login-message login-error';
                                loginButton.disabled = true;
                                return;
                            }
                            
                            loginMessage.textContent = '';
                            loginButton.disabled = false;
                        });
                        
                        // 实时检查登录密码
                        loginPasswordInput.addEventListener('input', function() {
                            const password = this.value;
                            
                            if (password.length < 6) {
                                loginMessage.textContent = '密码长度必须至少为6个字符，且必须包含大小写字母';
                                loginMessage.className = 'login-message login-error';
                                loginButton.disabled = true;
                                return;
                            }
                            
                            loginMessage.textContent = '';
                            loginButton.disabled = false;
                        });
                        
                        // 登录按钮点击事件
                        loginButton.addEventListener('click', function() {
                            const username = loginUsernameInput.value.trim();
                            const password = loginPasswordInput.value;
                            
                            if (!username || username.length < 2 || username.length > 20) {
                                loginMessage.textContent = '请输入有效的用户名';
                                loginMessage.className = 'login-message login-error';
                                return;
                            }
                            
                            if (!password || password.length < 6) {
                                loginMessage.textContent = '请输入有效的密码';
                                loginMessage.className = 'login-message login-error';
                                return;
                            }
                            
                            login(username, password);
                        });
                        
                        // 回车键登录
                        loginUsernameInput.addEventListener('keypress', function(e) {
                            if (e.key === 'Enter' && !loginButton.disabled) {
                                e.preventDefault();
                                loginPasswordInput.focus();
                            }
                        });
                        
                        loginPasswordInput.addEventListener('keypress', function(e) {
                            if (e.key === 'Enter' && !loginButton.disabled) {
                                e.preventDefault();
                                loginButton.click();
                            }
                        });
                    }
                    
                    // 绑定消息标签切换事件 - 现在标签已禁用，此函数仅用于内部状态更新
                    function bindMessageTabEvents() {
                        // 空函数，因为标签已禁用，不需要绑定点击事件
                    }

                    // 更新消息标签状态
                    function updateMessageTabState(tabId) {
                        const tabs = document.querySelectorAll('.message-tab');
                        tabs.forEach(tab => {
                            if (tab.getAttribute('data-tab') === tabId) {
                                tab.classList.add('active');
                            } else {
                                tab.classList.remove('active');
                            }
                        });
                    }
                    
                    // 提交反馈
                    function submitFeedback() {
                        const name = document.getElementById('feedback-name').value.trim();
                        const phone = document.getElementById('feedback-phone').value.trim();
                        const email = document.getElementById('feedback-email').value.trim();
                        const content = document.getElementById('feedback-content').value.trim();
                        const feedbackMessage = document.getElementById('feedback-message');

                        // 验证姓名
                        if (!name || name.length < 2) {
                            feedbackMessage.textContent = '请输入您的姓名，至少2个字符';
                            feedbackMessage.className = 'username-message error';
                            return;
                        }

                        // 验证手机号
                        // 修复无效转义序列问题
                        const phoneRegex = /^1[3-9]\d{9}$/;
                        if (!phone || !phoneRegex.test(phone)) {
                            feedbackMessage.textContent = '请输入有效的手机号';
                            feedbackMessage.className = 'username-message error';
                            return;
                        }

                        // 验证邮箱
                        const emailRegex = /^[^\s@]+@[^\s@]+\.[^\s@]+$/;
                        if (!emailRegex.test(email)) {
                            feedbackMessage.textContent = '请输入有效的邮箱地址';
                            feedbackMessage.className = 'username-message error';
                            return;
                        }

                        // 验证反馈内容
                        if (!content || content.length < 10) {
                            feedbackMessage.textContent = '反馈内容至少需要10个字符';
                            feedbackMessage.className = 'username-message error';
                            return;
                        }

                        // 获取CSRF令牌
                        function getCSRFToken() {
                            const cookieValue = document.cookie
                                .split('; ')
                                .find(row => row.startsWith('csrf_token='))
                                ?.split('=')[1];
                            return cookieValue;
                        }

                        // 发送反馈到服务器
                        fetch('/api/submit-feedback', {
                            method: 'POST',
                            headers: {
                                'Content-Type': 'application/json',
                                'X-CSRF-Token': getCSRFToken()
                            },
                            body: JSON.stringify({
                                name: name,
                                phone: phone,
                                email: email,
                                content: content
                            })
                        })
                        .then(response => response.json())
                        .then(data => {
                            if (data.success) {
                                feedbackMessage.textContent = '反馈提交成功！感谢您的建议！';
                                feedbackMessage.className = 'username-message success';
                                setTimeout(() => {
                                    document.getElementById('feedback-modal').style.display = 'none';
                                    document.getElementById('feedback-email').value = '';
                                    document.getElementById('feedback-content').value = '';
                                    feedbackMessage.textContent = '';
                                }, 2000);
                            } else {
                                feedbackMessage.textContent = '提交失败：' + data.message;
                                feedbackMessage.className = 'username-message error';
                            }
                        })
                        .catch(error => {
                            console.error('提交反馈出错:', error);
                            feedbackMessage.textContent = '提交失败，请稍后再试';
                            feedbackMessage.className = 'username-message error';
                        });
                    }

                    // 绑定用户名注册事件
                    function bindUsernameEvents() {
                        const usernameInput = document.getElementById('username-input');
                        const usernameMessage = document.getElementById('username-message');
                        const registerButton = document.getElementById('register-button');
                        
                        // 实时检查用户名
                        usernameInput.addEventListener('input', function() {
                            const username = this.value.trim();
                            
                            if (username.length < 2 || username.length > 20) {
                                usernameMessage.textContent = '用户名长度必须在2-20个字符之间';
                                usernameMessage.className = 'username-message username-error';
                                registerButton.disabled = true;
                                return;
                            }
                            
                            // 字符验证
                            const regex = /^[a-zA-Z0-9_\u4e00-\u9fa5]+$/;
                            if (!regex.test(username)) {
                                usernameMessage.textContent = '用户名只能包含字母、数字、下划线和中文';
                                usernameMessage.className = 'username-message username-error';
                                registerButton.disabled = true;
                                return;
                            }
                            
                            // 检查用户名是否已被使用
                            checkUsernameAvailability(username);
                        });
                        
                        // 注册按钮点击事件
                        registerButton.addEventListener('click', function() {
                            const username = usernameInput.value.trim();
                            if (username) {
                                registerUsername(username);
                            }
                        });
                        
                        // 回车键注册
                        usernameInput.addEventListener('keypress', function(e) {
                            if (e.key === 'Enter' && !registerButton.disabled) {
                                e.preventDefault();
                                registerUsername(this.value.trim());
                            }
                        });
                    }
                    
                    // 绑定消息类型选择事件
                    function bindMessageTypeEvents() {
                        const typeButtons = document.querySelectorAll('.message-type-button');
                        const recipientSelector = document.querySelector('.recipient-selector');
                        const recipientSelect = document.getElementById('recipient-select');
                        
                        typeButtons.forEach(button => {
                            button.addEventListener('click', function() {
                                // 更新按钮状态
                                typeButtons.forEach(btn => btn.classList.remove('active'));
                                this.classList.add('active');
                                
                                // 更新消息类型
                                messageType = this.getAttribute('data-type');
                                
                                // 显示/隐藏接收人选择器
                                if (messageType === 'private') {
                                    recipientSelector.classList.add('active');
                                    loadOnlineUsers(); // 刷新在线用户列表
                                } else {
                                    recipientSelector.classList.remove('active');
                                    selectedRecipient = '';
                                }
                                 
                                // 调用更新消息标签状态的函数
                        updateMessageTabState(messageType);
                                 
                                // 同步更新消息区域
                                document.querySelectorAll('.message-area').forEach(area => {
                                    area.classList.remove('active');
                                });
                                document.getElementById(`${messageType}-messages`).classList.add('active');
                            });
                        });
                        
                        // 接收人选择事件
                        recipientSelect.addEventListener('change', function() {
                            selectedRecipient = this.value;
                        });
                    }
                    
                    // 检查用户名是否可用
                    function checkUsernameAvailability(username) {
                        fetch('/api/check-username', {
                            method: 'POST',
                            headers: {
                                'Content-Type': 'application/json',
                            },
                            body: JSON.stringify({ username: username })
                        })
                        .then(response => response.json())
                        .then(data => {
                            const usernameMessage = document.getElementById('username-message');
                            const registerButton = document.getElementById('register-button');
                            
                            if (data.available) {
                                usernameMessage.textContent = '用户名可用';
                                usernameMessage.className = 'username-message username-success';
                                registerButton.disabled = false;
                            } else {
                                usernameMessage.textContent = data.message;
                                usernameMessage.className = 'username-message username-error';
                                registerButton.disabled = true;
                            }
                        })
                        .catch(error => {
                            console.error('检查用户名失败:', error);
                        });
                    }
                    
                    // 注册用户名
                    function registerUsername(username) {
                        const password = document.getElementById('password-input').value;
                        
                        // 验证密码
                        if (!password || password.length < 6) {
                            const usernameMessage = document.getElementById('username-message');
                            usernameMessage.textContent = '密码长度必须至少为6个字符，且必须包含大小写字母';
                            usernameMessage.className = 'username-message username-error';
                            return;
                        }
                        
                        fetch('/api/register-username', {
                            method: 'POST',
                            headers: {
                                'Content-Type': 'application/json',
                            },
                            body: JSON.stringify({ username: username, password: password })
                        })
                        .then(response => response.json())
                        .then(data => {
                            if (data.success) {
                                // 注册成功，显示登录弹窗
                                document.getElementById('username-modal').style.display = 'none';
                                document.getElementById('login-modal').style.display = 'flex';
                                
                                // 显示注册成功提示
                                const loginMessage = document.getElementById('login-message');
                                loginMessage.textContent = '注册成功，请登录';
                                loginMessage.className = 'login-message login-success';
                            } else {
                                // 注册失败，显示错误信息
                                const usernameMessage = document.getElementById('username-message');
                                usernameMessage.textContent = data.message;
                                usernameMessage.className = 'username-message username-error';
                            }
                        })
                        .catch(error => {
                            console.error('注册用户名失败:', error);
                            alert('注册失败，请重试');
                        });
                    }

                    // 登录函数
                    function login(username, password) {
                        fetch('/api/login', {
                            method: 'POST',
                            headers: {
                                'Content-Type': 'application/json',
                            },
                            body: JSON.stringify({ username: username, password: password })
                        })
                        .then(response => response.json())
                        .then(data => {
                            if (data.success) {
                                // 登录成功，保存用户名并进入聊天
                                currentUsername = data.username;
                                document.getElementById('current-user').textContent = currentUsername;
                                
                                // 隐藏登录弹窗，显示聊天界面
                                document.getElementById('login-modal').style.display = 'none';
                                document.getElementById('chat-container').style.display = 'block';
                                
                                // 初始化聊天
                                initChat();
                            } else {
                                // 登录失败，显示错误信息
                                const loginMessage = document.getElementById('login-message');
                                loginMessage.textContent = data.message;
                                loginMessage.className = 'login-message login-error';
                            }
                        })
                        .catch(error => {
                            console.error('登录失败:', error);
                            alert('登录失败，请重试');
                        });
                    }
                    
                    // 加载在线用户列表
                    function loadOnlineUsers() {
                        if (!isConnected || !currentUsername) return;
                        
                        fetch('/api/get-online-users')
                            .then(response => {
                                if (!response.ok) throw new Error('获取用户列表失败');
                                return response.json();
                            })
                            .then(data => {
                                const select = document.getElementById('recipient-select');
                                // 保存当前选中值
                                const currentValue = select.value;
                                
                                // 清空现有选项（保留第一个提示选项）
                                while (select.options.length > 1) {
                                    select.remove(1);
                                }
                                
                                // 添加在线用户
                                data.users.forEach(user => {
                                    const option = document.createElement('option');
                                    option.value = user;
                                    option.textContent = user;
                                    select.appendChild(option);
                                });
                                
                                // 恢复选中值
                                if (currentValue) {
                                    select.value = currentValue;
                                    selectedRecipient = currentValue;
                                }
                            })
                            .catch(error => {
                                console.error('加载在线用户失败:', error);
                                setTimeout(loadOnlineUsers, 5000); // 5秒后重试
                            });
                    }
                    
                    // 初始化聊天功能
                    function initChat() {
                        // 加载消息
                        loadMessages();
                        // 设置发送按钮点击事件
                        document.getElementById('send-button').addEventListener('click', sendMessage);
                        // 设置回车键发送消息
                        document.getElementById('message-input').addEventListener('keypress', function(e) {
                            if (e.key === 'Enter' && !e.shiftKey) {
                                e.preventDefault();
                                sendMessage();
                            }
                        });
                    }
                    
                    // 加载消息
                    function loadMessages() {
                        fetch('/api/chat')
                            .then(response => {
                                if (!response.ok) {
                                    throw new Error('网络响应不正常');
                                }
                                return response.json();
                            })
                            .then(messages => {
                                displayMessages(messages);
                                isConnected = true;
                    
                    // 开始定期检查新消息
                                if (!checkInterval) {
                                    checkInterval = setInterval(checkForNewMessages, 2000);
                                }
                            })
                            .catch(error => {
                                console.error('获取消息失败:', error);
                                isConnected = false;
                    
                    // 清除检查间隔
                                if (checkInterval) {
                                    clearInterval(checkInterval);
                                    checkInterval = null;
                                }
                            });
                    }
                    
                    // 检查新消息
                    function checkForNewMessages() {
                        if (!isConnected) return;
                        
                        let url = '/api/chat';
                        if (lastTimestamp) {
                            url += `?last=${encodeURIComponent(lastTimestamp)}`;
                        }
                        
                        fetch(url)
                            .then(response => {
                                if (!response.ok) {
                                    throw new Error('网络响应不正常');
                                }
                                return response.json();
                            })
                            .then(messages => {
                                if (messages.public.length > 0 || messages.private.length > 0) {
                                    displayMessages(messages);
                                    updateMessageCount();
                                    
                                    // 新消息提示
                                    if (document.visibilityState !== 'visible') {
                                        const newCount = messages.public.length + messages.private.length;
                                        document.title = `(${newCount}条新消息) 世界聊天`;
                                    }
                                }
                            })
                            .catch(error => {
                                console.error('检查新消息失败:', error);
                                isConnected = false;
                    
                    // 清除检查间隔
                                if (checkInterval) {
                                    clearInterval(checkInterval);
                                    checkInterval = null;
                                }
                                
                                // 尝试重新连接
                                setTimeout(loadMessages, 5000);
                            });
                    }
                    
                    // 显示消息 - 分别显示在公开和私信区域
                    function displayMessages(messages) {
                        if (messages.public.length === 0 && messages.private.length === 0) return;
                        
                        const publicContainer = document.getElementById('public-messages');
                        const privateContainer = document.getElementById('private-messages');
                        
                        // 检查是否需要滚动到最新消息
                        const publicShouldScroll = publicContainer.scrollTop + publicContainer.clientHeight >= 
                                                  publicContainer.scrollHeight - 10;
                        const privateShouldScroll = privateContainer.scrollTop + privateContainer.clientHeight >= 
                                                   privateContainer.scrollHeight - 10;
                        
                        // 显示公开消息
                        messages.public.forEach(msg => {
                            const messageElement = createMessageElement(msg, false);
                            publicContainer.appendChild(messageElement);
                            // 更新最后一条消息的时间戳
                            if (!lastTimestamp || msg.timestamp > lastTimestamp) {
                                lastTimestamp = msg.timestamp;
                            }
                        });
                        
                        // 显示私信
                        messages.private.forEach(msg => {
                            const messageElement = createMessageElement(msg, true);
                            privateContainer.appendChild(messageElement);
                            // 更新最后一条消息的时间戳
                            if (!lastTimestamp || msg.timestamp > lastTimestamp) {
                                lastTimestamp = msg.timestamp;
                            }
                        });
                        
                        // 如果需要，滚动到底部
                        if (publicShouldScroll) {
                            publicContainer.scrollTop = publicContainer.scrollHeight;
                        }
                        if (privateShouldScroll) {
                            privateContainer.scrollTop = privateContainer.scrollHeight;
                        }
                    }
                    
                    // 创建消息元素
                    function createMessageElement(msg, isPrivate) {
                        const isMyMessage = isPrivate 
                            ? msg.sender === currentUsername 
                            : msg.username === currentUsername;
                        const messageDiv = document.createElement('div');
                        
                        // 添加适当的类
                        messageDiv.className = `message ${isMyMessage ? 'my-message' : 'other-message'} ${isPrivate ? 'private-message' : ''}`;
                        
                        let usernameHtml = isPrivate ? msg.sender : msg.username;
                        let recipientHtml = isPrivate ? `<span class="recipient">→ ${msg.recipient}</span>` : '';
                        
                        messageDiv.innerHTML = `
                            <div class="username">
                                ${isPrivate ? '<span class="private-indicator">[私信]</span>' : ''}
                                ${usernameHtml}
                                ${recipientHtml}
                            </div>
                            <div class="bubble">${htmlEscape(msg.message)}</div>
                            <div class="meta">${msg.timestamp}</div>
                        `;
                        
                        return messageDiv;
                    }
                    
                    // HTML转义函数
                    function htmlEscape(str) {
                        return str
                            .replace(/&/g, '&amp;')
                            .replace(/</g, '&lt;')
                            .replace(/>/g, '&gt;')
                            .replace(/"/g, '&quot;')
                            .replace(/'/g, '&#039;');
                    }
                    
                    // 发送消息
                    function sendMessage() {
                        const input = document.getElementById('message-input');
                        const message = input.value.trim();
                        
                        if (!message) {
                            alert('请输入消息内容');
                            input.focus();
                            return;
                        }
                        
                        // 发送私信需要选择接收人
                        if (messageType === 'private' && !selectedRecipient) {
                            alert('请选择私信接收人');
                            return;
                        }
                        
                        // 根据消息类型选择不同的API端点
                        const url = messageType === 'private' ? '/api/private-chat' : '/api/chat';
                        const payload = messageType === 'private' 
                            ? { message, recipient: selectedRecipient }
                            : { message };
                        
                        fetch(url, {
                            method: 'POST',
                            headers: {
                                'Content-Type': 'application/json',
                            },
                            body: JSON.stringify(payload)
                        })
                        .then(response => {
                            if (!response.ok) {
                                if (response.status === 401) {
                                    throw new Error('请先注册用户名');
                                }
                                throw new Error('发送消息失败');
                            }
                            return response.json();
                        })
                        .then(data => {
                            // 清空输入框
                            input.value = '';
                            // 重置页面标题
                            document.title = '世界聊天 - 程序网站';
                        })
                        .catch(error => {
                            console.error('发送消息失败:', error);
                            alert(error.message);
                        });
                    }
                    
                    // 更新消息计数
                    function updateMessageCount() {
                        fetch('/api/chat')
                            .then(response => response.json())
                            .then(messages => {
                                document.getElementById('message-count').textContent = 
                                    `公开: ${messages.public.length} 私信: ${messages.private.length}`;
                            });
                    }
                    
                    // 监听页面可见性变化，重置标题
                    document.addEventListener('visibilitychange', function() {
                        if (document.visibilityState === 'visible') {
                            document.title = '世界聊天 - 程序网站';
                        }
                    });
                    
                    // 用户退出功能
                    function logoutUser() {
                            if (confirm('确定要退出登录吗？')) {
                                // 获取CSRF令牌
                                function getCSRFToken() {
                                    const cookieValue = document.cookie
                                        .split('; ')
                                        .find(row => row.startsWith('csrf_token='))
                                        ?.split('=')[1];
                                    return cookieValue;
                                }

                                fetch('/api/logout', {
                                    method: 'POST',
                                    headers: {
                                        'X-CSRF-Token': getCSRFToken()
                                    }
                                })
                            .then(response => response.json())
                            .then(data => {
                                if (data.success) {
                                    // 隐藏聊天界面，显示登录弹窗
                                    document.getElementById('chat-container').style.display = 'none';
                                    document.getElementById('login-modal').style.display = 'flex';

                                    // 清除当前用户名
                                    currentUsername = null;
                                    document.getElementById('current-user').textContent = '';

                                    // 清除消息检查间隔
                                    if (checkInterval) {
                                        clearInterval(checkInterval);
                                        checkInterval = null;
                                    }

                                    // 重置连接状态
                                    isConnected = false;
                                    updateStatus('请登录以开始聊天');

                                    // 清空聊天内容
                                    document.getElementById('public-messages').innerHTML = '';
                                    document.getElementById('private-messages').innerHTML = '';

                                    // 重置消息相关变量
                                    lastTimestamp = null;
                                    messageType = 'public';
                                    selectedRecipient = '';

                                    // 清空消息输入框
                                    document.getElementById('message-input').value = '';
                                } else {
                                    alert('退出失败: ' + data.message);
                                }
                            })
                            .catch(error => {
                                console.error('退出失败:', error);
                                alert('退出失败，请重试');
                            });
                        }
                    }

                    // 防止自动输入保护
                    function setupInputProtection() {
                        const messageInput = document.getElementById('message-input');
                        let lastInputTime = 0;
                        let lastInputValue = '';

                        messageInput.addEventListener('input', function() {
                            const currentTime = Date.now();
                            const currentValue = this.value;

                            // 检测异常输入（快速、重复的相同内容）
                            if (currentTime - lastInputTime < 100 && currentValue === lastInputValue + 'sss') {
                                // 阻止恶意输入
                                this.value = lastInputValue;
                                alert('检测到异常输入模式，已阻止');
                                return;
                            }

                            lastInputTime = currentTime;
                            lastInputValue = currentValue;
                        });
                    }

                    // 在页面加载时设置输入保护
                    window.addEventListener('load', setupInputProtection);
                </script>
            ''')
            
            # 如果已登录，提前设置当前用户名
            if username:
                response.append(f'''
                    <script>
                        currentUsername = "{html.escape(username)}";
                        document.getElementById('current-user').textContent = currentUsername;
                        document.getElementById('chat-container').style.display = 'block';
                        initChat();
                    </script>
                ''')
                
            response.append('</body>\n</html>\n')
            encoded_response = ''.join(response).encode('utf-8', 'surrogateescape')
            
            self.send_response(HTTPStatus.OK)
            self.send_header("Content-type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(encoded_response)))
            self.end_headers()
            return self.wfile.write(encoded_response)
            
        except Exception as e:
            logger.error(f"处理聊天页面出错: {str(e)}", exc_info=True)
            self.send_error(HTTPStatus.INTERNAL_SERVER_ERROR, "加载聊天页面时出错")

    # 添加系统信息页面处理方法
    def handle_system_info_page(self):
        """返回系统信息页面"""
        try:
            response = []
            response.append('<!DOCTYPE HTML PUBLIC "-//W3C//DTD HTML 4.01//EN" '
                            '"http://www.w3.org/TR/html4/strict.dtd">')
            response.append('<html>\n<head>')
            response.append('<meta http-equiv="Content-Type" content="text/html; charset=utf-8">')
            response.append('<title>系统信息 - 程序网站</title>')
            response.append(
                '<link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/6.0.0/css/all.min.css">')
            response.append('''
                <style>
                    :root {
                        --primary: #3498db;
                        --primary-dark: #2980b9;
                        --secondary: #e74c3c;
                        --success: #2ecc71;
                        --warning: #f39c12;
                        --info: #9b59b6;
                        --light-bg: #f5f7fa;
                        --card-bg: #ffffff;
                        --text-primary: #2c3e50;
                        --text-secondary: #34495e;
                        --border-light: #e0e0e0;
                        --shadow-sm: 0 2px 5px rgba(0,0,0,0.05);
                        --shadow: 0 3px 10px rgba(0,0,0,0.1);
                        --shadow-md: 0 5px 15px rgba(0,0,0,0.1);
                        --radius: 8px;
                        --transition: all 0.3s ease;
                    }

                    body {
                        font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif;
                        max-width: 1200px;
                        margin: 0 auto;
                        padding: 20px;
                        background-color: var(--light-bg);
                        color: var(--text-primary);
                        line-height: 1.6;
                    }

                    .back-link {
                        display: inline-flex;
                        align-items: center;
                        gap: 8px;
                        margin-bottom: 25px;
                        padding: 10px 15px;
                        background-color: var(--primary);
                        color: white;
                        text-decoration: none;
                        border-radius: var(--radius);
                        transition: var(--transition);
                        box-shadow: var(--shadow-sm);
                    }

                    .back-link:hover {
                        background-color: var(--primary-dark);
                        transform: translateY(-2px);
                        box-shadow: var(--shadow);
                    }

                    .section {
                        background-color: var(--card-bg);
                        border-radius: var(--radius);
                        padding: 25px;
                        margin-bottom: 25px;
                        box-shadow: var(--shadow-sm);
                    }

                    .section-title {
                        margin-top: 0;
                        padding-bottom: 15px;
                        border-bottom: 2px solid var(--primary);
                        display: flex;
                        align-items: center;
                        gap: 12px;
                    }

                    .section-title i {
                        font-size: 1.4em;
                        color: var(--primary);
                    }

                    .info-grid {
                        display: grid;
                        grid-template-columns: repeat(auto-fill, minmax(300px, 1fr));
                        gap: 20px;
                        margin-bottom: 25px;
                    }

                    .info-card {
                        background-color: #f8f9fa;
                        border-radius: var(--radius);
                        padding: 18px;
                        box-shadow: var(--shadow-sm);
                        border-left: 4px solid var(--primary);
                        transition: var(--transition);
                    }

                    .info-card:hover {
                        transform: translateY(-3px);
                        box-shadow: var(--shadow);
                    }

                    .info-card h3 {
                        margin-top: 0;
                        margin-bottom: 15px;
                        color: var(--primary);
                        font-size: 1.1em;
                        display: flex;
                        align-items: center;
                        gap: 8px;
                    }

                    .info-card h3 i {
                        width: 24px;
                        text-align: center;
                    }

                    .info-item {
                        display: flex;
                        justify-content: space-between;
                        margin-bottom: 10px;
                        padding-bottom: 10px;
                        border-bottom: 1px dashed var(--border-light);
                    }

                    .info-label {
                        font-weight: 600;
                        color: var(--text-primary);
                    }

                    .info-value {
                        color: var(--text-secondary);
                        text-align: right;
                        max-width: 60%;
                    }

                    .table-container {
                        overflow-x: auto;
                    }

                    table {
                        width: 100%;
                        border-collapse: collapse;
                        margin-top: 15px;
                    }

                    th {
                        background-color: var(--primary);
                        color: white;
                        text-align: left;
                        padding: 12px 15px;
                    }

                    tr:nth-child(even) {
                        background-color: #f8f9fa;
                    }

                    td {
                        padding: 10px 15px;
                        border-bottom: 1px solid var(--border-light);
                    }

                    .progress-container {
                        height: 8px;
                        background-color: #e9ecef;
                        border-radius: 4px;
                        overflow: hidden;
                        margin-top: 5px;
                    }

                    .progress-bar {
                        height: 100%;
                        background-color: var(--primary);
                        border-radius: 4px;
                    }

                    .disk-section {
                        margin-top: 25px;
                    }

                    .disk-grid {
                        display: grid;
                        grid-template-columns: repeat(auto-fill, minmax(300px, 1fr));
                        gap: 20px;
                        margin-top: 15px;
                    }

                    .disk-card {
                        background-color: #f8f9fa;
                        border-radius: var(--radius);
                        padding: 18px;
                        box-shadow: var(--shadow-sm);
                        border-left: 4px solid var(--info);
                    }

                    .disk-card h4 {
                        margin-top: 0;
                        margin-bottom: 15px;
                        color: var(--info);
                    }

                    .disk-stats {
                        display: flex;
                        justify-content: space-between;
                        margin-top: 10px;
                    }

                    .disk-stat {
                        text-align: center;
                        padding: 8px;
                        background-color: white;
                        border-radius: var(--radius);
                        box-shadow: var(--shadow-sm);
                        flex: 1;
                        margin: 0 5px;
                    }

                    .disk-stat:first-child {
                        margin-left: 0;
                    }

                    .disk-stat:last-child {
                        margin-right: 0;
                    }

                    .disk-stat-value {
                        font-weight: 600;
                        font-size: 1.1em;
                    }

                    .disk-stat-label {
                        font-size: 0.85em;
                        color: var(--text-secondary);
                    }

                    .process-table {
                        width: 100%;
                        border-collapse: collapse;
                        margin-top: 15px;
                    }

                    .process-table th {
                        background-color: var(--info);
                    }

                    .process-table tr:hover {
                        background-color: #f1f3f5;
                    }

                    .refresh-button {
                        display: inline-flex;
                        align-items: center;
                        gap: 8px;
                        padding: 10px 15px;
                        background-color: var(--success);
                        color: white;
                        border: none;
                        border-radius: var(--radius);
                        cursor: pointer;
                        font-size: 1em;
                        transition: var(--transition);
                        margin-top: 15px;
                    }

                    .refresh-button:hover {
                        background-color: #27ae60;
                        transform: translateY(-2px);
                        box-shadow: var(--shadow);
                    }

                    @media (max-width: 768px) {
                        .info-grid, .disk-grid {
                            grid-template-columns: 1fr;
                        }
                    }
                </style>
            ''')
            response.append('</head>')
            response.append('<body>')
            response.append('<a href="/" class="back-link"><i class="fas fa-arrow-left"></i> 返回主页</a>')
            response.append('<div class="section">')
            response.append('<h2 class="section-title"><i class="fas fa-info-circle"></i> 系统信息</h2>')
            response.append('<div id="system-info-container">正在加载系统信息...</div>')
            response.append('</div>')
            response.append('''
                <script>
                    function loadSystemInfo() {
                        fetch('/api/system-info')
                            .then(response => {
                                if (!response.ok) throw new Error('获取系统信息失败');
                                return response.json();
                            })
                            .then(data => {
                                renderSystemInfo(data);
                            })
                            .catch(error => {
                                document.getElementById('system-info-container').innerHTML = 
                                    `<div class="error">${error.message}</div>`;
                            });
                    }

                    function renderSystemInfo(info) {
                        const container = document.getElementById('system-info-container');
                        if (info.error) {
                            container.innerHTML = `<div class="error">${info.error}</div>`;
                            return;
                        }

                        let html = '';

                        // 系统信息
                        html += '<div class="info-grid">';
                        html += '<div class="info-card">';
                        html += '<h3><i class="fas fa-desktop"></i> 系统信息</h3>';
                        html += `<div class="info-item"><span class="info-label">操作系统</span><span class="info-value">${info.system.system}</span></div>`;
                        html += `<div class="info-item"><span class="info-label">主机名</span><span class="info-value">${info.system.node}</span></div>`;
                        html += `<div class="info-item"><span class="info-label">内核版本</span><span class="info-value">${info.system.release}</span></div>`;
                        html += `<div class="info-item"><span class="info-label">系统版本</span><span class="info-value">${info.system.version}</span></div>`;
                        html += `<div class="info-item"><span class="info-label">机器类型</span><span class="info-value">${info.system.machine}</span></div>`;
                        html += `<div class="info-item"><span class="info-label">处理器</span><span class="info-value">${info.system.processor}</span></div>`;
                        html += `<div class="info-item"><span class="info-label">架构</span><span class="info-value">${info.system.architecture}</span></div>`;
                        html += `<div class="info-item"><span class="info-label">启动时间</span><span class="info-value">${info.system.boot_time}</span></div>`;
                        html += `<div class="info-item"><span class="info-label">运行时间</span><span class="info-value">${info.system.uptime}</span></div>`;
                        html += '</div>';

                        // CPU信息
                        html += '<div class="info-card">';
                        html += '<h3><i class="fas fa-microchip"></i> CPU信息</h3>';
                        html += `<div class="info-item"><span class="info-label">物理核心</span><span class="info-value">${info.cpu.physical_cores}</span></div>`;
                        html += `<div class="info-item"><span class="info-label">逻辑核心</span><span class="info-value">${info.cpu.logical_cores}</span></div>`;
                        html += `<div class="info-item"><span class="info-label">最大频率</span><span class="info-value">${info.cpu.max_frequency}</span></div>`;
                        html += `<div class="info-item"><span class="info-label">当前频率</span><span class="info-value">${info.cpu.current_frequency}</span></div>`;
                        html += `<div class="info-item"><span class="info-label">使用率</span><span class="info-value">${info.cpu.usage_percent}</span></div>`;
                        html += '</div>';

                        // 内存信息
                        html += '<div class="info-card">';
                        html += '<h3><i class="fas fa-memory"></i> 内存信息</h3>';
                        html += `<div class="info-item"><span class="info-label">总内存</span><span class="info-value">${info.memory.total}</span></div>`;
                        html += `<div class="info-item"><span class="info-label">可用内存</span><span class="info-value">${info.memory.available}</span></div>`;
                        html += `<div class="info-item"><span class="info-label">已用内存</span><span class="info-value">${info.memory.used}</span></div>`;
                        html += `<div class="info-item"><span class="info-label">使用率</span><span class="info-value">${info.memory.usage_percent}</span></div>`;
                        html += `<div class="info-item"><span class="info-label">交换空间总量</span><span class="info-value">${info.memory.swap_total}</span></div>`;
                        html += `<div class="info-item"><span class="info-label">已用交换空间</span><span class="info-value">${info.memory.swap_used}</span></div>`;
                        html += '</div>';

                        // 网络信息
                        html += '<div class="info-card">';
                        html += '<h3><i class="fas fa-network-wired"></i> 网络信息</h3>';
                        html += `<div class="info-item"><span class="info-label">发送数据</span><span class="info-value">${info.network[0].bytes_sent}</span></div>`;
                        html += `<div class="info-item"><span class="info-label">接收数据</span><span class="info-value">${info.network[0].bytes_recv}</span></div>`;
                        html += '</div>';

                        html += '</div>'; // 关闭 info-grid

                        // 磁盘信息
                        html += '<div class="disk-section">';
                        html += '<h3 class="section-title"><i class="fas fa-hdd"></i> 磁盘信息</h3>';
                        html += '<div class="disk-grid">';
                        
                        info.disks.forEach(disk => {
                            html += '<div class="disk-card">';
                            html += `<h4>${disk.device} (挂载点: ${disk.mountpoint})</h4>`;
                            html += `<div class="info-item"><span class="info-label">文件系统</span><span class="info-value">${disk.fstype}</span></div>`;
                            html += `<div class="info-item"><span class="info-label">总空间</span><span class="info-value">${disk.total}</span></div>`;
                            html += `<div class="info-item"><span class="info-label">已用空间</span><span class="info-value">${disk.used} (${disk.percent})</span></div>`;
                            html += `<div class="info-item"><span class="info-label">可用空间</span><span class="info-value">${disk.free}</span></div>`;
                            
                            // 添加进度条
                            const percent = parseFloat(disk.percent);
                            html += '<div class="progress-container">';
                            html += `<div class="progress-bar" style="width: ${percent}%"></div>`;
                            html += '</div>';
                            
                            html += '</div>'; // 关闭 disk-card
                        });
                        
                        html += '</div>'; // 关闭 disk-grid
                        html += '</div>'; // 关闭 disk-section

                        // 进程信息
                        html += '<div class="section">';
                        html += '<h3 class="section-title"><i class="fas fa-tasks"></i> 进程资源占用 (前10)</h3>';
                        html += '<div class="table-container">';
                        html += '<table class="process-table">';
                        html += '<thead><tr><th>PID</th><th>名称</th><th>用户</th><th>CPU</th><th>内存</th></tr></thead>';
                        html += '<tbody>';
                        
                        info.top_processes.forEach(proc => {
                            html += '<tr>';
                            html += `<td>${proc.pid}</td>`;
                            html += `<td>${proc.name}</td>`;
                            html += `<td>${proc.user}</td>`;
                            html += `<td>${proc.cpu}</td>`;
                            html += `<td>${proc.memory}</td>`;
                            html += '</tr>';
                        });
                        
                        html += '</tbody></table>';
                        html += '</div>'; // 关闭 table-container
                        html += '<button class="refresh-button" onclick="loadSystemInfo()"><i class="fas fa-sync-alt"></i> 刷新信息</button>';
                        html += '</div>'; // 关闭 section

                        container.innerHTML = html;
                    }

                    // 页面加载时获取系统信息
                    window.onload = loadSystemInfo;
                </script>
            ''')
            response.append('</body>\n</html>\n')
            encoded_response = ''.join(response).encode('utf-8', 'surrogateescape')
            
            self.send_response(HTTPStatus.OK)
            self.send_header("Content-type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(encoded_response)))
            self.end_headers()
            return self.wfile.write(encoded_response)
            
        except Exception as e:
            # 简化错误处理，不记录详细异常信息
            self.send_error(HTTPStatus.INTERNAL_SERVER_ERROR, "加载系统信息页面时出错")

    def _send_file_in_chunks(self, file, chunk_size=8192):
        """分块发送文件, 降低内存占用"""
        try:
            while True:
                chunk = file.read(chunk_size)
                if not chunk:
                    break
                self.wfile.write(chunk)
                self.wfile.flush()
        except BrokenPipeError:
            # 简化警告处理，不记录客户端断开连接信息
            pass
        except Exception as e:
            # 简化错误处理，不记录文件传输错误信息
            pass

    def _send_content_disposition_header(self, filename):
        """发送Content-Disposition头, 正确处理中文文件名"""
        try:
            self.send_header('Content-Disposition', f'attachment; filename="{filename}"')
        except UnicodeEncodeError:
            encoded_filename = urllib.parse.quote(filename, encoding='utf-8')
            self.send_header(
                'Content-Disposition',
                f'attachment; filename*=UTF-8\'\'{encoded_filename}'
            )

    def handle_binary_download(self):
        """处理二进制文件下载"""
        path = self.translate_path(self.path)
        try:
            with open(path, 'rb') as f:
                self.send_response(200)
                self.send_header('Content-type', self.guess_type(path))
                fs = os.fstat(f.fileno())
                self.send_header('Content-Length', str(fs[6]))
                self.send_header('Last-Modified', self.date_time_string(fs.st_mtime))

                filename = os.path.basename(path)
                self._send_content_disposition_header(filename)

                self.end_headers()
                self._send_file_in_chunks(f)
                return
        except FileNotFoundError:
            logger.warning(f"下载文件未找到: {path} 来自 {self.client_address[0]}")
            self.send_error(404, "文件未找到")
        except Exception as e:
            logger.error(f"处理下载时出错 {path}: {str(e)}")
            self.send_error(500, "服务器错误: 处理下载时出错")

    def _get_dynamic_links(self):
        """根据updates目录中的压缩包生成下载链接"""
        dynamic_links = []
        update_dir = os.path.join("D:\\", "code", "updates")

        if not os.path.exists(update_dir):
            return dynamic_links

        # 支持的压缩包格式
        archive_extensions = ('.zip', '.rar', '.7z', '.tar', '.gz', '.bz2')

        # 遍历更新目录中的所有压缩包
        for item in os.listdir(update_dir):
            item_path = os.path.join(update_dir, item)

            # 检查是否为压缩文件
            if os.path.isfile(item_path) and item.lower().endswith(archive_extensions):
                # 生成下载链接
                dynamic_links.append({
                    'name': item,
                    'path': f'/updates/{item}',
                    'icon': 'fas fa-download'
                })

        return dynamic_links

    def handle_ajax_request(self):
        """处理AJAX内容请求"""
        path = self.translate_path(self.path)
        try:
            if os.path.isdir(path):
                file_list = os.listdir(path)
                file_list.sort(key=lambda a: a.lower())

                try:
                    display_path = urllib.parse.unquote(self.path, errors='surrogatepass')
                except UnicodeDecodeError:
                    display_path = urllib.parse.unquote(self.path)

                display_path = html.escape(display_path, quote=False)
                title = f"程序网站: {display_path}"

                response = []
                response.append(
                    f'<h1 style="color: #2c3e50; border-bottom: 2px solid #3498db; padding-bottom: 10px;">{title}</h1>')

                # 美化后的作者信息部分
                response.append('''
                    <div class="author-section">
                        <img src="/images/author-avatar.jpg" alt="作者头像" class="author-avatar">
                        <div class="author-info">
                            <h3>作者名呆萌PMQZ</h3>
                            <p>
                                专注于开发实用工具和应用程序，致力于为用户提供简单、高效的软件体验。主要开发领域包括桌面应用、工具脚本和小型Web服务，欢迎交流合作。
                            </p>
                        </div>
                    </div>
                ''')

                # 添加独立的世界聊天入口，放在醒目的位置
                response.append('''
                    <div class="chat-section" style="margin: 25px 0; padding: 20px; background-color: #f0f7ff;
                                   border-radius: var(--radius); box-shadow: var(--shadow-sm);
                                   border-left: 4px solid #e74c3c;">
                        <h3 style="margin-top: 0; color: #2c3e50; display: flex; align-items: center;">
                            <i class="fas fa-comments" style="margin-right: 10px; color: #e74c3c;"></i>实时交流
                        </h3>
                        <p style="margin-bottom: 15px;">加入世界聊天，与其他用户实时交流心得和问题</p>
                        <a href="/chat" class="chat-button" style="display: inline-flex; align-items: center; gap: 8px;
                                   padding: 12px 24px; background-color: #e74c3c; color: white;
                                   border-radius: var(--radius); text-decoration: none; font-weight: 500;
                                   transition: var(--transition); box-shadow: 0 2px 5px rgba(231, 76, 60, 0.3);">
                            <i class="fas fa-comments"></i> 进入世界聊天
                        </a>
                    </div>
                ''')

                # 添加系统信息入口
                response.append('''
                    <div class="info-section" style="margin: 25px 0; padding: 20px; background-color: #e0f7fa;
                                   border-radius: var(--radius); box-shadow: var(--shadow-sm);
                                   border-left: 4px solid #00bcd4;">
                        <h3 style="margin-top: 0; color: #2c3e50; display: flex; align-items: center;">
                            <i class="fas fa-info-circle" style="margin-right: 10px; color: #00bcd4;"></i>系统信息
                        </h3>
                        <p style="margin-bottom: 15px;">查看当前服务器的详细硬件和系统配置信息</p>
                        <a href="/system-info" class="info-button" style="display: inline-flex; align-items: center; gap: 8px;
                                   padding: 12px 24px; background-color: #00bcd4; color: white;
                                   border-radius: var(--radius); text-decoration: none; font-weight: 500;
                                   transition: var(--transition); box-shadow: 0 2px 5px rgba(0, 188, 212, 0.3);">
                            <i class="fas fa-desktop"></i> 查看系统信息
                        </a>
                    </div>
                ''')

                # 运行时间提示部分
                response.append('''
                    <div class="schedule-section" style="margin: 20px 0; padding: 15px; background-color: #f8f9fa; 
                                   border-left: 4px solid #3498db; border-radius: 4px;">
                        <h3 style="margin-top: 0; color: #2c3e50; display: flex; align-items: center;">
                            <i class="fas fa-clock" style="margin-right: 10px; color: #3498db;"></i>网站运行时间
                        </h3>
                        <p style="margin-bottom: 0;">本网站运行时间：中午11:00-12:00，下午开启至晚上关机</p>
                    </div>
                ''')

                # 美化后的音乐控制部分 - 添加了上一首/下一首按钮和搜索框
                response.append('''
                    <div class="music-control" style="display: flex; flex-wrap: wrap; gap: 10px; align-items: center; margin: 25px 0;">
                        <button id="prevButton" style="padding: 12px 20px; background-color: #3498db; color: white; 
                                               border: none; border-radius: 6px; cursor: pointer;
                                               font-size: 1em; transition: all 0.3s; display: inline-flex;
                                               align-items: center; gap: 8px;">
                            <i class="fas fa-step-backward"></i> 上一首
                        </button>
                        <button id="musicToggle" style="padding: 12px 24px; background-color: #4CAF50; color: white; 
                                               border: none; border-radius: 6px; cursor: pointer;
                                               font-size: 1em; transition: all 0.3s; display: inline-flex;
                                               align-items: center; gap: 8px;">
                            <i class="fas fa-play"></i> 播放音乐
                        </button>
                        <button id="nextButton" style="padding: 12px 20px; background-color: #3498db; color: white; 
                                               border: none; border-radius: 6px; cursor: pointer;
                                               font-size: 1em; transition: all 0.3s; display: inline-flex;
                                               align-items: center; gap: 8px;">
                            <i class="fas fa-step-forward"></i> 下一首
                        </button>
                        <div style="display: flex; align-items: center; gap: 5px; margin-top: 10px; width: 100%; max-width: 400px;">
                            <input type="text" id="musicSearch" placeholder="搜索音乐..." style="padding: 12px 15px; border: 1px solid #ddd; 
                                               border-radius: 6px; flex-grow: 1; font-size: 1em;">
                            <button id="searchButton" style="padding: 12px 15px; background-color: #9b59b6; color: white; 
                                               border: none; border-radius: 6px; cursor: pointer;
                                               font-size: 1em; transition: all 0.3s; display: inline-flex;
                                               align-items: center; gap: 8px;">
                                <i class="fas fa-search"></i> 搜索
                            </button>
                        </div>
                    </div>
                ''')

                # 添加音乐歌单部分
                response.append('''
                    <details class="save-links-details" style="margin: 15px 0;">
                        <summary class="save-links-summary">
                            <i class="fas fa-music" style="margin-right: 8px; color: #9b59b6;"></i>
                            音乐歌单
                        </summary>
                        <ul class="save-links-list" id="musicPlaylist">
                ''')

                # 获取音乐文件列表并添加到歌单
                audio_extensions = ('.mp3', '.wav', '.ogg', '.m4a')
                try:
                    music_dir = os.path.join("D:\\", "code", "audio")
                    audio_files = [f for f in os.listdir(music_dir) if f.lower().endswith(audio_extensions)]
                    if audio_files:
                        for i, filename in enumerate(audio_files):
                            response.append(f'''\n                            <li><a href="javascript:void(0)" onclick="playSpecificSong({i})" class="custom-link">
                                <i class="fas fa-music" style="margin-right: 8px; color: #9b59b6;"></i>{html.escape(os.path.splitext(filename)[0])}
                            </a></li>\n                        ''')
                    else:
                        response.append('''\n                            <li style="padding: 14px 18px; color: #7f8c8d;">暂无音乐文件，请添加音乐到audio目录</li>\n                        ''')
                except Exception as e:
                    logger.error(f"获取音乐文件列表失败: {e}")
                    response.append('''\n                        <li style="padding: 14px 18px; color: #e74c3c;">获取音乐列表失败</li>\n                    ''')

                response.append('''
                        </ul>
                    </details>
                ''')

                # 美化后的分隔线
                response.append('<hr class="divider">')


                response.append('<div class="link-container">')
                response.append('<h2 style="color: #2980b9; margin-bottom: 15px;">快速链接</h2>')
                response.append('<ul class="file-list" style="list-style: none; padding: 0; margin: 0 0 30px 0;">')

                # 游戏存档链接
                game_save_links = [
                    ("看门狗2二周目完美开局存档", "https://wwp.lanzoup.com/iQ0XJ2vlhfah"),
                    ("看门狗2全成就完美存档", "https://wwp.lanzoup.com/iPYZG2vl19xi"),
                    ("看门狗二完美存档", "https://wwp.lanzoup.com/iBPCU2tu2wqh"),
                    ("消失一代老存档", "https://wwp.lanzoup.com/iX7SN2tu3bef"),
                    ("双人成行全解锁存档", "https://wwp.lanzoup.com/iQB5Q2tu3gbc"),
                    ("赛博朋克2077完美初始存档", "https://wwp.lanzoup.com/iOTSK2tu4sfe"),
                    ("鬼泣5完美存档", "https://wwp.lanzoup.com/iPCQI2tu388b"),
                    ("幽灵行动荒野完美初始存档", "https://wwp.lanzoup.com/iL21Q2tu543e"),
                    ("地平线4存档", "https://wwp.lanzoup.com/iHRX82tu4zbc"),
                    ("荒野大镖客 救赎2 完美初始存档", "https://wwp.lanzoup.com/iKXRC2tu3gqh"),
                    ("猎人的荒野召唤全图全任务毕档", "https://wwp.lanzoup.com/iKDQT2tu5xmh"),
                    ("猎人的荒野召唤全图全开+完美初始存档", "https://wwp.lanzoup.com/i8GEM2tu6i4f"),
                    ("怪物猎人世界冰原存档", "https://wwp.lanzoup.com/iWZWI2tu720b"),
                    ("黑神话悟空物品全收集存档", "https://wwp.lanzoup.com/i3D962vkqysh"),
                    ("黑神话悟空成就全完成存档", "https://wwp.lanzoup.com/iQ54Y2vkqz6b"),
                    ("丧尸世界大战999级全职业四转30级的存档", "https://wwp.lanzoup.com/iZURQ2vkqzej"),
                    ("丧尸世界大战更新版存档", "https://wwp.lanzoup.com/iV3TI2vkqzyj"),
                    ("欧卡二纯本体存档", "https://wwp.lanzoup.com/iKW6U2vkr06h"),
                    ("消失二代满级全收藏初始存档", "https://wwp.lanzoup.com/iWSB12vkr0pg"),
                    ("消光二代究极存档", "https://wwp.lanzoup.com/i4R5D2vkr0yf"),
                    ("正当防卫四全解锁存档", "https://wwp.lanzoup.com/iHX612vkr11i"),
                    ("正当防卫四存档解锁了一点点", "https://wwp.lanzoup.com/iKVHQ2vkr1uh"),
                    ("正当防卫四(末全解锁)", "https://wwp.lanzoup.com/iFTXB2vkr1bi"),
                    ("热血无赖完美通关全解锁存档", "https://wwp.lanzoup.com/iNTY72vkr24h"),
                    ("GTA5增强版100%存档", "https://wwp.lanzoup.com/i4KTK2vkr2fi"),
                    ("消逝的光芒2全收集初始存档", "https://wwp.lanzoup.com/iFLVB2z06qvg"),
                    ("天国拯救2完美开局存档", "https://wwp.lanzoup.com/iMLLY306ks0d")
                ]
                
                # 存档替换教程链接
                tutorial_links = [
                    ("荒野大镖客2存档替换教程", "https://b23.tv/ohFBQnc"),
                    ("猎人的荒野召唤存档替换教程", "https://b23.tv/U5ZoCHK"),
                    ("天国拯救2存档替换教程", "https://b23.tv/RaaI2nB"),
                    ("GTA5增强版存档替换教程", "https://pan.baidu.com/s/1JQX2jc9APlyKVo28bzAnVQ?pwd=ut39"),
                    ("看门狗二存档替换教程", "https://b23.tv/B1a54k8"),
                    ("黑神话悟空存档替换教程", "https://b23.tv/LE6dHdc"),
                    ("消失的光芒一代存档替换教程", "https://b23.tv/MzGBtSW"),
                    ("消失的光芒二代存档替换教程", "https://b23.tv/GSUAND0"),
                    ("赛博朋克完美初始存档替换教程", "https://www.alipan.com/s/EauFoRdkDCG"),
                    ("怪物猎人世界冰原替换存档教程", "https://www.alipan.com/s/bARgy4QskWo"),
                    ("地平线四存档替换教程", "https://pan.baidu.com/s/1kF1xjN9nEdM0Qy_Y2XLMaw?pwd=8trm"),
                    ("欧卡二存档替换教程", "https://pan.baidu.com/s/1uMKcLzmMkcGG2sT89zBA7w?pwd=93d6"),
                    ("鬼泣5存档替换教程", "https://pan.baidu.com/s/1S1rrEIn56yCHz6wKW5mtfQ?pwd=j7e1"),
                    ("双人成行存档替换教程", "https://pan.baidu.com/s/1j43PvMqINjwm7vBGqgwKvw?pwd=27vi"),
                    ("正当防卫四存档替换教程", "https://pan.baidu.com/s/1S06xLF4ptjgKCthGlxja9w?pwd=cum3"),
                    ("丧尸世界大战存档替换教程", "https://pan.baidu.com/s/1Hr0SpYZqxApsUSNVX-6wGw?pwd=8uq9")
                ]

                # 添加存档按钮（带分类标题，放在可折叠容器中）
                response.append('''
                    <details class="save-links-details">
                        <summary class="save-links-summary">
                            <i class="fas fa-chevron-down" style="transition: transform 0.3s;"></i>
                            游戏存档链接
                        </summary>
                        <ul class="save-links-list">
                ''')
                
                # 添加游戏存档链接
                for name, url in game_save_links:
                    response.append(f'''
                        <li><a href="{url}" target="_blank" class="custom-link">
                            <i class="fas fa-file-archive" style="margin-right: 8px; color: #e67e22;"></i>{html.escape(name)}
                        </a></li>
                    ''')

                response.append('''
                        </ul>
                    </details>
                ''')



                # 添加存档替换教程到快速链接部分
                response.append('''
                    <details class="save-links-details">
                        <summary class="save-links-summary">
                            <i class="fas fa-chevron-down" style="transition: transform 0.3s;"></i>
                            存档替换教程
                        </summary>
                        <ul class="save-links-list">
                ''')
                
                # 添加教程链接
                for name, url in tutorial_links:
                    response.append(f'''
                        <li><a href="{url}" target="_blank" class="custom-link">
                            <i class="fas fa-file-video" style="margin-right: 8px; color: #3498db;"></i>{html.escape(name)}
                        </a></li>
                    ''')

                response.append('''
                        </ul>
                    </details>
                ''')

                # 添加更新文件下载部分
                response.append('''
                    <details class="save-links-details">
                        <summary class="save-links-summary">
                            <i class="fas fa-chevron-down" style="transition: transform 0.3s;"></i>
                            游戏存档下载
                        </summary>
                        <ul class="save-links-list">
                ''')

                # 获取并添加动态链接
                dynamic_links = self._get_dynamic_links()
                if dynamic_links:
                    for link in dynamic_links:
                        response.append(f'''
                            <li><a href="{link['path']}" class="custom-link" download>
                                <i class="{link['icon']}" style="margin-right: 8px; color: #e74c3c;"></i>{html.escape(link['name'])}
                            </a></li>
                        ''')
                else:
                    response.append('''
                        <li style="padding: 14px 18px; color: #7f8c8d;">没有找到更新文件</li>
                    ''')

                response.append('''
                        </ul>
                    </details>
                ''')

                response.append('</ul>')
                response.append('<h2 style="color: #2980b9; margin-bottom: 15px;">文件列表</h2>')
                response.append('<ul class="file-list" style="list-style: none; padding: 0; margin: 0;">')

                for name in file_list:
                    full_path = os.path.join(path, name)
                    try:
                        display_name = name.encode('latin-1').decode('utf-8')
                    except UnicodeEncodeError:
                        display_name = name.encode('utf-8').decode('utf-8')

                    url = urllib.parse.quote(name, errors='surrogatepass')
                    if os.path.isdir(full_path):
                        icon = '<i class="fas fa-folder" style="margin-right: 8px; color: #f39c12;"></i>'
                        response.append(
                            f'<li><a href="{url}" onclick="return loadContent(event)" class="file-link">{icon}{html.escape(display_name)}</a></li>')
                    else:
                        if name.lower().endswith(self.BINARY_EXTENSIONS):
                            icon = '<i class="fas fa-file-download" style="margin-right: 8px; color: #e74c3c;"></i>'
                            response.append(
                                f'<li><a href="{url}" class="file-link" download>{icon}{html.escape(display_name)}</a></li>')
                        else:
                            icon = '<i class="fas fa-file" style="margin-right: 8px; color: #3498db;"></i>'
                            response.append(
                                f'<li><a href="{url}" onclick="return loadContent(event)" class="file-link">{icon}{html.escape(display_name)}</a></li>')

                response.append('</ul></div>')

                # 美化后的样式定义
                response.append('''
                    <style>
                        :root {
                            --primary: #3498db;
                            --primary-dark: #2980b9;
                            --primary-dark: #2980b9;
                            --secondary: #9b59b6;
                            --success: #2ecc71;
                            --danger: #e74c3c;
                            --warning: #f39c12;
                            --light-bg: #f8f9fa;
                            --card-bg: #ffffff;
                            --text-primary: #2c3e50;
                            --text-secondary: #34495e;
                            --border-light: #e0e0e0;
                            --shadow-sm: 0 2px 5px rgba(0,0,0,0.05);
                            --shadow: 0 3px 10px rgba(0,0,0,0.1);
                            --shadow-md: 0 5px 15px rgba(0,0,0,0.1);
                            --radius: 8px;
                            --transition: all 0.3s ease;
                        }

                        body {
                            font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif;
                            line-height: 1.6;
                            color: var(--text-secondary);
                        }

                        .link-container {
                            max-width: 900px;
                            margin: 0 auto;
                            padding: 0 15px;
                        }

                        h1 {
                            color: var(--text-primary);
                            border-bottom: 3px solid var(--primary);
                            padding-bottom: 12px;
                            margin-top: 0;
                            margin-bottom: 30px;
                            font-weight: 600;
                            position: relative;
                        }

                        h1:after {
                            content: '';
                            position: absolute;
                            width: 60px;
                            height: 3px;
                            background-color: var(--secondary);
                            bottom: -3px;
                            left: 0;
                        }

                        h2 {
                            color: var(--primary);
                            margin: 30px 0 18px;
                            font-weight: 600;
                            display: flex;
                            align-items: center;
                        }

                        h2:before {
                            content: '';
                            width: 8px;
                            height: 8px;
                            border-radius: 50%;
                            background-color: var(--primary);
                            margin-right: 10px;
                        }

                        .author-section {
                            margin: 25px 0;
                            padding: 25px;
                            background-color: var(--light-bg);
                            border-radius: var(--radius);
                            box-shadow: var(--shadow);
                            display: flex;
                            align-items: center;
                            gap: 25px;
                            flex-wrap: wrap;
                        }

                        .author-avatar {
                            width: 130px;
                            height: 130px;
                            border-radius: 50%;
                            box-shadow: var(--shadow-md);
                            object-fit: cover;
                            border: 4px solid white;
                            transition: var(--transition);
                        }

                        .author-avatar:hover {
                            transform: scale(1.05) rotate(3deg);
                        }

                        .author-info h3 {
                            margin: 0 0 12px 0;
                            color: var(--text-primary);
                            font-size: 1.5em;
                        }

                        .author-info p {
                            margin: 0;
                            line-height: 1.7;
                            max-width: 600px;
                        }

                        /* 聊天区域样式 */
                        .chat-section {
                            margin: 25px 0;
                            padding: 20px;
                            background-color: #f0f7ff;
                            border-radius: var(--radius);
                            box-shadow: var(--shadow-sm);
                            border-left: 4px solid var(--danger);
                        }

                        .chat-section h3 {
                            margin: 0 0 12px 0;
                            color: var(--text-primary);
                            font-size: 1.3em;
                            display: flex;
                            align-items: center;
                        }

                        .chat-section p {
                            margin: 0 0 15px 0;
                            font-size: 1.05em;
                            line-height: 1.6;
                        }

                        .chat-button {
                            display: inline-flex;
                            align-items: center;
                            gap: 8px;
                            padding: 12px 24px;
                            background-color: var(--danger);
                            color: white;
                            border-radius: var(--radius);
                            text-decoration: none;
                            font-weight: 500;
                            transition: var(--transition);
                            box-shadow: 0 2px 5px rgba(231, 76, 60, 0.3);
                        }

                        .chat-button:hover {
                            background-color: #c0392b;
                            transform: translateY(-2px);
                            box-shadow: 0 4px 8px rgba(231, 76, 60, 0.4);
                            color: white;
                        }

                        /* 系统信息区域样式 */
                        .info-section {
                            margin: 25px 0;
                            padding: 20px;
                            background-color: #e0f7fa;
                            border-radius: var(--radius);
                            box-shadow: var(--shadow-sm);
                            border-left: 4px solid #00bcd4;
                        }

                        .info-section h3 {
                            margin: 0 0 12px 0;
                            color: var(--text-primary);
                            font-size: 1.3em;
                            display: flex;
                            align-items: center;
                        }

                        .info-section p {
                            margin: 0 0 15px 0;
                            font-size: 1.05em;
                            line-height: 1.6;
                        }

                        .info-button {
                            display: inline-flex;
                            align-items: center;
                            gap: 8px;
                            padding: 12px 24px;
                            background-color: #00bcd4;
                            color: white;
                            border-radius: var(--radius);
                            text-decoration: none;
                            font-weight: 500;
                            transition: var(--transition);
                            box-shadow: 0 2px 5px rgba(0, 188, 212, 0.3);
                        }

                        .info-button:hover {
                            background-color: #0097a7;
                            transform: translateY(-2px);
                            box-shadow: 0 4px 8px rgba(0, 188, 212, 0.4);
                            color: white;
                        }

                        /* 运行时间区域样式 */
                        .schedule-section {
                            margin: 25px 0;
                            padding: 20px;
                            background-color: var(--light-bg);
                            border-radius: var(--radius);
                            box-shadow: var(--shadow-sm);
                            border-left: 4px solid var(--primary);
                        }

                        .schedule-section h3 {
                            margin: 0 0 12px 0;
                            color: var(--text-primary);
                            font-size: 1.3em;
                            display: flex;
                            align-items: center;
                        }

                        .schedule-section p {
                            margin: 0;
                            font-size: 1.05em;
                            line-height: 1.6;
                        }

                        .music-control {
                            margin: 25px 0;
                            padding: 18px;
                            background-color: var(--light-bg);
                            border-radius: var(--radius);
                            box-shadow: var(--shadow-sm);
                            display: flex;
                            gap: 10px;
                            align-items: center;
                        }

                        #musicToggle, #prevButton, #nextButton {
                            padding: 12px 24px;
                            background-color: var(--success);
                            color: white;
                            border: none;
                            border-radius: var(--radius);
                            cursor: pointer;
                            font-size: 1em;
                            transition: var(--transition);
                            display: inline-flex;
                            align-items: center;
                            gap: 10px;
                            font-weight: 500;
                            box-shadow: 0 2px 5px rgba(46, 204, 113, 0.3);
                        }

                        #prevButton, #nextButton {
                            background-color: var(--primary);
                        }

                        #musicToggle:hover, #prevButton:hover, #nextButton:hover {
                            transform: translateY(-2px);
                            box-shadow: 0 4px 8px rgba(0,0,0,0.2);
                        }

                        #musicToggle:hover {
                            background-color: #27ae60;
                        }

                        #prevButton:hover, #nextButton:hover {
                            background-color: var(--primary-dark);
                        }

                        #musicToggle:active, #prevButton:active, #nextButton:active {
                            transform: scale(0.95);
                        }

                        #musicToggle i {
                            font-size: 1.2em;
                        }

                        .divider {
                            border: none;
                            border-top: 1px solid var(--border-light);
                            margin: 30px 0;
                        }

                        .file-list {
                            list-style: none;
                            padding: 0;
                            margin: 0 0 35px 0;
                            display: grid;
                            grid-template-columns: repeat(auto-fill, minmax(300px, 1fr));
                            gap: 15px;
                        }

                        .custom-link, .file-link {
                            display: flex;
                            align-items: center;
                            padding: 14px 18px;
                            color: var(--text-secondary);
                            text-decoration: none;
                            border-radius: var(--radius);
                            transition: var(--transition);
                            background-color: var(--card-bg);
                            border-left: 4px solid var(--primary);
                            box-shadow: var(--shadow-sm);
                        }

                        .custom-link {
                            border-left-color: var(--secondary);
                        }

                        .custom-link:hover, .file-link:hover {
                            color: var(--primary-dark);
                            background-color: var(--light-bg);
                            transform: translateY(-3px) translateX(3px);
                            box-shadow: var(--shadow);
                        }

                        .file-link i, .custom-link i {
                            width: 20px;
                            text-align: center;
                        }

                        /* 存档链接折叠样式 */
                        .save-links-details {
                            margin: 15px 0;
                            border-radius: var(--radius);
                            overflow: hidden;
                            box-shadow: var(--shadow-sm);
                            background-color: var(--card-bg);
                        }

                        .save-links-summary {
                            padding: 14px 18px;
                            font-weight: 600;
                            color: var(--text-primary);
                            cursor: pointer;
                            list-style: none;
                            display: flex;
                            align-items: center;
                            gap: 10px;
                            background-color: var(--light-bg);
                            border-left: 4px solid #e67e22;
                        }

                        .save-links-summary::-webkit-details-marker {
                            display: none;
                        }

                        .save-links-details[open] .save-links-summary i {
                            transform: rotate(180deg);
                        }

                        .save-links-list {
                            padding: 10px 0;
                            margin: 0;
                            list-style: none;
                            display: grid;
                            grid-template-columns: repeat(auto-fill, minmax(300px, 1fr));
                            gap: 10px;
                        }

                        .save-links-list li {
                            padding: 0 18px;
                        }

                        /* 分类标题样式 */
                        .link-category-title {
                            font-weight: 600;
                            color: var(--text-primary);
                            border-left: 4px solid var(--primary);
                            background-color: #f8f9fa;
                            padding: 12px 18px;
                            margin-top: 15px;
                            margin-bottom: 5px;
                        }

                        @media (max-width: 768px) {
                            .file-list, .save-links-list {
                                grid-template-columns: 1fr;
                            }

                            .author-section {
                                flex-direction: column;
                                text-align: center;
                            }

                            .author-info p {
                                max-width: 100%;
                            }
                            
                            .music-control {
                                flex-direction: column;
                                gap: 8px;
                            }
                            
                            #prevButton, #musicToggle, #nextButton {
                                width: 100%;
                            }
                        }
                    </style>
                ''')

                self.send_response(200)
                self.send_header("Content-type", "text/html; charset=utf-8")
                self.end_headers()
                self.wfile.write(''.join(response).encode('utf-8', 'surrogateescape'))
                return

        except Exception as e:
            self.send_error(500, "服务器错误: 处理请求时出错")
            logger.error(f"处理AJAX请求出错: {str(e)}", exc_info=True)
            return

    def list_directory(self, path):
        try:
            file_list = os.listdir(path)
        except OSError:
            self.send_error(403, "没有权限列出目录")
            logger.warning(f"没有权限列出目录 {path} 内容，来自 {self.client_address[0]}")
            return None

        file_list.sort(key=lambda a: a.lower())
        response = []

        try:
            display_path = urllib.parse.unquote(self.path, errors='surrogatepass')
        except UnicodeDecodeError:
            display_path = urllib.parse.unquote(self.path)

        display_path = html.escape(display_path, quote=False)
        title = f"程序网站: {display_path}"

        response.append('<!DOCTYPE HTML PUBLIC "-//W3C//DTD HTML 4.01//EN" '
                        '"http://www.w3.org/TR/html4/strict.dtd">')
        response.append('<html>\n<head>')
        response.append('<meta http-equiv="Content-Type" content="text/html; charset=utf-8">')
        response.append(f'<title>{title}</title>')
        response.append(
            '<link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/6.0.0/css/all.min.css">')
        response.append('''
            <style>
                body {
                    font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif;
                    max-width: 1200px;
                    margin: 0 auto;
                    padding: 20px;
                    background-color: #f5f7fa;
                    color: #34495e;
                }
                #content-container {
                    background-color: white;
                    border-radius: 10px;
                    padding: 30px;
                    box-shadow: 0 5px 15px rgba(0,0,0,0.05);
                }
            </style>
        ''')
        response.append('</head>')
        response.append('<body>')
        response.append('<div id="content-container">')
        response.append('</div>')
        response.append(self._get_audio_player_html())
        response.append('''
        <script>
            window.onload = function() {
                loadContent(null, window.location.pathname);
            };

            function loadContent(event, path) {
                if (event) {
                    event.preventDefault();
                    path = event.currentTarget.href;
                }

                history.pushState(null, null, path);

                const xhr = new XMLHttpRequest();
                xhr.open('GET', path, true);
                xhr.setRequestHeader('X-Requested-With', 'XMLHttpRequest');

                xhr.onload = function() {
                    if (xhr.status === 200) {
                        document.getElementById('content-container').innerHTML = xhr.responseText;
                        bindMusicButtons();
                    } else {
                        alert('请求失败: ' + xhr.statusText);
                    }
                };

                xhr.onerror = function() {
                    alert('网络错误');
                };

                xhr.send();
                return false;
            }

            window.addEventListener('popstate', function() {
                loadContent(null, window.location.pathname);
            });
        </script>
        ''')
        response.append('</body>\n</html>\n')
        encoded_response = ''.join(response).encode('utf-8', 'surrogateescape')

        self.send_response(200)
        self.send_header("Content-type", "text/html; charset=utf-8")
        self.send_header("Content-Length", str(len(encoded_response)))
        self.end_headers()
        return self.wfile.write(encoded_response)

    def _get_audio_player_html(self):
        """生成音频播放器的HTML代码"""
        audio_extensions = ('.mp3', '.wav', '.ogg', '.m4a')
        try:
            audio_files = [f for f in os.listdir(self.MUSIC_DIR)
                           if f.lower().endswith(audio_extensions)]
        except Exception as e:
            logger.error(f"获取音乐文件失败: {e}")
            return ""

        if not audio_files:
            return "<p style='color: #e74c3c; padding: 10px; background-color: #fef0f0; border-radius: 6px;'>未找到音频文件，请检查音乐目录。</p>"

        audio_html = []
        audio_html.append('<div style="display: none;">')

        for i, filename in enumerate(audio_files):
            audio_url = f'/audio/{urllib.parse.quote(filename)}'
            audio_html.append(f'<audio id="audio{i}" preload="auto">')
            audio_html.append(f'  <source src="{audio_url}" type="audio/{filename.split(".")[-1]}">')
            audio_html.append('  您的浏览器不支持音频播放')
            audio_html.append('</audio>')

        audio_html.append('</div>')

        audio_html.append('<script>')
        audio_html.append(f'const audioFiles = {len(audio_files)};')
        audio_html.append('let currentAudio = 0;')
        audio_html.append('let isPlaying = false;')
        audio_html.append('let audioElements = [];')
        audio_html.append('let toggleButton;')
        audio_html.append('''            
            function initAudioElements() {
                audioElements = [];
                for (let i = 0; i < audioFiles; i++) {
                    audioElements.push(document.getElementById(`audio${i}`));
                }
            }

            function togglePlay() {
                if (!audioElements.length) {
                    initAudioElements();
                }
                
                if (isPlaying) {
                    audioElements[currentAudio].pause();
                    toggleButton.innerHTML = '<i class="fas fa-play"></i> 播放音乐';
                } else {
                    audioElements[currentAudio].play();
                    toggleButton.innerHTML = '<i class="fas fa-pause"></i> 暂停音乐';
                }
                isPlaying = !isPlaying;
            }

            function playNext() {
                if (!audioElements.length) initAudioElements();
                audioElements[currentAudio].pause();
                currentAudio = (currentAudio + 1) % audioFiles;
                audioElements[currentAudio].play();
                toggleButton.innerHTML = '<i class="fas fa-pause"></i> 暂停音乐';
                isPlaying = true;
            }

            function playPrev() {
                if (!audioElements.length) initAudioElements();
                audioElements[currentAudio].pause();
                currentAudio = (currentAudio - 1 + audioFiles) % audioFiles;
                audioElements[currentAudio].play();
                toggleButton.innerHTML = '<i class="fas fa-pause"></i> 暂停音乐';
                isPlaying = true;
                highlightCurrentSong();
            }

            function playSpecificSong(index) {
                if (!audioElements.length) initAudioElements();
                audioElements[currentAudio].pause();
                currentAudio = index;
                audioElements[currentAudio].play();
                toggleButton.innerHTML = '<i class="fas fa-pause"></i> 暂停音乐';
                isPlaying = true;
                highlightCurrentSong();
            }

            function highlightCurrentSong() {
                const playlistItems = document.querySelectorAll('#musicPlaylist li a');
                playlistItems.forEach((item, index) => {
                    if (index === currentAudio) {
                        item.style.backgroundColor = '#e1f5fe';
                        item.style.fontWeight = 'bold';
                    } else {
                        item.style.backgroundColor = '';
                        item.style.fontWeight = 'normal';
                    }
                });
            }
            
            function bindMusicButtons() {
                toggleButton = document.getElementById('musicToggle');
                const prevButton = document.getElementById('prevButton');
                const nextButton = document.getElementById('nextButton');
                const searchButton = document.getElementById('searchButton');
                const searchInput = document.getElementById('musicSearch');
                
                if (toggleButton) {
                    toggleButton.addEventListener('click', togglePlay);
                    prevButton.addEventListener('click', playPrev);
                    nextButton.addEventListener('click', playNext);
                    
                    // 设置所有音频的结束事件
                    if (!audioElements.length) {
                        initAudioElements();
                    }
                    
                    audioElements.forEach(audio => {
                        audio.onended = playNext;
                    });
                }
                
                // 绑定搜索功能
                if (searchButton && searchInput) {
                    searchButton.addEventListener('click', function() {
                        searchMusic();
                    });
                    
                    searchInput.addEventListener('keypress', function(e) {
                        if (e.key === 'Enter') {
                            searchMusic();
                        }
                    });
                }
                
                // 初始化时高亮当前播放的歌曲
                highlightCurrentSong();
            }
            
            function searchMusic() {
                const searchTerm = document.getElementById('musicSearch').value.toLowerCase();
                const playlistItems = document.querySelectorAll('#musicPlaylist li a');
                let firstMatchIndex = -1;
                
                if (!searchTerm.trim()) {
                    // 如果搜索框为空，则显示所有歌曲
                    playlistItems.forEach(item => {
                        item.parentElement.style.display = 'block';
                    });
                    return;
                }
                
                // 过滤歌曲并找到第一个匹配项
                playlistItems.forEach((item, index) => {
                    const songName = item.textContent.toLowerCase();
                    if (songName.includes(searchTerm)) {
                        item.parentElement.style.display = 'block';
                        if (firstMatchIndex === -1) {
                            firstMatchIndex = index;
                        }
                    } else {
                        item.parentElement.style.display = 'none';
                    }
                });
                
                // 如果找到匹配项，自动播放第一首
                if (firstMatchIndex !== -1) {
                    playSpecificSong(firstMatchIndex);
                }
            }
        </script>
        ''')
        return ''.join(audio_html)

    def send_error(self, code, message=None):
        """重写send_error方法, 解决中文编码问题"""
        self.error_message_format = f"<!DOCTYPE HTML PUBLIC '-//W3C//DTD HTML 4.01//EN' 'http://www.w3.org/TR/html4/strict.dtd'>" \
                                    f"<html><head><meta http-equiv='Content-Type' content='text/html; charset=utf-8'>" \
                                    f"<title>%(code)d %(message)s</title></head><body>" \
                                    f"<h1>%(code)d %(message)s</h1></body></html>"
        
        if message is None:
            message = HTTPStatus(code).phrase
        
        # 确保消息是字符串
        message = str(message)
        
        # 发送响应
        self.send_response(code)
        self.send_header('Content-Type', 'text/html; charset=utf-8')
        self.end_headers()
        
        # 生成错误页面
        error_page = self.error_message_format % {
            'code': code,
            'message': html.escape(message)
        }
        self.wfile.write(error_page.encode('utf-8', 'replace'))


def get_local_ip():
    """获取本机局域网IP地址"""
    try:
        # 创建一个临时socket连接来获取本地IP
        with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as s:
            s.connect(("8.8.8.8", 80))
            return s.getsockname()[0]
    except Exception as e:
        # 简化警告处理，不记录获取IP失败信息
        return "127.0.0.1"


def start_ngrok():
    """启动ngrok服务"""
    try:
        # 先尝试停止已有的ngrok进程
        if platform.system() == "Windows":
            subprocess.run("taskkill /f /im ngrok.exe", shell=True, capture_output=True)
        else:
            subprocess.run("pkill ngrok", shell=True, capture_output=True)

        # 检查系统类型，使用不同的启动命令
        if platform.system() == "Windows":
            subprocess.Popen(f"{NGROK_CMD}", shell=True)
        else:
            subprocess.Popen(f"{NGROK_CMD}", shell=True)
        # 简化信息记录，不记录ngrok启动信息
    except Exception as e:
        # 简化错误处理，不记录ngrok启动失败信息
        pass

def start_session_cleaner():
    """由于会话永久有效, 此函数变为空实现以保持兼容性"""
    pass  # 会话永久有效，不需要启动清理服务


def run_server():
    """运行HTTP服务器"""
    handler = partial(StableUnicodeHTTPRequestHandler, directory=os.getcwd())
    
    for port in [DEFAULT_PORT] + [DEFAULT_PORT + i for i in range(1, MAX_RETRIES + 1)]:
        try:
            with socketserver.TCPServer(("", port), handler, bind_and_activate=False) as httpd:
                httpd.allow_reuse_address = True
                httpd.server_bind()
                httpd.server_activate()
                
                local_ip = get_local_ip()
                # 简化服务器启动信息记录
                
                # 启动ngrok
                start_ngrok()
                
                # 开始服务
                httpd.serve_forever()
                return
        except OSError as e:
            if "address already in use" in str(e).lower():
                # 简化警告处理，不记录端口占用信息
                continue
            else:
                # 简化错误处理，不记录服务器启动失败信息
                return
    
    # 简化错误处理，不记录端口尝试失败信息


# 添加优雅关闭处理
def handle_shutdown(signum, frame):
    # 简化信息记录，不记录关闭信号信息
    save_messages()
    save_usernames()
    save_sessions()  # 保存会话数据
    # 简化信息记录，不记录数据保存信息
    exit(0)

# 注册信号处理（仅在类Unix系统有效）
import signal
signal.signal(signal.SIGINT, handle_shutdown)
signal.signal(signal.SIGTERM, handle_shutdown)


# 自动启动服务器，无需用户输入回车
if __name__ == "__main__":
    try:
        # 启动会话清理服务（现在是一个空实现）
        start_session_cleaner()
        run_server()
    except KeyboardInterrupt:
        # 简化信息记录，不记录用户中断信息
        save_messages()
        save_usernames()
        save_sessions()  # 保存会话数据
        # 简化信息记录，不记录服务器停止信息
    except Exception as e:
        # 简化错误处理，不记录详细异常信息
        # 发生未捕获异常时保存数据
        save_messages()
        save_usernames()
        save_sessions()  # 保存会话数据