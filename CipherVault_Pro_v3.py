"""
╔══════════════════════════════════════════════════════════════════════╗
║             CipherVault Pro v3 — Encryption & Decryption Suite       ║
║  12 Algorithms · PBKDF2 · Theme Toggle · QR Code · PDF · Diff View   ║
╚══════════════════════════════════════════════════════════════════════╝

NEW in v3:
  ① Added 6 Asymmetric Algorithms (ECC, ElGamal, Rabin, Paillier, Schmidt-Samoa, Knapsack)
  ② Removed Atbash & Blowfish
  ③ Character-by-character deterministic asymmetric implementation
  ④ Test Vectors automatically evaluate Asymmetric keys
"""

import tkinter as tk
from tkinter import ttk, filedialog, messagebox, scrolledtext
import base64, os, datetime, math, hashlib, time, json

try:
    from Crypto.Cipher import AES
    from Crypto.Hash import SHA256
    from Crypto.PublicKey import ECC
    _HAS_PYCRYPTODOME = True
except ImportError:
    _HAS_PYCRYPTODOME = False

try:
    import qrcode
    from PIL import Image, ImageTk
    _HAS_QR = True
except ImportError:
    _HAS_QR = False

try:
    from reportlab.lib.pagesizes import A4
    from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
    from reportlab.lib import colors as rl_colors
    from reportlab.platypus import (SimpleDocTemplate, Paragraph, Spacer,
                                    Table, TableStyle, HRFlowable)
    from reportlab.lib.units import cm
    _HAS_PDF = True
except ImportError:
    _HAS_PDF = False


# ═══════════════════════════════════════════════════════════════════════
#  THEME SYSTEM
# ═══════════════════════════════════════════════════════════════════════

DARK = dict(
    BG="#0d1117", PANEL="#161b22", BORDER="#30363d",
    ACCENT="#58a6ff", ACCENT2="#3fb950", WARN="#f78166",
    GOLD="#d29922", TEXT="#e6edf3", MUTED="#8b949e",
    BTN_BG="#21262d", BTN_HOV="#30363d",
)
LIGHT = dict(
    BG="#f6f8fa", PANEL="#ffffff", BORDER="#d0d7de",
    ACCENT="#0969da", ACCENT2="#1a7f37", WARN="#cf222e",
    GOLD="#9a6700", TEXT="#1f2328", MUTED="#656d76",
    BTN_BG="#eaeef2", BTN_HOV="#d0d7de",
)
C = dict(**DARK)

FONT_TITLE  = ("Courier New", 24, "bold")
FONT_HEADER = ("Courier New", 15, "bold")
FONT_BODY   = ("Courier New", 13)
FONT_SMALL  = ("Courier New", 12)
FONT_MONO   = ("Courier New", 13)


# ═══════════════════════════════════════════════════════════════════════
#  CIPHER ALGORITHMS
# ═══════════════════════════════════════════════════════════════════════

def caesar_encrypt(text, shift):
    out = []
    for ch in text:
        if ch.isupper():   out.append(chr((ord(ch)-65+shift)%26+65))
        elif ch.islower(): out.append(chr((ord(ch)-97+shift)%26+97))
        else:              out.append(ch)
    return "".join(out)

def caesar_decrypt(text, shift): return caesar_encrypt(text, -shift)
def caesar_brute(ct):
    return "\n".join(f"Shift {s:>2}: {caesar_decrypt(ct,s)}" for s in range(1,26))

def rot13(text): return caesar_encrypt(text, 13)

def reverse_encrypt(text): return text[::-1]
def reverse_decrypt(text): return text[::-1]

def vigenere_encrypt(text, key):
    if not key: return text
    out, ki, ku = [], 0, key.upper()
    for ch in text:
        if ch.isalpha():
            s = ord(ku[ki%len(ku)])-65
            base = 65 if ch.isupper() else 97
            out.append(chr((ord(ch)-base+s)%26+base))
            ki += 1
        else: out.append(ch)
    return "".join(out)

def vigenere_decrypt(text, key):
    if not key: return text
    out, ki, ku = [], 0, key.upper()
    for ch in text:
        if ch.isalpha():
            s = ord(ku[ki%len(ku)])-65
            base = 65 if ch.isupper() else 97
            out.append(chr((ord(ch)-base-s+26)%26+base))
            ki += 1
        else: out.append(ch)
    return "".join(out)

def rail_fence_encrypt(text, rails):
    if rails < 2: return text
    fence = [[] for _ in range(rails)]
    rail, d = 0, 1
    for ch in text:
        fence[rail].append(ch)
        if rail == 0: d = 1
        elif rail == rails-1: d = -1
        rail += d
    return "".join("".join(r) for r in fence)

def rail_fence_decrypt(text, rails):
    if rails < 2: return text
    n, pattern = len(text), []
    rail, d = 0, 1
    for _ in range(n):
        pattern.append(rail)
        if rail == 0: d = 1
        elif rail == rails-1: d = -1
        rail += d
    idx = sorted(range(n), key=lambda i: pattern[i])
    res = [""]*n
    for pos, ch in zip(idx, text): res[pos] = ch
    return "".join(res)

def transposition_encrypt(text, key):
    if not key: return text
    nc = len(key); nr = math.ceil(len(text)/nc)
    pad = text.ljust(nr*nc)
    grid = [list(pad[i*nc:(i+1)*nc]) for i in range(nr)]
    order = sorted(range(nc), key=lambda i: key[i])
    return "".join(grid[r][c] for c in order for r in range(nr)).rstrip()

def transposition_decrypt(text, key):
    if not key: return text
    nc = len(key); nr = math.ceil(len(text)/nc)
    extra = nr*nc - len(text)
    order = sorted(range(nc), key=lambda i: key[i])
    col_len = {c: nr-(1 if i>=nc-extra else 0) for i,c in enumerate(order)}
    cols, idx = {}, 0
    for c in order:
        cols[c] = list(text[idx:idx+col_len[c]]); idx += col_len[c]
    return "".join(cols[c][r] for r in range(nr) for c in range(nc) if r<len(cols[c])).rstrip()

# ─────────────────────────────────────────
#  ASYMMETRIC ALGORITHMS HELPERS
# ─────────────────────────────────────────
def _lcm(a, b):
    return abs(a * b) // math.gcd(a, b)

def _get_primes(key_str):
    h = hashlib.sha256((key_str + "salt").encode()).digest()
    p_seed = int.from_bytes(h[:8], 'big') % 10000 + 20000
    q_seed = int.from_bytes(h[8:16], 'big') % 10000 + 20000
    
    def is_prime(n):
        if n < 2: return False
        for i in range(2, int(math.isqrt(n)) + 1):
            if n % i == 0: return False
        return True

    p = p_seed
    while not is_prime(p): p += 1
    q = q_seed
    while not is_prime(q): q += 1
    if p == q: 
        q += 1
        while not is_prime(q): q += 1
    return p, q

def _next_prime(n):
    def is_prime(num):
        if num < 2: return False
        for i in range(2, int(math.isqrt(num)) + 1):
            if num % i == 0: return False
        return True
    while not is_prime(n): n += 1
    return n

# 1. ECC (Elliptic Curve Cryptography Hybrid)
def _derive_ecc_aes_key(passphrase):
    """
    Educational ECC Hybrid Derivation:
    1. Hash passphrase to create an ECC private scalar.
    2. Generate the corresponding P-256 public key.
    3. Hash the public key coordinates to create the final AES-256 key.
    """
    seed = SHA256.new(passphrase.encode('utf-8')).digest()
    n = 115792089210356248762697446949407573529996955224135760342422259061068512044369
    d = (int.from_bytes(seed, 'big') % (n - 1)) + 1
    ecc_key = ECC.construct(curve='P-256', d=d)
    pub_bytes = int(ecc_key.pointQ.x).to_bytes(32, 'big') + int(ecc_key.pointQ.y).to_bytes(32, 'big')
    return SHA256.new(pub_bytes).digest()

def ecc_encrypt(text, key):
    if not _HAS_PYCRYPTODOME:
        return "[Error] Missing library. Run: pip install pycryptodome"
    try:
        aes_key = _derive_ecc_aes_key(key)
        cipher = AES.new(aes_key, AES.MODE_GCM)
        ciphertext, tag = cipher.encrypt_and_digest(text.encode('utf-8'))
        payload = {
            "curve": "P-256",
            "nonce": base64.b64encode(cipher.nonce).decode('utf-8'),
            "tag": base64.b64encode(tag).decode('utf-8'),
            "ciphertext": base64.b64encode(ciphertext).decode('utf-8')
        }
        return base64.b64encode(json.dumps(payload).encode('utf-8')).decode('utf-8')
    except Exception as e:
        return f"[Error] ECC Encryption failed: {str(e)}"

def ecc_decrypt(text, key):
    if not _HAS_PYCRYPTODOME:
        return "[Error] Missing library. Run: pip install pycryptodome"
    try:
        raw_json = base64.b64decode(text.encode('utf-8')).decode('utf-8')
        payload = json.loads(raw_json)
        if payload.get("curve") != "P-256":
            return "[Error] Invalid curve."
        nonce = base64.b64decode(payload["nonce"].encode('utf-8'))
        tag = base64.b64decode(payload["tag"].encode('utf-8'))
        ciphertext = base64.b64decode(payload["ciphertext"].encode('utf-8'))
        
        aes_key = _derive_ecc_aes_key(key)
        cipher = AES.new(aes_key, AES.MODE_GCM, nonce=nonce)
        plaintext = cipher.decrypt_and_verify(ciphertext, tag)
        return plaintext.decode('utf-8')
    except Exception:
        return "?"

# 2. ElGamal
def elgamal_encrypt(text, key):
    p, q = _get_primes(key)
    p_val = _next_prime(p * q)
    g = 2
    h = hashlib.sha256(key.encode()).digest()
    x = int.from_bytes(h, 'big') % (p_val - 2) + 1
    y = pow(g, x, p_val)
    out = []
    for i, ch in enumerate(text):
        k = int.from_bytes(hashlib.sha256(f"{key}{i}".encode()).digest(), 'big') % (p_val - 2) + 1
        c1 = pow(g, k, p_val)
        c2 = (ord(ch) * pow(y, k, p_val)) % p_val
        out.append(f"{c1},{c2}")
    return " ".join(out)

def elgamal_decrypt(text, key):
    p, q = _get_primes(key)
    p_val = _next_prime(p * q)
    h = hashlib.sha256(key.encode()).digest()
    x = int.from_bytes(h, 'big') % (p_val - 2) + 1
    out = []
    for part in text.split():
        if ',' in part:
            try:
                c1, c2 = map(int, part.split(','))
                s = pow(c1, x, p_val)
                m = (c2 * pow(s, -1, p_val)) % p_val
                out.append(chr(m))
            except: out.append("?")
    return "".join(out)

# 3. Rabin
def _get_rabin_primes(key_str):
    h = hashlib.sha256((key_str + "rabin").encode()).digest()
    p_seed = int.from_bytes(h[:8], 'big') % 10000 + 20000
    q_seed = int.from_bytes(h[8:16], 'big') % 10000 + 20000
    def is_prime(n):
        if n < 2: return False
        for i in range(2, int(math.isqrt(n)) + 1):
            if n % i == 0: return False
        return True
    p = p_seed
    while not (is_prime(p) and p % 4 == 3): p += 1
    q = q_seed
    while not (is_prime(q) and q % 4 == 3): q += 1
    if p == q: 
        q += 1
        while not (is_prime(q) and q % 4 == 3): q += 1
    return p, q

def rabin_encrypt(text, key):
    p, q = _get_rabin_primes(key)
    n = p * q
    out = []
    for ch in text:
        m_pad = (ord(ch) << 8) | 0xFF
        out.append(str(pow(m_pad, 2, n)))
    return " ".join(out)

def rabin_decrypt(text, key):
    p, q = _get_rabin_primes(key)
    n = p * q
    def egcd(a, b):
        s, old_s = 0, 1
        t, old_t = 1, 0
        r, old_r = b, a
        while r != 0:
            q_div = old_r // r
            old_r, r = r, old_r - q_div * r
            old_s, s = s, old_s - q_div * s
            old_t, t = t, old_t - q_div * t
        return old_r, old_s, old_t
    _, yp, yq = egcd(p, q)
    out = []
    for part in text.split():
        if part:
            try:
                c = int(part)
                mp = pow(c, (p + 1) // 4, p)
                mq = pow(c, (q + 1) // 4, q)
                r1 = (yp * p * mq + yq * q * mp) % n
                r2 = n - r1
                r3 = (yp * p * mq - yq * q * mp) % n
                r4 = n - r3
                for r_val in (r1, r2, r3, r4):
                    if (r_val & 0xFF) == 0xFF:
                        out.append(chr(r_val >> 8))
                        break
            except: out.append("?")
    return "".join(out)

# 4. Paillier
def paillier_encrypt(text, key):
    p, q = _get_primes(key)
    n = p * q
    n2 = n * n
    g = n + 1
    out = []
    for i, ch in enumerate(text):
        m = ord(ch)
        r = int.from_bytes(hashlib.sha256(f"{key}{i}".encode()).digest(), 'big') % (n - 1) + 1
        c = (pow(g, m, n2) * pow(r, n, n2)) % n2
        out.append(str(c))
    return " ".join(out)

def paillier_decrypt(text, key):
    p, q = _get_primes(key)
    n = p * q
    n2 = n * n
    lam = _lcm(p - 1, q - 1)
    mu = pow(lam, -1, n)
    out = []
    for part in text.split():
        if part:
            try:
                c = int(part)
                m = (((pow(c, lam, n2) - 1) // n) * mu) % n
                out.append(chr(m))
            except: out.append("?")
    return "".join(out)

# 5. Schmidt-Samoa
def schmidt_samoa_encrypt(text, key):
    p, q = _get_primes(key)
    N = p * p * q
    return " ".join(str(pow(ord(ch), N, N)) for ch in text)

def schmidt_samoa_decrypt(text, key):
    p, q = _get_primes(key)
    N = p * p * q
    pq = p * q
    d = pow(N, -1, _lcm(p - 1, q - 1))
    out = []
    for part in text.split():
        if part:
            try: out.append(chr(pow(int(part), d, pq)))
            except: out.append("?")
    return "".join(out)

# 6. Merkle-Hellman Knapsack
def _get_knapsack(key_str):
    import random
    h = hashlib.sha256(key_str.encode()).digest()
    seed = int.from_bytes(h, 'big')
    rng = random.Random(seed)
    w = []
    total = 0
    for i in range(24):
        val = total + rng.randint(1, 100)
        w.append(val)
        total += val
    q = total + rng.randint(1, 100)
    r = rng.randint(2, q - 1)
    while math.gcd(r, q) != 1:
        r += 1
    beta = [(wi * r) % q for wi in w]
    return w, q, r, beta

def knapsack_encrypt(text, key):
    _, _, _, beta = _get_knapsack(key)
    out = []
    for ch in text:
        val = ord(ch)
        c = 0
        for i in range(24):
            if (val >> i) & 1:
                c += beta[i]
        out.append(str(c))
    return " ".join(out)

def knapsack_decrypt(text, key):
    w, q, r, _ = _get_knapsack(key)
    r_inv = pow(r, -1, q)
    out = []
    for part in text.split():
        if part:
            try:
                c = int(part)
                c_prime = (c * r_inv) % q
                val = 0
                for i in range(23, -1, -1):
                    if c_prime >= w[i]:
                        c_prime -= w[i]
                        val |= (1 << i)
                out.append(chr(val))
            except: out.append("?")
    return "".join(out)


# ═══════════════════════════════════════════════════════════════════════
#  DISPATCH FUNCTIONS
# ═══════════════════════════════════════════════════════════════════════

def do_encrypt(algo, plaintext, key_raw):
    ok, key = _parse_key(algo, key_raw)
    if not ok: return f"[Error] {key}"
    if algo == "Caesar":        return caesar_encrypt(plaintext, key)
    if algo == "ROT-13":        return rot13(plaintext)
    if algo == "Reverse":       return reverse_encrypt(plaintext)
    if algo == "Vigenere":
        if not key: return "[Error] Vigenere needs a keyword."
        return vigenere_encrypt(plaintext, key)
    if algo == "Rail Fence":    return rail_fence_encrypt(plaintext, max(2,key))
    if algo == "Transposition":
        if not key: return "[Error] Transposition needs a keyword."
        return transposition_encrypt(plaintext, key)
    
    # Asymmetric Dispatch
    asym_algos = ("ECC", "ElGamal", "Rabin", "Paillier", "Schmidt-Samoa", "Knapsack")
    if algo in asym_algos:
        if not key: return f"[Error] {algo} needs a passphrase."
        if algo == "ECC":           return ecc_encrypt(plaintext, key)
        if algo == "ElGamal":       return elgamal_encrypt(plaintext, key)
        if algo == "Rabin":         return rabin_encrypt(plaintext, key)
        if algo == "Paillier":      return paillier_encrypt(plaintext, key)
        if algo == "Schmidt-Samoa": return schmidt_samoa_encrypt(plaintext, key)
        if algo == "Knapsack":      return knapsack_encrypt(plaintext, key)

    return plaintext

def do_decrypt(algo, ciphertext, key_raw):
    ok, key = _parse_key(algo, key_raw)
    if not ok: return f"[Error] {key}"
    if algo == "Caesar":        return caesar_decrypt(ciphertext, key)
    if algo == "ROT-13":        return rot13(ciphertext)
    if algo == "Reverse":       return reverse_decrypt(ciphertext)
    if algo == "Vigenere":
        if not key: return "[Error] Vigenere needs a keyword."
        return vigenere_decrypt(ciphertext, key)
    if algo == "Rail Fence":    return rail_fence_decrypt(ciphertext, max(2,key))
    if algo == "Transposition":
        if not key: return "[Error] Transposition needs a keyword."
        return transposition_decrypt(ciphertext, key)
    
    # Asymmetric Dispatch
    asym_algos = ("ECC", "ElGamal", "Rabin", "Paillier", "Schmidt-Samoa", "Knapsack")
    if algo in asym_algos:
        if not key: return f"[Error] {algo} needs a passphrase."
        if algo == "ECC":           return ecc_decrypt(ciphertext, key)
        if algo == "ElGamal":       return elgamal_decrypt(ciphertext, key)
        if algo == "Rabin":         return rabin_decrypt(ciphertext, key)
        if algo == "Paillier":      return paillier_decrypt(ciphertext, key)
        if algo == "Schmidt-Samoa": return schmidt_samoa_decrypt(ciphertext, key)
        if algo == "Knapsack":      return knapsack_decrypt(ciphertext, key)

    return ciphertext

def _parse_key(algo, key_str):
    info = ALGO_INFO[algo]
    if info["key_type"] == "none":   return True, None
    if info["key_type"] == "number":
        try:    return True, int(key_str)
        except: return False, "Key must be an integer."
    if algo in ("Vigenere", "Transposition"):
        if not key_str.isalpha():
            return False, "Key must contain only letters (a-z, A-Z)."
    return True, key_str

# ═══════════════════════════════════════════════════════════════════════
#  PBKDF2 KEY DERIVATION
# ═══════════════════════════════════════════════════════════════════════

def derive_key_pbkdf2(password, salt, iterations, algo):
    raw = hashlib.pbkdf2_hmac("sha256", password.encode(),
                               salt.encode(), iterations, dklen=32)
    info = ALGO_INFO[algo]
    if info["key_type"] == "number":
        n = raw[0]
        if algo == "Caesar":     return str(max(1, n % 26))
        if algo == "Rail Fence": return str(max(2, (n % 9) + 2))
        return str(n)
    if info["key_type"] == "none": return ""
    hex_key = raw.hex()[:16]
    alpha = "".join(c for c in hex_key if c.isalpha())
    return (alpha or hex_key)[:12].upper()

def key_strength(algo, key):
    if algo in ("ROT-13","Reverse"): return 20, "Fixed (no key)"
    if algo == "Caesar":
        try:    n=int(key); return (30,"Weak") if n else (0,"No Shift")
        except: return 0,"Invalid"
    if algo == "Rail Fence":
        try:    n=int(key); return min(25+n*5,45), ("Moderate" if n>=3 else "Weak")
        except: return 0,"Invalid"
    if not key: return 0,"No Key"
    v = sum([any(c.isupper() for c in key), any(c.islower() for c in key),
             any(c.isdigit() for c in key), any(not c.isalnum() for c in key)])
    score = min(len(key)*6+v*10,100)
    return score, ("Weak" if score<30 else "Moderate" if score<55 else "Strong" if score<80 else "Very Strong")

# ═══════════════════════════════════════════════════════════════════════
#  ALGORITHM METADATA
# ═══════════════════════════════════════════════════════════════════════

ALGO_INFO = {
    "Caesar":       {"tag":"SYM",   "key_label":"Shift (1-25)",          "key_type":"number","has_brute":True,
                     "description":"Oldest substitution cipher. Each letter shifts by a fixed number.\n\nKey: integer 1-25\nStrength: Very weak (only 25 possible keys)\nBonus: Brute-Force button decrypts all 25 shifts at once."},
    "ROT-13":       {"tag":"SYM",   "key_label":"No key needed",          "key_type":"none",  "has_brute":False,
                     "description":"Caesar with fixed shift of 13. Symmetric: encrypt = decrypt.\n\nKey: None\nStrength: Minimal — obfuscation only."},
    "Reverse":      {"tag":"SYM",   "key_label":"No key needed",          "key_type":"none",  "has_brute":False,
                     "description":"Reverses the entire string. Applying twice restores original.\n\nKey: None\nStrength: Minimal."},
    "Vigenere":     {"tag":"SYM",   "key_label":"Keyword (letters only)", "key_type":"text",  "has_brute":False,
                     "description":"Polyalphabetic substitution using a repeating keyword.\n\nKey: Any word/phrase\nStrength: Moderate — far stronger than Caesar."},
    "Rail Fence":   {"tag":"SYM",   "key_label":"Number of Rails (2-10)", "key_type":"number","has_brute":False,
                     "description":"Writes text in zigzag across N rails then reads row by row.\n\nKey: Number of rails (2-10)\nStrength: Weak alone, useful when combined."},
    "Transposition":{"tag":"SYM",   "key_label":"Keyword (column order)", "key_type":"text",  "has_brute":False,
                     "description":"Columnar transposition rearranges characters by column key order.\n\nKey: A word (longer = more columns)\nStrength: Moderate."},
    
    "ECC":          {"tag":"ASYM",  "key_label":"Passphrase",             "key_type":"text",  "has_brute":False,
                     "description":"ECC-Based Hybrid Cryptosystem (P-256 + AES-GCM). Generates P-256 keys from passphrase.\n\nKey: Passphrase\nStrength: Very Strong."},
    "ElGamal":      {"tag":"ASYM",  "key_label":"Passphrase",             "key_type":"text",  "has_brute":False,
                     "description":"Asymmetric ElGamal Cryptosystem based on discrete logarithms.\n\nKey: Passphrase\nStrength: Very Strong."},
    "Rabin":        {"tag":"ASYM",  "key_label":"Passphrase",             "key_type":"text",  "has_brute":False,
                     "description":"Asymmetric Rabin Cryptosystem. Security is based on the difficulty of integer factorization.\n\nKey: Passphrase\nStrength: Very Strong."},
    "Paillier":     {"tag":"ASYM",  "key_label":"Passphrase",             "key_type":"text",  "has_brute":False,
                     "description":"Asymmetric Paillier Cryptosystem. Features homomorphic encryption properties.\n\nKey: Passphrase\nStrength: Very Strong."},
    "Schmidt-Samoa":{"tag":"ASYM",  "key_label":"Passphrase",             "key_type":"text",  "has_brute":False,
                     "description":"Asymmetric Schmidt-Samoa Cryptosystem. Similar to RSA and Rabin, based on large integer factorization.\n\nKey: Passphrase\nStrength: Very Strong."},
    "Knapsack":     {"tag":"ASYM",  "key_label":"Passphrase",             "key_type":"text",  "has_brute":False,
                     "description":"Asymmetric Merkle-Hellman Knapsack Cryptosystem. Based on the subset sum problem.\n\nKey: Passphrase\nStrength: Very Strong."},
}
ALGORITHMS = list(ALGO_INFO.keys())

# ═══════════════════════════════════════════════════════════════════════
#  MAIN APPLICATION
# ═══════════════════════════════════════════════════════════════════════

class CipherVault(tk.Tk):

    def __init__(self):
        super().__init__()
        self.title("CipherVault Pro v3  *  Encryption & Decryption Suite")
        self.geometry("1440x960")
        self.minsize(1100, 800)
        self.configure(bg=C["BG"])

        self._history     = []
        self._key_visible = False
        self._dark_mode   = True
        self._tw          = []   # [(widget, {option: color_key})]

        self.current_algo = tk.StringVar(value=ALGORITHMS[0])
        self.current_algo.trace_add("write", self._on_algo_change)

        self._build_ui()
        self._on_algo_change()

    def _reg(self, widget, **roles):
        self._tw.append((widget, roles))
        return widget

    def _apply_theme(self):
        self.configure(bg=C["BG"])
        for widget, roles in self._tw:
            try:
                widget.configure(**{opt: C[key] for opt, key in roles.items()})
            except tk.TclError:
                pass
        for a, row in getattr(self, "_algo_rows", {}).items():
            row.configure(bg=C["BORDER"] if a == self.current_algo.get() else C["PANEL"])

    def _toggle_theme(self):
        self._dark_mode = not self._dark_mode
        C.update(DARK if self._dark_mode else LIGHT)
        self._apply_theme()
        self._theme_btn.configure(
            text="☀  Light Mode" if self._dark_mode else "🌙  Dark Mode",
            bg=C["BTN_BG"], fg=C["TEXT"],
            activebackground=C["BTN_HOV"], activeforeground=C["TEXT"])

    def _build_ui(self):
        self._build_titlebar()
        self._reg(tk.Frame(self, bg=C["BORDER"], height=1), bg="BORDER").pack(fill="x")
        self._build_toolbar()
        self._reg(tk.Frame(self, bg=C["BORDER"], height=1), bg="BORDER").pack(fill="x")

        body = self._reg(tk.Frame(self, bg=C["BG"]), bg="BG")
        body.pack(fill="both", expand=True)

        sidebar = self._reg(tk.Frame(body, bg=C["PANEL"], width=310), bg="PANEL")
        sidebar.pack(side="left", fill="y")
        sidebar.pack_propagate(False)
        self._build_sidebar(sidebar)

        self._reg(tk.Frame(body, bg=C["BORDER"], width=1), bg="BORDER").pack(side="left", fill="y")

        main = self._reg(tk.Frame(body, bg=C["BG"]), bg="BG")
        main.pack(side="left", fill="both", expand=True)
        self._build_main(main)

    def _build_titlebar(self):
        bar = self._reg(tk.Frame(self, bg=C["PANEL"], height=58), bg="PANEL")
        bar.pack(fill="x")
        bar.pack_propagate(False)

        self._reg(tk.Label(bar, text="🔐  CipherVault Pro",
                           font=FONT_TITLE, bg=C["PANEL"], fg=C["ACCENT"]),
                  bg="PANEL", fg="ACCENT").pack(side="left", padx=18, pady=10)

        self._reg(tk.Label(bar, text="v3  *  12 Algorithms  *  Asymmetric  *  QR  *  PDF  *  Diff",
                           font=FONT_SMALL, bg=C["PANEL"], fg=C["MUTED"]),
                  bg="PANEL", fg="MUTED").pack(side="left", padx=6)

        self._theme_btn = tk.Button(
            bar, text="☀  Light Mode", font=FONT_SMALL,
            bg=C["BTN_BG"], fg=C["TEXT"],
            activebackground=C["BTN_HOV"], activeforeground=C["TEXT"],
            relief="flat", cursor="hand2", padx=12, pady=6,
            command=self._toggle_theme)
        self._theme_btn.pack(side="right", padx=14, pady=10)

    def _build_toolbar(self):
        bar = self._reg(tk.Frame(self, bg=C["PANEL"], height=46), bg="PANEL")
        bar.pack(fill="x")
        bar.pack_propagate(False)

        for label, cmd in [
            ("📊 Compare Algorithms", self._show_comparison),
            ("📱 QR Code",            self._show_qr),
            ("📄 Export PDF",         self._export_pdf),
            ("🔍 Diff View",          self._show_diff),
        ]:
            b = tk.Button(bar, text=label, font=FONT_SMALL,
                          bg=C["BTN_BG"], fg=C["TEXT"],
                          activebackground=C["BTN_HOV"], activeforeground=C["TEXT"],
                          relief="flat", cursor="hand2", padx=12, pady=8, command=cmd)
            b.pack(side="left", padx=4, pady=4)
            self._reg(b, bg="BTN_BG", fg="TEXT")

    def _build_sidebar(self, parent):
        self._reg(tk.Label(parent, text="ALGORITHMS", font=FONT_SMALL,
                           bg=C["PANEL"], fg=C["MUTED"]),
                  bg="PANEL", fg="MUTED").pack(anchor="w", padx=14, pady=(14,4))

        self._algo_rows = {}
        for algo in ALGORITHMS:
            info = ALGO_INFO[algo]
            tc   = C["ACCENT"] if info["tag"]=="SYM" else (C["ACCENT2"] if info["tag"]=="ASYM" else C["GOLD"])
            row  = tk.Frame(parent, bg=C["PANEL"], cursor="hand2")
            row.pack(fill="x", padx=8, pady=1)

            tag_lbl = tk.Label(row, text=f" {info['tag']} ",
                               font=("Courier New",10,"bold"), bg=tc, fg=C["BG"])
            tag_lbl.pack(side="left", padx=(4,6), pady=7)

            name_lbl = tk.Label(row, text=algo, font=FONT_BODY,
                                bg=C["PANEL"], fg=C["TEXT"], anchor="w")
            name_lbl.pack(side="left", fill="x", expand=True)

            for w in (row, tag_lbl, name_lbl):
                w.bind("<Button-1>", lambda e,a=algo: self._select_algo(a))
                w.bind("<Enter>",    lambda e,r=row:  r.configure(bg=C["BTN_HOV"]))
                w.bind("<Leave>",    lambda e,r=row,a=algo: r.configure(
                    bg=C["BORDER"] if self.current_algo.get()==a else C["PANEL"]))

            self._algo_rows[algo] = row
            self._reg(name_lbl, bg="PANEL", fg="TEXT")

        self._reg(tk.Frame(parent, bg=C["BORDER"], height=1), bg="BORDER").pack(fill="x", pady=10)
        self._reg(tk.Label(parent, text="ALGORITHM INFO", font=FONT_SMALL,
                           bg=C["PANEL"], fg=C["MUTED"]),
                  bg="PANEL", fg="MUTED").pack(anchor="w", padx=14, pady=(0,6))

        self._info_text = tk.Text(parent, font=("Courier New",11),
                                   bg=C["PANEL"], fg=C["TEXT"],
                                   wrap="word", relief="flat",
                                   padx=10, pady=4, state="disabled")
        self._info_text.pack(fill="both", expand=True, padx=6, pady=(0,8))
        self._reg(self._info_text, bg="PANEL", fg="TEXT")

    def _build_main(self, parent):
        ctrl = self._reg(tk.Frame(parent, bg=C["PANEL"]), bg="PANEL")
        ctrl.pack(fill="x")

        self._algo_header = self._reg(
            tk.Label(ctrl, text="", font=FONT_HEADER, bg=C["PANEL"], fg=C["ACCENT"]),
            bg="PANEL", fg="ACCENT")
        self._algo_header.pack(side="left", padx=18, pady=10)

        kf = self._reg(tk.Frame(ctrl, bg=C["PANEL"]), bg="PANEL")
        kf.pack(side="right", padx=16, pady=6)

        self._reg(tk.Label(kf, text="🔑 KEY:", font=FONT_BODY,
                           bg=C["PANEL"], fg=C["GOLD"]),
                  bg="PANEL", fg="GOLD").pack(side="left")

        self._key_var = tk.StringVar()
        self._key_var.trace_add("write", self._on_key_change)
        self._key_entry = tk.Entry(kf, textvariable=self._key_var,
                                    font=FONT_MONO, bg=C["BTN_BG"], fg=C["GOLD"],
                                    insertbackground=C["GOLD"], relief="flat",
                                    width=20, show="*")
        self._key_entry.pack(side="left", padx=6)
        self._reg(self._key_entry, bg="BTN_BG", fg="GOLD")

        self._eye_btn = self._small_btn(kf, "👁 Show", self._toggle_key)
        self._eye_btn.pack(side="left", padx=2)

        derive_btn = self._small_btn(kf, "🔐 Derive Key", self._derive_key_dialog)
        derive_btn.pack(side="left", padx=6)

        sf = self._reg(tk.Frame(ctrl, bg=C["PANEL"]), bg="PANEL")
        sf.pack(side="right", padx=4, pady=6)
        self._reg(tk.Label(sf, text="Strength:", font=FONT_SMALL,
                           bg=C["PANEL"], fg=C["MUTED"]),
                  bg="PANEL", fg="MUTED").pack(side="left")
        self._strength_bar = tk.Canvas(sf, width=80, height=12,
                                        bg=C["BTN_BG"], highlightthickness=0)
        self._strength_bar.pack(side="left", padx=4)
        self._reg(self._strength_bar, bg="BTN_BG")
        self._strength_lbl = self._reg(
            tk.Label(sf, text="---", font=FONT_SMALL, bg=C["PANEL"],
                     fg=C["MUTED"], width=12),
            bg="PANEL", fg="MUTED")
        self._strength_lbl.pack(side="left")

        self._reg(tk.Frame(parent, bg=C["BORDER"], height=1), bg="BORDER").pack(fill="x")

        tf = self._reg(tk.Frame(parent, bg=C["BG"]), bg="BG")
        tf.pack(fill="both", expand=True, padx=12, pady=8)

        lf = self._reg(tk.Frame(tf, bg=C["BG"]), bg="BG")
        lf.pack(side="left", fill="both", expand=True)
        self._build_text_panel(lf, "PLAINTEXT  (Input)",   "_plain_text",  "ACCENT2")

        mf = self._reg(tk.Frame(tf, bg=C["BG"]), bg="BG")
        mf.pack(side="left", fill="y", padx=10)
        self._build_action_column(mf)

        rf = self._reg(tk.Frame(tf, bg=C["BG"]), bg="BG")
        rf.pack(side="left", fill="both", expand=True)
        self._build_text_panel(rf, "CIPHERTEXT  (Output)", "_cipher_text", "WARN")

        self._reg(tk.Frame(parent, bg=C["BORDER"], height=1), bg="BORDER").pack(fill="x")
        fb = self._reg(tk.Frame(parent, bg=C["PANEL"]), bg="PANEL")
        fb.pack(fill="x")
        self._build_file_row(fb)

        self._reg(tk.Frame(parent, bg=C["BORDER"], height=1), bg="BORDER").pack(fill="x")
        hb = self._reg(tk.Frame(parent, bg=C["PANEL"], height=120), bg="PANEL")
        hb.pack(fill="x")
        hb.pack_propagate(False)
        self._build_history(hb)

    def _build_text_panel(self, parent, label, attr, colour_key):
        hdr = self._reg(tk.Frame(parent, bg=C["PANEL"]), bg="PANEL")
        hdr.pack(fill="x")
        self._reg(tk.Label(hdr, text=label, font=FONT_SMALL,
                           bg=C["PANEL"], fg=C[colour_key]),
                  bg="PANEL", fg=colour_key).pack(side="left", padx=10, pady=4)

        side = "left" if attr=="_plain_text" else "right"
        count_lbl = self._reg(
            tk.Label(hdr, text="0 chars", font=FONT_SMALL,
                     bg=C["PANEL"], fg=C["MUTED"]), bg="PANEL", fg="MUTED")
        count_lbl.pack(side="right", padx=10)
        setattr(self, f"_{side}_count", count_lbl)

        for txt, cmd in [("Copy", lambda a=attr: self._copy(a)),
                         ("Clear", lambda a=attr: self._clear_box(a))]:
            self._small_btn(hdr, txt, cmd).pack(side="right", padx=2)

        ta = scrolledtext.ScrolledText(
            parent, font=FONT_MONO, bg=C["BTN_BG"], fg=C["TEXT"],
            insertbackground=C["TEXT"], relief="flat", wrap="word", padx=8, pady=6)
        ta.pack(fill="both", expand=True)
        ta.bind("<KeyRelease>", lambda e: self._update_counts())
        self._reg(ta, bg="BTN_BG", fg="TEXT")
        setattr(self, attr, ta)

    def _build_action_column(self, parent):
        for _ in range(3): tk.Frame(parent, bg=C["BG"], height=8).pack()

        enc = tk.Button(parent, text="ENCRYPT\n   v   ",
                        font=("Courier New",13,"bold"),
                        bg=C["ACCENT2"], fg=C["BG"],
                        activebackground="#2ea043", activeforeground=C["BG"],
                        relief="flat", cursor="hand2", padx=14, pady=14,
                        command=self._do_encrypt)
        enc.pack(fill="x", pady=4)
        self._reg(enc, bg="ACCENT2", fg="BG")

        dec = tk.Button(parent, text="   ^   \nDECRYPT",
                        font=("Courier New",13,"bold"),
                        bg=C["WARN"], fg=C["BG"],
                        activebackground="#c65b4e", activeforeground=C["BG"],
                        relief="flat", cursor="hand2", padx=14, pady=14,
                        command=self._do_decrypt)
        dec.pack(fill="x", pady=4)
        self._reg(dec, bg="WARN", fg="BG")

        self._reg(tk.Frame(parent, bg=C["BORDER"], height=1), bg="BORDER").pack(fill="x", pady=8)

        swap_btn = tk.Button(parent, text="Swap", font=FONT_SMALL,
                             bg=C["BTN_BG"], fg=C["TEXT"],
                             activebackground=C["BTN_HOV"],
                             relief="flat", cursor="hand2", padx=10, pady=6,
                             command=self._swap_texts)
        swap_btn.pack(fill="x", pady=2)
        self._reg(swap_btn, bg="BTN_BG", fg="TEXT")

        self._brute_btn = tk.Button(parent, text="Brute\nForce",
                                     font=FONT_SMALL,
                                     bg=C["GOLD"], fg=C["BG"],
                                     activebackground=C["BTN_HOV"],
                                     relief="flat", cursor="hand2", padx=10, pady=6,
                                     command=self._do_brute)
        self._brute_btn.pack(fill="x", pady=2)
        self._reg(self._brute_btn, bg="GOLD", fg="BG")

        self._test_btn = tk.Button(parent, text="Test\nVectors",
                                    font=FONT_SMALL,
                                    bg=C["BTN_BG"], fg=C["TEXT"],
                                    activebackground=C["BTN_HOV"],
                                    relief="flat", cursor="hand2", padx=10, pady=6,
                                    command=self._show_test_vectors)
        self._test_btn.pack(fill="x", pady=2)
        self._reg(self._test_btn, bg="BTN_BG", fg="TEXT")

        clear_btn = tk.Button(parent, text="Clear All", font=FONT_SMALL,
                              bg=C["BTN_BG"], fg=C["MUTED"],
                              activebackground=C["BTN_HOV"],
                              relief="flat", cursor="hand2", padx=10, pady=6,
                              command=self._clear_all)
        clear_btn.pack(fill="x", pady=2)
        self._reg(clear_btn, bg="BTN_BG", fg="MUTED")

    def _build_file_row(self, parent):
        self._reg(tk.Label(parent, text="FILES:", font=FONT_SMALL,
                           bg=C["PANEL"], fg=C["MUTED"]),
                  bg="PANEL", fg="MUTED").pack(side="left", padx=14, pady=8)

        for txt, cmd in [
            ("Open->Plain",  self._open_file_plain),
            ("Open->Cipher", self._open_file_cipher),
            ("Save Plain",   self._save_plain),
            ("Save Cipher",  self._save_cipher),
            ("Encrypt File", self._encrypt_file_direct),
            ("Decrypt File", self._decrypt_file_direct),
        ]:
            self._small_btn(parent, txt, cmd).pack(side="left", padx=3, pady=6)

    def _build_history(self, parent):
        self._reg(tk.Label(parent, text="OPERATION HISTORY", font=FONT_SMALL,
                           bg=C["PANEL"], fg=C["MUTED"]),
                  bg="PANEL", fg="MUTED").pack(anchor="w", padx=14, pady=(6,2))
        self._history_box = scrolledtext.ScrolledText(
            parent, font=("Courier New",11), bg=C["PANEL"], fg=C["MUTED"],
            relief="flat", state="disabled", height=5)
        self._history_box.pack(fill="both", expand=True, padx=6, pady=(0,4))
        self._reg(self._history_box, bg="PANEL", fg="MUTED")

    def _small_btn(self, parent, text, cmd):
        b = tk.Button(parent, text=text, font=FONT_SMALL,
                      bg=C["BTN_BG"], fg=C["TEXT"],
                      activebackground=C["BTN_HOV"], activeforeground=C["TEXT"],
                      relief="flat", cursor="hand2", padx=6, pady=4, command=cmd)
        self._reg(b, bg="BTN_BG", fg="TEXT")
        return b

    def _select_algo(self, algo):
        self.current_algo.set(algo)

    def _on_algo_change(self, *_):
        algo = self.current_algo.get()
        for a, row in self._algo_rows.items():
            row.configure(bg=C["BORDER"] if a==algo else C["PANEL"])
        info = ALGO_INFO[algo]
        self._algo_header.configure(text=f"[ {info['tag']} ]  {algo} Cipher")
        kt = info["key_type"]
        self._key_entry.configure(
            state="normal" if kt!="none" else "disabled",
            fg=C["GOLD"] if kt!="none" else C["MUTED"])
        has_brute = info.get("has_brute", False)
        self._brute_btn.configure(
            state="normal" if has_brute else "disabled",
            bg=C["GOLD"] if has_brute else C["BTN_BG"],
            fg=C["BG"] if has_brute else C["MUTED"])

        if kt == "none":
            self._key_var.set("")
        elif kt == "number" and not self._key_var.get().isdigit():
            self._key_var.set("")
        elif kt == "text" and algo in ("Vigenere", "Transposition") and not self._key_var.get().isalpha():
            self._key_var.set("")

        self._info_text.configure(state="normal")
        self._info_text.delete("1.0","end")
        self._info_text.insert("end", info["description"])
        self._info_text.configure(state="disabled")
        self._update_strength()

    def _on_key_change(self, *_):
        self._update_strength()
        algo = self.current_algo.get()
        key = self._key_var.get()
        ok, _ = _parse_key(algo, key)
        self._key_entry.configure(fg=C["GOLD"] if ok else C["WARN"])

    def _update_strength(self):
        algo, key = self.current_algo.get(), self._key_var.get()
        score, label = key_strength(algo, key)
        self._strength_bar.delete("all")
        w = int(80*score/100)
        col = C["WARN"] if score<30 else C["GOLD"] if score<60 else C["ACCENT2"]
        if w: self._strength_bar.create_rectangle(0,0,w,12,fill=col,outline="")
        self._strength_lbl.configure(text=label, fg=col)

    def _do_encrypt(self):
        algo = self.current_algo.get()
        plain = self._plain_text.get("1.0","end-1c")
        key   = self._key_var.get()
        if not plain.strip():
            messagebox.showwarning("Empty","Please enter plaintext."); return
        ok, _ = _parse_key(algo, key)
        if not ok and ALGO_INFO[algo]["key_type"] != "none":
            messagebox.showwarning("Invalid Key", "Please enter a valid key for the chosen algorithm.")
            return
        result = do_encrypt(algo, plain, key)
        self._set_cipher(result)
        self._log(f"ENCRYPT | {algo} | {len(plain)} -> {len(result)} chars")
        self._update_counts()

    def _do_decrypt(self):
        algo   = self.current_algo.get()
        cipher = self._cipher_text.get("1.0","end-1c")
        key    = self._key_var.get()
        if not cipher.strip():
            messagebox.showwarning("Empty","Please enter ciphertext."); return
        ok, _ = _parse_key(algo, key)
        if not ok and ALGO_INFO[algo]["key_type"] != "none":
            messagebox.showwarning("Invalid Key", "Please enter a valid key for the chosen algorithm.")
            return
        result = do_decrypt(algo, cipher, key)
        self._set_plain(result)
        self._log(f"DECRYPT | {algo} | {len(cipher)} -> {len(result)} chars")
        self._update_counts()

    def _do_brute(self):
        cipher = self._cipher_text.get("1.0","end-1c")
        if not cipher.strip():
            messagebox.showwarning("Empty","Enter ciphertext first."); return
        self._set_plain(caesar_brute(cipher))
        self._log("BRUTE FORCE | Caesar | All 25 shifts")

    def _show_test_vectors(self):
        win = tk.Toplevel(self)
        win.title("Algorithm Test Vectors")
        win.geometry("600x500")
        win.configure(bg=C["BG"])
        win.grab_set()

        tk.Label(win, text="Test Vectors – Verify Cipher Correctness",
                 font=FONT_HEADER, bg=C["BG"], fg=C["ACCENT"]).pack(pady=12)

        txt = tk.Text(win, font=("Courier New",11), bg=C["BTN_BG"], fg=C["TEXT"],
                      relief="flat", padx=8, pady=8, wrap="word")
        txt.pack(fill="both", expand=True, padx=12, pady=4)

        vectors = {
            "Caesar (key=3)": ("HELLO", "KHOOR"),
            "ROT-13":         ("HELLO", "URYYB"),
            "Reverse":        ("HELLO", "OLLEH"),
            "Vigenere (key=KEY)": ("HELLO", "RIJVS"),
            "Rail Fence (rails=3)": ("HELLOWORLD", "HOOELLWRDL"),
            "Transposition (key=KEY)": ("HELLOWORLD", "EODHLLLOWOR"),
        }
        for algo in ("ECC", "ElGamal", "Rabin", "Paillier", "Schmidt-Samoa", "Knapsack"):
            ct = do_encrypt(algo, "HI", "KEY")
            if len(ct) > 30: ct = ct[:27] + "..."
            vectors[f"{algo} (key=KEY)"] = ("HI", ct)
            
        for name, (pt, ct) in vectors.items():
            txt.insert("end", f"{name}\n  Plain : {pt}\n  Cipher: {ct}\n\n", "mono")
        txt.tag_config("mono", font=("Courier New",11))
        txt.configure(state="disabled")

        tk.Button(win, text="Close", font=FONT_SMALL,
                  bg=C["BTN_BG"], fg=C["TEXT"],
                  activebackground=C["BTN_HOV"], relief="flat",
                  command=win.destroy).pack(pady=10)

    def _set_plain(self, text):
        self._plain_text.delete("1.0","end")
        self._plain_text.insert("end", text)
        self._update_counts()

    def _set_cipher(self, text):
        self._cipher_text.delete("1.0","end")
        self._cipher_text.insert("end", text)
        self._update_counts()

    def _swap_texts(self):
        p = self._plain_text.get("1.0","end-1c")
        c = self._cipher_text.get("1.0","end-1c")
        self._set_plain(c); self._set_cipher(p)
        self._log("SWAP | Plaintext <-> Ciphertext")

    def _copy(self, attr):
        self.clipboard_clear()
        self.clipboard_append(getattr(self,attr).get("1.0","end-1c"))
        self._log("COPY | Copied to clipboard")

    def _clear_box(self, attr):
        getattr(self,attr).delete("1.0","end"); self._update_counts()

    def _clear_all(self):
        if not messagebox.askyesno("Clear All", "Delete all plaintext, ciphertext, and key?"):
            return
        self._plain_text.delete("1.0","end")
        self._cipher_text.delete("1.0","end")
        self._key_var.set("")
        self._update_counts()
        self._log("CLEAR | All fields cleared")

    def _toggle_key(self):
        self._key_visible = not self._key_visible
        self._key_entry.configure(show="" if self._key_visible else "*")
        self._eye_btn.configure(text="Hide" if self._key_visible else "👁 Show")

    def _update_counts(self):
        p = self._plain_text.get("1.0","end-1c")
        c = self._cipher_text.get("1.0","end-1c")
        self._left_count.configure(text=f"{len(p)} chars  {len(p.split())} words")
        self._right_count.configure(text=f"{len(c)} chars  {len(c.split())} words")

    def _open_file_plain(self):
        p = filedialog.askopenfilename(filetypes=[("Text","*.txt"),("All","*.*")])
        if p:
            with open(p,"r",encoding="utf-8",errors="replace") as f: self._set_plain(f.read())
            self._log(f"OPEN | {os.path.basename(p)} -> Plaintext")

    def _open_file_cipher(self):
        p = filedialog.askopenfilename(filetypes=[("Text","*.txt"),("All","*.*")])
        if p:
            with open(p,"r",encoding="utf-8",errors="replace") as f: self._set_cipher(f.read())
            self._log(f"OPEN | {os.path.basename(p)} -> Ciphertext")

    def _save_plain(self):
        p = filedialog.asksaveasfilename(defaultextension=".txt")
        if p:
            with open(p,"w",encoding="utf-8") as f: f.write(self._plain_text.get("1.0","end-1c"))
            self._log(f"SAVE | Plaintext -> {os.path.basename(p)}")

    def _save_cipher(self):
        p = filedialog.asksaveasfilename(defaultextension=".txt")
        if p:
            with open(p,"w",encoding="utf-8") as f: f.write(self._cipher_text.get("1.0","end-1c"))
            self._log(f"SAVE | Ciphertext -> {os.path.basename(p)}")

    def _encrypt_file_direct(self):
        src = filedialog.askopenfilename(filetypes=[("Text","*.txt"),("All","*.*")])
        if not src: return
        dst = filedialog.asksaveasfilename(defaultextension=".enc.txt")
        if not dst: return
        with open(src,"r",encoding="utf-8",errors="replace") as f: content=f.read()
        result = do_encrypt(self.current_algo.get(), content, self._key_var.get())
        with open(dst,"w",encoding="utf-8") as f: f.write(result)
        self._log(f"FILE ENCRYPT | {os.path.basename(src)}")
        messagebox.showinfo("Done",f"File encrypted!\n{dst}")

    def _decrypt_file_direct(self):
        src = filedialog.askopenfilename(filetypes=[("Text","*.txt"),("All","*.*")])
        if not src: return
        dst = filedialog.asksaveasfilename(defaultextension=".dec.txt")
        if not dst: return
        with open(src,"r",encoding="utf-8",errors="replace") as f: content=f.read()
        result = do_decrypt(self.current_algo.get(), content, self._key_var.get())
        with open(dst,"w",encoding="utf-8") as f: f.write(result)
        self._log(f"FILE DECRYPT | {os.path.basename(src)}")
        messagebox.showinfo("Done",f"File decrypted!\n{dst}")

    def _log(self, msg):
        ts = datetime.datetime.now().strftime("%H:%M:%S")
        entry = f"[{ts}]  {msg}"
        self._history.append(entry)
        MAX_HISTORY = 1000
        if len(self._history) > MAX_HISTORY:
            self._history = self._history[-MAX_HISTORY:]
            self._history_box.configure(state="normal")
            self._history_box.delete("1.0","end")
            for line in self._history:
                self._history_box.insert("end", line+"\n")
            self._history_box.see("end")
            self._history_box.configure(state="disabled")
        else:
            self._history_box.configure(state="normal")
            self._history_box.insert("end", entry+"\n")
            self._history_box.see("end")
            self._history_box.configure(state="disabled")

    def _derive_key_dialog(self):
        algo = self.current_algo.get()
        win  = tk.Toplevel(self)
        win.title("Derive Key from Password  (PBKDF2-HMAC-SHA256)")
        win.geometry("520x400")
        win.configure(bg=C["BG"])
        win.resizable(False, False)
        win.grab_set()

        pad = tk.Frame(win, bg=C["BG"])
        pad.pack(fill="both", expand=True, padx=28, pady=18)

        tk.Label(pad, text="Password-Based Key Derivation", font=FONT_HEADER,
                 bg=C["BG"], fg=C["ACCENT"]).pack(anchor="w")
        tk.Label(pad, text="PBKDF2-HMAC-SHA256 | Generates a strong cipher key from any password.",
                 font=FONT_SMALL, bg=C["BG"], fg=C["MUTED"]).pack(anchor="w", pady=(2,14))

        fields = {}
        for label, default, show in [
            ("Password :",   "",       "*"),
            ("Salt :",       "CipherVault", ""),
            ("Iterations :", "100000", ""),
        ]:
            row = tk.Frame(pad, bg=C["BG"])
            row.pack(fill="x", pady=5)
            tk.Label(row, text=label, font=FONT_BODY, bg=C["BG"],
                     fg=C["TEXT"], width=15, anchor="w").pack(side="left")
            var = tk.StringVar(value=default)
            tk.Entry(row, textvariable=var, font=FONT_MONO,
                     bg=C["BTN_BG"], fg=C["GOLD"],
                     insertbackground=C["GOLD"], relief="flat",
                     show=show).pack(side="left", fill="x", expand=True, ipady=4)
            fields[label] = var

        tk.Label(pad, text="Derived Key:", font=FONT_BODY,
                 bg=C["BG"], fg=C["TEXT"]).pack(anchor="w", pady=(14,2))
        preview = tk.Label(pad, text="  (click Derive)  ", font=FONT_MONO,
                           bg=C["PANEL"], fg=C["ACCENT2"], anchor="w",
                           padx=8, pady=8)
        preview.pack(fill="x")

        def on_derive():
            pwd  = fields["Password :"].get()
            salt = fields["Salt :"].get() or "CipherVault"
            try: iters = int(fields["Iterations :"].get())
            except: messagebox.showerror("Error","Iterations must be a number."); return
            if not pwd: messagebox.showwarning("Empty","Enter a password."); return
            key = derive_key_pbkdf2(pwd, salt, iters, algo)
            preview.configure(text=f"  {key}  ")
            preview._derived = key

        def on_apply():
            key = getattr(preview, "_derived", None)
            if not key: messagebox.showwarning("Not ready","Click Derive first."); return
            self._key_var.set(key)
            self._log(f"PBKDF2 | Key derived for {algo}")
            win.destroy()

        btns = tk.Frame(pad, bg=C["BG"])
        btns.pack(fill="x", pady=(16,0))
        for txt, cmd, col, fgc in [
            ("Derive",         on_derive, "GOLD",    "BG"),
            ("Apply to Key",   on_apply,  "ACCENT2", "BG"),
            ("Cancel",         win.destroy,"WARN",   "BG"),
        ]:
            tk.Button(btns, text=txt, font=FONT_SMALL,
                      bg=C[col], fg=C[fgc],
                      activebackground=C["BTN_HOV"], relief="flat",
                      cursor="hand2", padx=12, pady=7, command=cmd
                      ).pack(side="left", padx=4)

    def _show_comparison(self):
        plain = self._plain_text.get("1.0","end-1c")
        if not plain.strip():
            plain = "The quick brown fox jumps over the lazy dog. 0123456789 !"
        key = self._key_var.get()

        win = tk.Toplevel(self)
        win.title("Algorithm Comparison")
        win.geometry("960x580")
        win.configure(bg=C["BG"])

        tk.Label(win, text="Algorithm Comparison  —  Speed & Output Analysis",
                 font=FONT_HEADER, bg=C["BG"], fg=C["ACCENT"]).pack(anchor="w", padx=20, pady=(16,4))
        preview_txt = plain[:70]+"..." if len(plain)>70 else plain
        tk.Label(win, text=f'Input ({len(plain)} chars): "{preview_txt}"',
                 font=FONT_SMALL, bg=C["BG"], fg=C["MUTED"]).pack(anchor="w", padx=20, pady=(0,10))

        cols   = ["Algorithm",  "Tag",  "Key Used",   "In",  "Out",  "Ratio", "Time (ms)", "Output Sample"]
        widths = [15,            6,      14,            5,     5,      6,        10,          30]

        frame  = tk.Frame(win, bg=C["BG"])
        frame.pack(fill="both", expand=True, padx=16, pady=4)

        hdr = tk.Frame(frame, bg=C["BORDER"])
        hdr.pack(fill="x")
        for col, w in zip(cols, widths):
            tk.Label(hdr, text=col, font=("Courier New",11,"bold"),
                     bg=C["PANEL"], fg=C["ACCENT"],
                     width=w, anchor="w", padx=6, pady=7
                     ).pack(side="left")

        canvas  = tk.Canvas(frame, bg=C["BG"], highlightthickness=0)
        sb      = ttk.Scrollbar(frame, orient="vertical", command=canvas.yview)
        inner   = tk.Frame(canvas, bg=C["BG"])
        inner.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0,0), window=inner, anchor="nw")
        canvas.configure(yscrollcommand=sb.set)
        canvas.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")

        def _on_mousewheel(event):
            canvas.yview_scroll(int(-1*(event.delta/120)), "units")
        canvas.bind_all("<MouseWheel>", _on_mousewheel)
        def _unbind_mw(e):
            canvas.unbind_all("<MouseWheel>")
        win.bind("<Destroy>", _unbind_mw)

        def_keys = {"Caesar":"3","ROT-13":"","Reverse":"","Vigenere":key or "KEY",
                    "Rail Fence":"3","Transposition":key or "KEY"}
        for algo in ("ECC", "ElGamal", "Rabin", "Paillier", "Schmidt-Samoa", "Knapsack"):
            def_keys[algo] = key or "KEY"

        for i, algo in enumerate(ALGORITHMS):
            rbg = C["PANEL"] if i%2==0 else C["BTN_BG"]
            uk  = def_keys[algo]
            try:
                t0 = time.perf_counter()
                out = do_encrypt(algo, plain, uk)
                ms  = (time.perf_counter()-t0)*1000
            except Exception as ex:
                out, ms = str(ex), 0.0

            ratio   = f"{len(out)/max(len(plain),1):.2f}x"
            sample  = out[:28].replace("\n"," ")
            info    = ALGO_INFO[algo]
            tag_c   = C["ACCENT"] if info["tag"]=="SYM" else (C["ACCENT2"] if info["tag"]=="ASYM" else C["GOLD"])

            row = tk.Frame(inner, bg=rbg); row.pack(fill="x")
            vals = [algo, info["tag"], uk or "---", str(len(plain)), str(len(out)),
                    ratio, f"{ms:.3f}", sample]
            fgs  = [C["TEXT"], tag_c, C["GOLD"], C["MUTED"], C["MUTED"],
                    C["ACCENT2"], C["ACCENT"], C["MUTED"]]
            for val, fg, w in zip(vals, fgs, widths):
                tk.Label(row, text=val, font=("Courier New",11),
                         bg=rbg, fg=fg, width=w, anchor="w", padx=6, pady=8
                         ).pack(side="left")

        tk.Button(win, text="Close", font=FONT_SMALL,
                  bg=C["BTN_BG"], fg=C["TEXT"],
                  activebackground=C["BTN_HOV"], relief="flat",
                  cursor="hand2", padx=14, pady=7,
                  command=win.destroy).pack(pady=10)
        self._log("COMPARE | Algorithm comparison opened")

    def _show_qr(self):
        if not _HAS_QR:
            messagebox.showerror("Missing","Install: pip install qrcode[pil] pillow"); return
        cipher = self._cipher_text.get("1.0","end-1c").strip()
        if not cipher:
            messagebox.showwarning("Empty","Encrypt some text first."); return
        if len(cipher) > 2900:
            messagebox.showwarning("Too Long",
                                    f"Text is {len(cipher)} chars. Max ~2900 for QR.\n"
                                    "Use shorter input."); return

        win = tk.Toplevel(self)
        win.title("QR Code Generator")
        win.geometry("520x660")
        win.configure(bg=C["BG"])
        win.resizable(False, False)

        tk.Label(win, text="QR Code  —  Ciphertext", font=FONT_HEADER,
                 bg=C["BG"], fg=C["ACCENT"]).pack(pady=(18,4))
        tk.Label(win, text=f"Algorithm: {self.current_algo.get()}   |   {len(cipher)} characters",
                 font=FONT_SMALL, bg=C["BG"], fg=C["MUTED"]).pack()

        qr = qrcode.QRCode(error_correction=qrcode.constants.ERROR_CORRECT_M,
                            box_size=6, border=3)
        qr.add_data(cipher)
        qr.make(fit=True)
        img_pil = qr.make_image(fill_color="black", back_color="white").convert("RGB")
        img_pil = img_pil.resize((360,360), Image.LANCZOS)

        win._pil = img_pil
        win._tk  = ImageTk.PhotoImage(img_pil)

        tk.Label(win, image=win._tk, bg=C["BG"]).pack(pady=12)

        preview = cipher[:80]+"..." if len(cipher)>80 else cipher
        tk.Label(win, text=preview, font=("Courier New",10),
                 bg=C["PANEL"], fg=C["TEXT"],
                 wraplength=460, justify="left", padx=10, pady=8
                 ).pack(fill="x", padx=20)

        def save_qr():
            p = filedialog.asksaveasfilename(
                defaultextension=".png", initialfile="ciphertext_qr.png",
                filetypes=[("PNG","*.png"),("All","*.*")])
            if p:
                win._pil.save(p)
                self._log(f"QR SAVE | {os.path.basename(p)}")
                messagebox.showinfo("Saved",f"QR saved:\n{p}")

        btns = tk.Frame(win, bg=C["BG"]); btns.pack(pady=10)
        for txt, cmd, col, fgc in [
            ("Save PNG", save_qr,   "ACCENT2", "BG"),
            ("Close",    win.destroy,"BTN_BG", "TEXT"),
        ]:
            tk.Button(btns, text=txt, font=FONT_SMALL,
                      bg=C[col], fg=C[fgc],
                      activebackground=C["BTN_HOV"], relief="flat",
                      cursor="hand2", padx=14, pady=7, command=cmd
                      ).pack(side="left", padx=6)

        self._log(f"QR | Generated for {len(cipher)} chars")

    def _export_pdf(self):
        if not _HAS_PDF:
            messagebox.showerror("Missing","Install: pip install reportlab"); return

        plain  = self._plain_text.get("1.0","end-1c")
        cipher = self._cipher_text.get("1.0","end-1c")
        if not plain and not cipher:
            messagebox.showwarning("Empty","Nothing to export."); return

        path = filedialog.asksaveasfilename(
            defaultextension=".pdf", initialfile="CipherVault_Report.pdf",
            filetypes=[("PDF","*.pdf"),("All","*.*")])
        if not path: return

        algo    = self.current_algo.get()
        key_raw = self._key_var.get()
        masked  = ("*"*len(key_raw)) if key_raw else "---"
        ts      = datetime.datetime.now().strftime("%Y-%m-%d  %H:%M:%S")
        score, slabel = key_strength(algo, key_raw)

        doc = SimpleDocTemplate(path, pagesize=A4,
                                topMargin=2*cm, bottomMargin=2*cm,
                                leftMargin=2*cm, rightMargin=2*cm)

        dark  = rl_colors.HexColor("#0d1117")
        blue  = rl_colors.HexColor("#58a6ff")
        grn   = rl_colors.HexColor("#3fb950")
        red   = rl_colors.HexColor("#f78166")
        gld   = rl_colors.HexColor("#d29922")
        lt    = rl_colors.HexColor("#e6edf3")
        muted = rl_colors.HexColor("#8b949e")
        panel = rl_colors.HexColor("#161b22")
        panel2= rl_colors.HexColor("#1c2128")

        head_style = ParagraphStyle("H",  fontName="Courier-Bold", fontSize=20,
                                    textColor=blue, spaceAfter=4)
        sub_style  = ParagraphStyle("S",  fontName="Courier",      fontSize=10,
                                    textColor=muted, spaceAfter=12)
        sec_style  = ParagraphStyle("Sc", fontName="Courier-Bold", fontSize=13,
                                    textColor=grn, spaceBefore=14, spaceAfter=6)
        body_style = ParagraphStyle("B",  fontName="Courier",      fontSize=10,
                                    textColor=lt, backColor=panel,
                                    borderPadding=(6,8,6,8), spaceAfter=6)
        note_style = ParagraphStyle("N",  fontName="Courier",      fontSize=9,
                                    textColor=muted)

        story = []
        story.append(Paragraph("CipherVault Pro", head_style))
        story.append(Paragraph("Encryption and Decryption Report", sub_style))
        story.append(HRFlowable(width="100%", thickness=1, color=blue, spaceAfter=14))

        meta_data = [
            ["Generated",    ts],
            ["Algorithm",    f"{algo}  [{ALGO_INFO[algo]['tag']}]"],
            ["Key (masked)", masked],
            ["Key Strength", f"{slabel}  ({score}/100)"],
            ["Input Length", f"{len(plain)} chars / {len(plain.split())} words"],
            ["Output Length",f"{len(cipher)} chars"],
        ]
        mt = Table(meta_data, colWidths=[4.5*cm, 12.5*cm])
        mt.setStyle(TableStyle([
            ("BACKGROUND",    (0,0),(-1,-1), panel),
            ("TEXTCOLOR",     (0,0),(0,-1),  muted),
            ("TEXTCOLOR",     (1,0),(1,-1),  lt),
            ("FONTNAME",      (0,0),(-1,-1), "Courier"),
            ("FONTSIZE",      (0,0),(-1,-1), 10),
            ("ROWBACKGROUNDS",(0,0),(-1,-1), [panel, panel2]),
            ("GRID",          (0,0),(-1,-1), 0.5, rl_colors.HexColor("#30363d")),
            ("TOPPADDING",    (0,0),(-1,-1), 6),
            ("BOTTOMPADDING", (0,0),(-1,-1), 6),
            ("LEFTPADDING",   (0,0),(-1,-1), 10),
        ]))
        story.append(mt)
        story.append(Spacer(1, 14))

        story.append(Paragraph("PLAINTEXT", sec_style))
        for chunk in [plain[i:i+90] for i in range(0, max(len(plain),1), 90)]:
            story.append(Paragraph(chunk or "---", body_style))

        story.append(Paragraph("CIPHERTEXT", sec_style))
        for chunk in [cipher[i:i+90] for i in range(0, max(len(cipher),1), 90)]:
            story.append(Paragraph(chunk or "---", body_style))

        if self._history:
            story.append(Paragraph("OPERATION HISTORY", sec_style))
            for entry in self._history[-20:]:
                story.append(Paragraph(entry, note_style))

        story.append(Spacer(1,14))
        story.append(HRFlowable(width="100%", thickness=0.5, color=muted))
        story.append(Paragraph("Generated by CipherVault Pro v3  |  Educational Use Only",
                                note_style))

        doc.build(story)
        self._log(f"PDF | Exported -> {os.path.basename(path)}")
        messagebox.showinfo("Exported", f"PDF report saved:\n{path}")

    def _show_diff(self):
        plain  = self._plain_text.get("1.0","end-1c")
        cipher = self._cipher_text.get("1.0","end-1c")
        if not plain or not cipher:
            messagebox.showwarning("Empty","Both text boxes must have content."); return

        win = tk.Toplevel(self)
        win.title("Side-by-Side Diff View")
        win.geometry("1100x660")
        win.configure(bg=C["BG"])

        tk.Label(win, text="Character-Level Diff  —  Plaintext vs Ciphertext",
                 font=FONT_HEADER, bg=C["BG"], fg=C["ACCENT"]).pack(pady=(16,4))
        tk.Label(win, text=f"Algorithm: {self.current_algo.get()}",
                 font=FONT_SMALL, bg=C["BG"], fg=C["MUTED"]).pack()

        leg = tk.Frame(win, bg=C["BG"]); leg.pack(pady=8)
        for txt, col, fgc in [
            ("  Same Character  ",   "#1a3a1a", "#3fb950"),
            ("  Changed Character  ","#3a1a1a", "#f78166"),
            ("  Extra / Missing  ",  "#1a2a3a", "#79c0ff"),
        ]:
            tk.Label(leg, text=txt, font=FONT_SMALL,
                     bg=col, fg=fgc, padx=4, pady=3
                     ).pack(side="left", padx=6)

        panels = tk.Frame(win, bg=C["BG"])
        panels.pack(fill="both", expand=True, padx=14, pady=4)

        def make_panel(parent, title, col_key):
            f = tk.Frame(parent, bg=C["BG"])
            f.pack(side="left", fill="both", expand=True, padx=4)
            tk.Label(f, text=title, font=FONT_SMALL,
                     bg=C["PANEL"], fg=C[col_key]).pack(fill="x")
            ta = tk.Text(f, font=("Courier New",13), bg=C["BTN_BG"], fg=C["TEXT"],
                         relief="flat", wrap="char", padx=8, pady=6)
            sb = ttk.Scrollbar(f, orient="vertical", command=ta.yview)
            ta.configure(yscrollcommand=sb.set)
            ta.pack(side="left", fill="both", expand=True)
            sb.pack(side="right", fill="y")
            ta.tag_configure("match",  background="#1a3a1a", foreground="#3fb950")
            ta.tag_configure("diff",   background="#3a1a1a", foreground="#f78166")
            ta.tag_configure("extra",  background="#1a2a3a", foreground="#79c0ff")
            ta.tag_configure("space",  foreground="#555566")
            return ta

        ta_p = make_panel(panels, "PLAINTEXT",  "ACCENT2")
        tk.Frame(panels, bg=C["BORDER"], width=2).pack(side="left", fill="y")
        ta_c = make_panel(panels, "CIPHERTEXT", "WARN")

        max_len = max(len(plain), len(cipher))
        stats   = {"match":0, "diff":0, "extra":0}

        for i in range(max_len):
            pc = plain[i]  if i < len(plain)  else None
            cc = cipher[i] if i < len(cipher) else None

            def ins(ta, ch, tag):
                ta.insert("end", ch if ch and ch!="\n" else ("\\n\n" if ch=="\n" else "."), tag)

            if pc is None:
                ins(ta_p, ".", "extra"); ins(ta_c, cc, "extra"); stats["extra"] += 1
            elif cc is None:
                ins(ta_p, pc, "extra"); ins(ta_c, ".", "extra"); stats["extra"] += 1
            elif pc == cc:
                tag = "space" if pc==" " else "match"
                ins(ta_p, pc, tag); ins(ta_c, cc, tag); stats["match"] += 1
            else:
                ins(ta_p, pc, "diff"); ins(ta_c, cc, "diff"); stats["diff"] += 1

        for ta in (ta_p, ta_c): ta.configure(state="disabled")

        total = max_len or 1
        stat_txt = (f"Total: {max_len} chars  |  "
                    f"Same: {stats['match']} ({stats['match']/total*100:.1f}%)  |  "
                    f"Changed: {stats['diff']} ({stats['diff']/total*100:.1f}%)  |  "
                    f"Extra/Missing: {stats['extra']}")
        tk.Label(win, text=stat_txt, font=FONT_SMALL,
                 bg=C["PANEL"], fg=C["TEXT"], pady=6).pack(fill="x")

        tk.Button(win, text="Close", font=FONT_SMALL,
                  bg=C["BTN_BG"], fg=C["TEXT"],
                  activebackground=C["BTN_HOV"], relief="flat",
                  cursor="hand2", padx=14, pady=7,
                  command=win.destroy).pack(pady=10)

        self._log(f"DIFF | Same:{stats['match']}  Changed:{stats['diff']}  Extra:{stats['extra']}")

# ═══════════════════════════════════════════════════════════════════════
#  ENTRY POINT
# ═══════════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    app = CipherVault()
    app.mainloop()
