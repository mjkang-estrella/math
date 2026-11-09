"""Minimal pure-python text extraction from an (untrusted) PDF: inflate FlateDecode streams and
collect string operands of Tj/TJ/'/" operators, inserting spaces for large TJ kerns and newlines
for Td/TD/T*/ET.  Lossy (custom font encodings, math) but adequate for keyword screening.
Refuses to overwrite. usage: minipdf.py IN.body OUT.txt"""
import os
import re
import sys
import zlib

src, dst = sys.argv[1], sys.argv[2]
if os.path.exists(dst):
    raise SystemExit('refusing to overwrite ' + dst)
data = open(src, 'rb').read()
out = []
for m in re.finditer(rb'stream\r?\n', data):
    start = m.end()
    end = data.find(b'endstream', start)
    if end < 0:
        continue
    raw = data[start:end]
    try:
        s = zlib.decompress(raw)
    except Exception:
        try:
            s = zlib.decompressobj().decompress(raw)
        except Exception:
            continue
    if b'Tj' not in s and b'TJ' not in s:
        continue
    i = 0
    n = len(s)
    buf = []
    tokens = re.finditer(rb'\((?:\\.|[^\\)])*\)|\[|\]|-?\d+\.?\d*|T[jJdD*]|ET|\'|"', s)
    in_arr = False
    for t in tokens:
        tok = t.group(0)
        if tok.startswith(b'('):
            body = tok[1:-1]
            body = re.sub(rb'\\([nrtbf()\\])', lambda mm: {b'n': b'\n', b'r': b'', b't': b' ', b'b': b'', b'f': b'',
                                                           b'(': b'(', b')': b')', b'\\': b'\\'}[mm.group(1)], body)
            body = re.sub(rb'\\([0-7]{1,3})', lambda mm: bytes([int(mm.group(1), 8) & 255]), body)
            buf.append(body.decode('latin-1'))
        elif tok == b'[':
            in_arr = True
        elif tok == b']':
            in_arr = False
        elif in_arr and re.match(rb'-?\d', tok):
            try:
                if float(tok) < -200:
                    buf.append(' ')
            except ValueError:
                pass
        elif tok in (b'Td', b'TD', b'T*', b'ET', b"'", b'"'):
            buf.append('\n' if tok != b'Td' else ' ')
    out.append(''.join(buf))
text = '\n'.join(out)
text = re.sub(r'[ \t]+', ' ', text)
with open(dst, 'x', encoding='utf-8') as f:
    f.write(text)
print('chars', len(text))
