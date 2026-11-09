"""Deterministic HTML -> text: drop script/style, keep block breaks, unescape.
usage: html_text.py BODY OUT.txt [START_MARKER]"""
import html, re, sys

b = open(sys.argv[1], 'rb').read().decode('utf8', 'replace')
if len(sys.argv) > 3:
    i = b.find(sys.argv[3])
    b = b[i:] if i >= 0 else b
b = re.sub(r'(?is)<(script|style|svg)[^>]*>.*?</\1>', ' ', b)
b = re.sub(r'(?i)<(br|/p|/div|/h[1-6]|/li|/tr|/table|/section)[^>]*>', '\n', b)
b = re.sub(r'<[^>]+>', ' ', b)
b = html.unescape(b)
lines = [re.sub(r'[ \t\r\f\v]+', ' ', l).strip() for l in b.split('\n')]
out = '\n'.join(l for l in lines if l)
open(sys.argv[2], 'w').write(out + '\n')
print(len(out))
