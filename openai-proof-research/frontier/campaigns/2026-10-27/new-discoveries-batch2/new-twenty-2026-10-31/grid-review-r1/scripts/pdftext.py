"""Crude pure-Python PDF text extractor (zlib + Tj/TJ strings), written for lane grid-review-r1.

Usage: pdftext.py OUT.txt IN.pdf
Untrusted input is only parsed, never executed. Output is approximate text for keyword grep;
ligatures and math glyphs may be lost.
"""
import re
import sys
import zlib


def unescape(s):
    out = bytearray()
    i = 0
    while i < len(s):
        c = s[i]
        if c == 0x5C and i + 1 < len(s):
            d = s[i + 1]
            m = {ord('n'): 10, ord('r'): 13, ord('t'): 9, ord('b'): 8, ord('f'): 12}
            if d in m:
                out.append(m[d]); i += 2; continue
            if 0x30 <= d <= 0x37:
                j = i + 1
                k = 0
                while j < len(s) and j < i + 4 and 0x30 <= s[j] <= 0x37:
                    k = k * 8 + s[j] - 0x30; j += 1
                out.append(k & 255); i = j; continue
            out.append(d); i += 2; continue
        out.append(c); i += 1
    return bytes(out)


LIG = {0x0C: 'fi', 0x0D: 'fl', 0x0B: 'ff', 0x0E: 'ffi', 0x0F: 'ffl', 0x1B: 'ff', 0x1C: 'fi', 0x1D: 'fl'}


def dec(b):
    return ''.join(LIG.get(x, chr(x) if 32 <= x < 127 else ' ') for x in b)


def main():
    out, inp = sys.argv[1], sys.argv[2]
    data = open(inp, 'rb').read()
    texts = []
    for m in re.finditer(rb'stream\r?\n', data):
        start = m.end()
        end = data.find(b'endstream', start)
        if end < 0:
            continue
        raw = data[start:end]
        try:
            s = zlib.decompressobj().decompress(raw)
        except Exception:
            continue
        if b'BT' not in s:
            continue
        line = []
        for tok in re.finditer(rb'\[((?:[^\]\\]|\\.)*)\]\s*TJ|\(((?:[^)\\]|\\.)*)\)\s*Tj|(T\*|Td|TD|ET)', s, re.S):
            if tok.group(1) is not None:
                for part in re.finditer(rb'\(((?:[^)\\]|\\.)*)\)|(-?\d+\.?\d*)', tok.group(1), re.S):
                    if part.group(1) is not None:
                        line.append(dec(unescape(part.group(1))))
                    elif part.group(2) is not None and float(part.group(2)) < -180:
                        line.append(' ')
            elif tok.group(2) is not None:
                line.append(dec(unescape(tok.group(2))))
            else:
                line.append('\n' if tok.group(3) in (b'T*', b'ET') else ' ')
        texts.append(''.join(line))
    txt = '\n'.join(texts)
    txt = re.sub(r'[ \t]+', ' ', txt)
    open(out, 'w').write(txt)
    print(inp, 'chars', len(txt))


if __name__ == '__main__':
    main()
