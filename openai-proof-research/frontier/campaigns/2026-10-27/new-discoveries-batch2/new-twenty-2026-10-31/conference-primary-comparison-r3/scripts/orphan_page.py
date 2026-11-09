# Wrap an orphan content stream of a truncated PDF COPY in a synthetic page with a merged resource dict. Bytes only.
import re, sys, zlib, hashlib
src, dst, cobj = sys.argv[1], sys.argv[2], int(sys.argv[3])
b = open(src, 'rb').read()
objs = {}
for m in re.finditer(rb'(?<![0-9])(\d+)\s+(\d+)\s+obj\b', b): objs[int(m.group(1))] = m.start()
def body(n):
    off = objs[n]; seg = b[off:off + 2_000_000]; e = seg.find(b'endobj'); return seg[:e if e > 0 else len(seg)]
s = body(cobj); i = s.find(b'stream'); j = i + 6
if s[j:j+2] == b'\r\n': j += 2
elif s[j:j+1] in (b'\n', b'\r'): j += 1
L = int(re.search(rb'/Length\s+(\d+)', s).group(1)); data = zlib.decompress(s[j:j+L])
used = sorted(set(re.findall(rb'/([A-Za-z0-9_+.-]+)\s+[-0-9.]+\s+Tf', data)))
xo = sorted(set(re.findall(rb'/([A-Za-z0-9_+.-]+)\s+Do', data))); gs = sorted(set(re.findall(rb'/([A-Za-z0-9_+.-]+)\s+gs', data)))
print('content bytes', len(data), 'fonts', used, 'xobj', xo, 'gs', gs)
fonts, xobjs, egs = {}, {}, {}
for n in objs:
    t = body(n)[:3000]
    for kind, store in ((rb'/Font', fonts), (rb'/XObject', xobjs), (rb'/ExtGState', egs)):
        m = re.search(kind + rb'\s*<<(.*?)>>', t, re.S)
        if m:
            for name, ref in re.findall(rb'/([A-Za-z0-9_+.-]+)\s+(\d+\s+0\s+R)', m.group(1)): store.setdefault(name, set()).add(ref)
miss = [u for u in used if u not in fonts]; amb = {u.decode(): [r.decode() for r in fonts[u]] for u in used if u in fonts and len(fonts[u]) > 1}
print('missing fonts', miss, 'ambiguous', amb)
def d(store, names): return b' '.join(b'/' + k + b' ' + sorted(store[k])[0] for k in names if k in store)
res = b'<< /Font << ' + d(fonts, used) + b' >> /XObject << ' + d(xobjs, xo) + b' >> /ExtGState << ' + d(egs, gs) + b' >> /ProcSet [/PDF /Text /ImageC /ImageI] >>'
mx = max(objs) + 1; P, PG, C = mx, mx + 1, mx + 2
out = bytearray(b + b'\n'); offs = dict(objs)
offs[PG] = len(out); out += f'{PG} 0 obj\n<< /Type /Page /Parent {P} 0 R /MediaBox [0 0 592 789] /Contents {cobj} 0 R /Resources '.encode() + res + b' >>\nendobj\n'
offs[P] = len(out); out += f'{P} 0 obj\n<< /Type /Pages /Kids [{PG} 0 R] /Count 1 >>\nendobj\n'.encode()
offs[C] = len(out); out += f'{C} 0 obj\n<< /Type /Catalog /Pages {P} 0 R >>\nendobj\n'.encode()
x = len(out); size = C + 1
out += f'xref\n0 {size}\n'.encode() + b'0000000000 65535 f \n'
for k in range(1, size): out += (f'{offs[k]:010d} 00000 n \n' if k in offs else '0000000000 65535 f \n').encode()
out += f'trailer\n<< /Size {size} /Root {C} 0 R >>\nstartxref\n{x}\n%%EOF\n'.encode()
open(dst, 'wb').write(out); print('dst', hashlib.sha256(out).hexdigest())
