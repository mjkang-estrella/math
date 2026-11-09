# Append a fresh Pages tree, catalog and xref to a COPY of a truncated PDF (bytes only; no code from the PDF executed).
import re, sys, hashlib
src, dst = sys.argv[1], sys.argv[2]
b = open(src, 'rb').read()
objs = {}
for m in re.finditer(rb'(?<![0-9])(\d+)\s+(\d+)\s+obj\b', b):
    objs[int(m.group(1))] = m.start()          # last definition wins
pages = []
for n, off in sorted(objs.items(), key=lambda x: x[1]):
    seg = b[off:off + 3000]
    end = seg.find(b'endobj'); seg = seg[:end if end > 0 else 3000]
    if re.search(rb'/Type\s*/Page(?![s\w])', seg): pages.append((n, off, seg[:300]))
print('objects', len(objs), 'pages', [(n, off) for n, off, _ in pages])
mx = max(objs) + 1
P, C = mx, mx + 1
out = bytearray(b if b.endswith(b'\n') else b + b'\n')
offs = dict(objs)
offs[P] = len(out); out += (f'{P} 0 obj\n<< /Type /Pages /Kids [' + ' '.join(f'{n} 0 R' for n, _, _ in pages) + f'] /Count {len(pages)} >>\nendobj\n').encode()
offs[C] = len(out); out += f'{C} 0 obj\n<< /Type /Catalog /Pages {P} 0 R >>\nendobj\n'.encode()
x = len(out); size = C + 1
out += f'xref\n0 {size}\n'.encode() + b'0000000000 65535 f \n'
for i in range(1, size):
    out += (f'{offs[i]:010d} 00000 n \n' if i in offs else '0000000000 65535 f \n').encode()
out += f'trailer\n<< /Size {size} /Root {C} 0 R >>\nstartxref\n{x}\n%%EOF\n'.encode()
open(dst, 'wb').write(out)
print('src', hashlib.sha256(b).hexdigest(), 'dst', hashlib.sha256(out).hexdigest())
