import re, sys
b = open(sys.argv[1], 'rb').read()
objs = {}
for m in re.finditer(rb'(?<![0-9])(\d+)\s+(\d+)\s+obj\b', b): objs[int(m.group(1))] = m.start()
pages = {}
for n, off in objs.items():
    seg = b[off:off + 4000]; e = seg.find(b'endobj'); seg = seg[:e if e > 0 else 4000]
    if re.search(rb'/Type\s*/Page(?![s\w])', seg):
        c = re.search(rb'/Contents\s*(\[[^\]]*\]|\d+\s+0\s+R)', seg); r = re.search(rb'/Resources\s*(\d+\s+0\s+R|<<)', seg)
        pages[n] = (c.group(1) if c else None, r.group(1) if r else None, re.sub(rb'\s+', b' ', seg[:500]))
refd = set()
for n, (c, r, s) in pages.items():
    print('PAGE', n, c, r); print('   ', s[:400])
    if c: refd |= {int(x) for x in re.findall(rb'(\d+)\s+0\s+R', c)}
streams = []
for n, off in sorted(objs.items(), key=lambda x: x[1]):
    head = b[off:off + 600]
    if b'stream' in head and n not in refd:
        h = re.sub(rb'\s+', b' ', head[:head.find(b'stream')])
        if b'/Subtype' not in h and b'/Type' not in h: streams.append((n, off, h[:200]))
print('UNREFERENCED plain streams:'); [print(' ', s) for s in streams]
