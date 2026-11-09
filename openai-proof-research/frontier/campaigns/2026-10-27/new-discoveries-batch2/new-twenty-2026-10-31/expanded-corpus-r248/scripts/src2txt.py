"""Read (untrusted) arXiv e-print bodies IN MEMORY (gzip tar or single gzip file), never extracting to disk;
concatenate .tex/.bbl/.txt members into texts/NAME.tex.txt. Refuses to overwrite.
usage: src2txt.py NAME1 NAME2 ..."""
import os, sys, io, tarfile, gzip
D = '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r248'
os.makedirs(D + '/texts', exist_ok=True)
for name in sys.argv[1:]:
    dst = f'{D}/texts/{name}.tex.txt'
    if os.path.exists(dst):
        print('exists', dst)
        continue
    b = open(f'{D}/sources/{name}.body', 'rb').read()
    parts = []
    try:
        with tarfile.open(fileobj=io.BytesIO(b), mode='r:*') as tf:
            for m in tf.getmembers():
                if m.isfile() and m.name.lower().endswith(('.tex', '.bbl', '.txt', '.sty')) and not m.name.lower().endswith('.sty'):
                    parts.append(f'%%%%%% MEMBER {m.name}\n' + tf.extractfile(m).read().decode('utf-8', 'replace'))
                elif m.isfile():
                    parts.append(f'%%%%%% (binary/other member {m.name} size {m.size})')
    except tarfile.ReadError:
        try:
            parts.append('%%%%%% single gzip file\n' + gzip.decompress(b).decode('utf-8', 'replace'))
        except OSError:
            parts.append('%%%%%% plain\n' + b.decode('utf-8', 'replace'))
    t = '\n'.join(parts)
    with open(dst, 'x', encoding='utf-8') as f:
        f.write(t)
    print(name, len(t))
