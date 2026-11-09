#!/usr/bin/env python3
"""Safely unpack an arXiv e-print (gzip of tar or of a single file) into a NEW empty dir.
Usage: unpack.py EPRINT OUTDIR. Only regular files with safe relative names are written."""
import gzip, io, os, sys, tarfile
src, outd = sys.argv[1], sys.argv[2]
if os.path.exists(outd):
    sys.exit('outdir exists')
os.makedirs(outd)
raw = gzip.decompress(open(src, 'rb').read())
try:
    tf = tarfile.open(fileobj=io.BytesIO(raw))
    members = tf.getmembers()
except tarfile.ReadError:
    tf = None
if tf is None:
    with open(os.path.join(outd, 'main.tex'), 'xb') as f:
        f.write(raw)
    print('single file', len(raw))
else:
    for m in members:
        n = os.path.normpath(m.name)
        if not m.isfile() or n.startswith('..') or os.path.isabs(n):
            print('skip', m.name, m.type); continue
        p = os.path.join(outd, n)
        os.makedirs(os.path.dirname(p), exist_ok=True)
        with open(p, 'xb') as f:
            f.write(tf.extractfile(m).read())
        print('file', n, m.size)
