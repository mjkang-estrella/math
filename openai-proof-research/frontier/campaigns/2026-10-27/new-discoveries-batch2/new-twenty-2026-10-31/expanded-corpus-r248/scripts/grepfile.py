"""Scoped search of named files for literal keys (case-insensitive); prints up to K snippets per key (read-only).
usage: grepfile.py K WIDTH FILE [FILE...] -- key1 key2 ..."""
import sys
K, W = int(sys.argv[1]), int(sys.argv[2])
rest = sys.argv[3:]
i = rest.index('--')
files, keys = rest[:i], rest[i + 1:]
for path in files:
    t = open(path, encoding='utf-8', errors='replace').read()
    low = t.lower()
    print('##', path.rsplit('/', 1)[-1], 'chars', len(t))
    for key in keys:
        k = key.lower()
        total = low.count(k)
        print('==', key, 'count', total)
        pos = low.find(k)
        hits = 0
        while pos != -1 and hits < K:
            print('   ...', t[max(0, pos - W // 3):pos + W].replace('\n', ' '))
            hits += 1
            pos = low.find(k, pos + 1)
