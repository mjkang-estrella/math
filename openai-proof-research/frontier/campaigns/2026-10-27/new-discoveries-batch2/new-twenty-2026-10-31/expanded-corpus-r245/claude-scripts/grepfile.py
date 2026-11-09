"""Scoped search of one named file for several literal keys; prints up to K matching snippets per key (read-only).
usage: grepfile.py FILE K key1 key2 ..."""
import sys

path, K = sys.argv[1], int(sys.argv[2])
t = open(path, encoding='utf-8', errors='replace').read()
print('bytes', len(t))
for key in sys.argv[3:]:
    i = 0
    hits = 0
    pos = t.find(key)
    total = t.count(key)
    print('==', key, 'count', total)
    while pos != -1 and hits < K:
        print('   ...', t[max(0, pos - 150):pos + 250].replace('\n', ' '))
        hits += 1
        pos = t.find(key, pos + 1)
