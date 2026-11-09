#!/usr/bin/env python3
"""Compare two hashbind JSON files. Usage: hashcompare.py BEFORE.json AFTER.json"""
import hashlib, json, sys
a = json.load(open(sys.argv[1])); b = json.load(open(sys.argv[2]))
diff = sorted(k for k in set(a) | set(b) if a.get(k) != b.get(k))
print('entries', len(a), len(b), 'differences', len(diff), diff[:10])
for p in sys.argv[1:3]:
    print(p, hashlib.sha256(open(p, 'rb').read()).hexdigest())
