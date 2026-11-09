"""List tree paths (from a GitHub tree JSON or list of such) containing any of the given substrings (case-insensitive)."""
import json
import sys

path = sys.argv[1]
keys = [k.lower() for k in sys.argv[2:]]
data = json.load(open(path, encoding='utf-8'))
items = []


def walk(o):
    if isinstance(o, dict):
        if 'path' in o and isinstance(o['path'], str):
            items.append((o['path'], o.get('sha'), o.get('size')))
        for v in o.values():
            if isinstance(v, (dict, list)):
                walk(v)
    elif isinstance(o, list):
        for v in o:
            walk(v)


walk(data)
print('paths', len(items))
seen = set()
for p, sha, size in items:
    if any(k in p.lower() for k in keys) and p not in seen:
        seen.add(p)
        print(p, sha, size)
