"""Print JSON objects (any depth) in a ledger file whose serialisation contains a key (read-only)."""
import json
import sys

path, key = sys.argv[1], sys.argv[2]
data = json.loads(open(path, encoding='utf-8').read())
hits = []


def walk(o, depth=0):
    if isinstance(o, dict):
        s = json.dumps(o, ensure_ascii=False)
        if key in s:
            inner = [v for v in o.values() if key in json.dumps(v, ensure_ascii=False)]
            if depth > 0 and all(not isinstance(v, (dict, list)) for v in inner) or len(s) < 6000:
                hits.append(s)
                return
            for v in o.values():
                walk(v, depth + 1)
    elif isinstance(o, list):
        for v in o:
            walk(v, depth + 1)


walk(data)
for h in hits[:20]:
    print(h[:6000])
    print('----')
print('hits', len(hits))
