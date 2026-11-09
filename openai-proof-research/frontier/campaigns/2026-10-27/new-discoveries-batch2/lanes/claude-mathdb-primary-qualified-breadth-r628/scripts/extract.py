# Extract reserved literal records from the 20 in-place r301 chunks into this lane (read-only on corpus).
import hashlib, json, os, sys
L = os.path.abspath(sys.argv[1]); O = os.path.join(L, 'claude-mathdb-primary-qualified-breadth-r628')
ids = set(json.load(open(os.path.join(L, 'root-mathdb-curvature-adjudication-r627', 'reserved-ids-r628.json')))['ids'])
C = os.path.join(L, 'pi-mathdb-full-corpus-inventory-r301', 'corpus'); out = []
for fn in sorted(os.listdir(C)):
    if not fn.startswith('mathdb-normalized-chunk-'): continue
    with open(os.path.join(C, fn), 'rb') as f:
        for ln, b in enumerate(f, 1):
            x = json.loads(b)
            if x.get('mathdb_id') in ids:
                st = x.get('statement')
                out.append({'mathdb_id': x['mathdb_id'], 'chunk': 'pi-mathdb-full-corpus-inventory-r301/corpus/' + fn, 'line': ln,
                            'literal_line_sha256': hashlib.sha256(b).hexdigest(),
                            'canonical_record_sha256': hashlib.sha256(json.dumps(x, ensure_ascii=False, sort_keys=True, separators=(',', ':')).encode('utf-8')).hexdigest(),
                            'statement_utf8_sha256': hashlib.sha256(st.encode('utf-8')).hexdigest() if isinstance(st, str) else None,
                            'record': x})
out.sort(key=lambda r: r['mathdb_id'])
assert len(out) == 50 and len({r['mathdb_id'] for r in out}) == 50, len(out)
with open(os.path.join(O, 'literal-records.json'), 'w', encoding='utf-8') as f:
    f.write(json.dumps(out, ensure_ascii=False, indent=1) + '\n')
print(len(out))
