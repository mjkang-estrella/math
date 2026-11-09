"""Bind the exact MathDB 324342 raw corpus line (chunk 0002, line 3870).
   python3 -I -B scripts/mathdb_bind.py CHUNK OUT_DIR"""
import hashlib, json, sys
chunk, out = sys.argv[1], sys.argv[2]
data = open(chunk, 'rb').read()
lines = data.split(b'\n')
raw = lines[3870 - 1]
rec = json.loads(raw)
assert rec['mathdb_id'] == 324342, rec['mathdb_id']
open(out + '/324342.raw.jsonl', 'wb').write(raw + b'\n')
held = open('../held-reopen-r1/324342.raw.jsonl', 'rb').read()
b = {
    'chunk_path': chunk, 'chunk_sha256': hashlib.sha256(data).hexdigest(), 'line_number': 3870,
    'line_sha256_without_newline': hashlib.sha256(raw).hexdigest(),
    'line_sha256_with_newline': hashlib.sha256(raw + b'\n').hexdigest(),
    'raw_line_bytes': len(raw),
    'held_reopen_r1_raw_jsonl_identical': held == raw + b'\n' or held == raw,
    'mathdb_id': rec['mathdb_id'], 'uuid': rec['uuid'], 'canonical_url': rec['canonical_url'], 'title': rec['title'],
    'statement': rec['statement'], 'source_name': rec['source_name'], 'source_url': rec['source_url'],
    'status_in_snapshot': rec['status'], 'solution_count_in_snapshot': rec['solution_count'],
    'retrieval_source': rec['retrieval_source'], 'lastmod': rec['lastmod'],
    'note': 'Cached corpus snapshot only; it does not certify the live MathDB page state.'
}
json.dump(b, open(out + '/mathdb-binding.json', 'w'), indent=1, ensure_ascii=False)
print(json.dumps({k: b[k] for k in ('chunk_sha256', 'line_sha256_without_newline', 'line_sha256_with_newline', 'held_reopen_r1_raw_jsonl_identical')}, indent=1))
