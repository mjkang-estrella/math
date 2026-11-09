import pathlib,json,hashlib,datetime
L=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r174')
h=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((L/'results.json').read_text());reserve=json.loads((L/'reservation.json').read_text())
assert set(r)==set(map(str,reserve['ids'])) and len(r)==20
for i,x in r.items():
 raw=(L/f'raw/{i}.jsonl').read_bytes();assert raw.endswith(b'\n') and h(raw)==x['provenance']['raw_sha256']
 d=json.loads(raw);assert d['statement']==x['statement'];assert h(x['statement'].encode())==x['statement_utf8_sha256']
 if i=='372147':
  x['supplementary_source_receipts']=[json.loads(s) for s in (L/'outputs/http.jsonl').read_text().splitlines() if '2508.19646' in json.loads(s)['url']]
reg=json.loads((L/'outputs/registry-screen.json').read_text());assert len(reg['github_queries'])<=8
rows=[json.loads(s) for s in (L/'outputs/sequence-broad.jsonl').read_text().splitlines()]
idx=[x['index'] for x in rows];assert len(rows)==1267 and sorted(idx)==list(range(1267))
assert len({x['pattern'] for x in rows})==1267
r['372160']['coverage']={'all_canonical_three_letter_patterns_of_lengths':[7,8],'patterns':1267,'alphabet_sizes_through':10,'selected_patterns_through_18':8,'note':'Every row is a source-algorithm computation, not all avoiding words or all saturated sequences.'}
ext=L/'outputs/sequence-extended.jsonl'
if ext.exists():r['372160']['extended_search']=[json.loads(s) for s in ext.read_text().splitlines()]
(L/'results.json').write_text(json.dumps(r,indent=2,ensure_ascii=False)+'\n')
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reserved_entries':20,'raw_and_statement_hash_checks':'PASS','canonical_pattern_coverage':'1267/1267, exactly once','excluded':8,'parked':12,'new_endpoints':0,'credit':0}
(L/'outputs/audit.json').write_text(json.dumps(out,indent=2)+'\n')
manifest={str(p.relative_to(L)):h(p.read_bytes()) for p in sorted(L.rglob('*')) if p.is_file() and p.name!='manifest.json'}
(L/'outputs/manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(out)
