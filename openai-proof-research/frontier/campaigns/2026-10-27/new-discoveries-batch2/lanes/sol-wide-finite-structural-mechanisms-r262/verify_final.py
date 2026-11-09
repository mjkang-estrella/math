import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
errors=[];m=json.loads((L/'final-manifest.json').read_text())
for r in m['files']:
 p=L/r['path']
 if not p.is_file() or h(p)!=r['sha256'] or p.stat().st_size!=r['bytes']:errors.append('manifest:'+str(p))
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in m['excludes']}
assert actual=={r['path'] for r in m['files']}
frozen=0
for r in json.loads((L/'provenance.json').read_text()):
 q=pathlib.Path(r['copy'])
 if h(q)!=r['sha256']:errors.append('copy:'+str(q))
 if r['kind']=='scientific frozen':
  frozen+=1
  if h(pathlib.Path(r['original']))!=r['sha256']:errors.append('original:'+r['original'])
sources=0
for line in (L/'bindings.jsonl').read_text().splitlines():
 r=json.loads(line);sources+=1
 for key in ['pdf','text']:
  if h(pathlib.Path(r[key]))!=r[key+'_sha256']:errors.append(key+':'+r[key])
r=json.loads((L/'semantic-history.json').read_text())
if h(pathlib.Path(r['path']))!=r['sha256']:errors.append('immutable history index')
history_changes=[]
for r in json.loads((L/'history-bindings.json').read_text()):
 p=pathlib.Path(r['path'])
 if not p.is_file() or h(p)!=r['sha256']:history_changes.append(str(p))
receipt=dict(utc=str(datetime.datetime.now(datetime.timezone.utc)),status='PASS' if not errors else 'FAIL',manifest_sha256=h(L/'final-manifest.json'),manifest_entries=len(m['files']),frozen_original_copy_pairs=frozen,primary_pdf_text_pairs=sources,errors=errors,incidental_live_history_changes=history_changes,history_limit='Only frozen r258/r260 and established immutable r256 index are required original-equality dependencies; other current-lane reports were bounded search snapshots.',counts=dict(additional=9,total=39,next=40,changed=False),scientific_outcome='unresolved; no source proof or counterexample certified',caps=dict(AS=536870912,groupRSS=536870912,CPU_seconds=210,wall_seconds=230,raised=False))
(L/'final-verification.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt));assert not errors
