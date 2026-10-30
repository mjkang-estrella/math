import json,hashlib,sys,datetime
from pathlib import Path
L=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
def write(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
def row(p):
 b=p.read_bytes();return dict(path=str(p.relative_to(L)),bytes=len(b),sha256=sha(b))
excluded={'finalmanifest.json','manifest-verification.json'}
if sys.argv[1]=='seal':
 refs=[]
 for lane,n in [('sol-fresh-source-discovery-r147','history-receipt.json'),('sol-fresh-source-discovery-r148','history-initial.json'),('sol-fresh-source-discovery-r145','history-exact.json')]:
  p=L.parent/lane/n;refs.append(dict(path=str(p),sha256=sha(p.read_bytes())))
 write('provenance.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),decision='honest zero',count_context=dict(additional=9,total=39,next=40,edited=False),omega_fixed='490f6bccbf445ab8e111a16b0b8670a5dd7c9a9c',openai_fixed='7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a',retrievals=[json.loads(s) for s in (L/'http.jsonl').read_text().splitlines()],retained_indexes=refs,history=dict(paths=1622,changed_new=6,missing=0,full_body_lexical=True,semantic_absence=False,r145_broad_aliases_freshly_searched=False,new_nested_coverage=False,r111_r113_preserved=True),coverage_limits=['aa026-to-a19a capped300','a19a-to-490f capped300','selected retained baseline paths only; no whole-registry body clearance','publisher journal body403; latest arXiv read','no independent full audit of localization or thesis','no Lean replay or global novelty clearance'],read_extents='discovery.md gives exact theorem/proof bodies and missing bridges',resource=dict(guard_sha256='825ee0d48177cd12354cdbf36fd36b61f0503ff3241356a7bf638ee0bc49fa45',AS_bytes=536870912,group_RSS_bytes=536870912,CPU_seconds=210,wall_seconds=230,sample_ms=40,unsampled_transients_excluded=False),public_proof=dict(doi='10.5281/zenodo.22637968',published='2026-09-07',created='2026-09-07T07:22:46.633127+00:00',scope='Viakhirev Conjecture10 all stated densities; actual Cor2.2/Lemma3.1/Theorem2.1 proofs read'),primary_files=[row(p) for p in sorted((L/'sources').iterdir()) if p.is_file()],no_full_result=True))
 science=[]
 for p in sorted(L.rglob('*')):
  if not p.is_file():continue
  rel=str(p.relative_to(L))
  if p.name in {'SUMMARY.md','discovery.md','checks.py','check-results.json','provenance.json','work.py','run-checks.sh','finalize.py'} or rel.startswith('sources/') or rel.startswith('reopened/') or rel in {'alias-queries.jsonl','registry-path-screen.json','baseline-target-paths.json','http.jsonl'}:science.append(row(p))
 write('scientific-freeze.json',dict(entries=science,excluded_mutable_context=['context-NEXT.md','context-reading.log'],source_scope='full ordinary source resolution absent; controls uncredited'))
 entries=[row(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in excluded]
 write('finalmanifest.json',dict(schema_version=1,entries=entries,excluded=sorted(excluded)))
 print('sealed',len(entries),'manifest entries;',len(science),'scientific entries')
elif sys.argv[1]=='verify':
 j=json.loads((L/'finalmanifest.json').read_bytes());actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in excluded}
 assert actual=={x['path'] for x in j['entries']}
 for n in ['finalmanifest.json','scientific-freeze.json']:
  for r in json.loads((L/n).read_bytes())['entries']:
   p=L/r['path'];assert row(p)==r,r['path']
 assert 'context-NEXT.md' not in {r['path'] for r in json.loads((L/'scientific-freeze.json').read_bytes())['entries']}
 r=dict(verified=True,manifest_sha256=sha((L/'finalmanifest.json').read_bytes()),scientific_freeze_sha256=sha((L/'scientific-freeze.json').read_bytes()),manifest_entries=len(j['entries']),scientific_entries=len(json.loads((L/'scientific-freeze.json').read_bytes())['entries']),mutable_NEXT_excluded=True)
 write('manifest-verification.json',r);print(json.dumps(r))
