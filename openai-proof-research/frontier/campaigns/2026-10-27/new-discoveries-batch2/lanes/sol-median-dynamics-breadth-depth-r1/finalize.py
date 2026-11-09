from pathlib import Path
import hashlib,json,re,datetime
L=Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
bindings=json.loads((L/'freeze.json').read_text())
for r in bindings:
 assert h(L/r['copy'])==r['sha256']
 if not r['administrative']:assert h(Path(r['original']))==r['sha256']
http=[json.loads(x) for x in (L/'http.jsonl').read_text().splitlines()]
for r in http:
 if r.get('status')==200 and '/pdf/' in r['url']:
  p=L/'frozen'/(r['url'].split('/pdf/')[1]+'.pdf');assert h(p)==r['sha256']
maps={}
for p in sorted((L/'frozen').glob('*.txt')):
 pages=p.read_text().split('\f');hits=[]
 for page,body in enumerate(pages,1):
  for line in body.splitlines():
   if re.search(r'^(Theorem [135]|Conjecture [134]|Proposition 3.6|Lemma 5.1|.*[Ww]e conjecture)',line):hits.append(dict(pdf_page=page,text=line[:250]))
 maps[p.name]=dict(sha256=h(p),statements=hits)
(L/'source-map.json').write_text(json.dumps(maps,indent=2))
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1'/'packet'/'helper_guard.py'
prov=dict(date=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='proposed exact source-conjecture counterexample; unaccepted',counts_unchanged=[9,39,40],helper_guard=dict(path=str(guard),sha256=h(guard),AS_and_group_RSS_MiB=512,CPU_seconds=210,wall_seconds=230),freeze_bindings=bindings,http=http,scientific_hashes={str(p.relative_to(L)):h(p) for p in sorted((L/'frozen').glob('*')) if p.is_file()},administrative_policy='snapshot only; originals not compared after snapshot',current_registry_limit='Forbidden routes not retried; no whole current GitHub head/citing clearance',chronology='Target1911.08613v2 initially2019-11-19 updated2023-01-02 per current Atom record; present certificate2026-10-30; current2026 breadth source versions as identified in query XML/PDF headers',before_after_originals_pass=True)
(L/'provenance.json').write_text(json.dumps(prov,indent=2))
manifest={str(p.relative_to(L)):h(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
(L/'manifest.json').write_text(json.dumps(manifest,indent=2));print('manifest files',len(manifest))
print('Curve conjecture pages:',[x for x in maps['2610.19585v1.txt']['statements'] if 'Conjecture 4' in x['text']])
