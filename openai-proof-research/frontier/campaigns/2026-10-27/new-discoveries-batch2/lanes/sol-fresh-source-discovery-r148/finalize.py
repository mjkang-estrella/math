from pathlib import Path
import json,hashlib,datetime,sys
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
def entry(p):return dict(path=str(p.relative_to(L)),bytes=p.stat().st_size,sha256=sha(p))
if len(sys.argv)>1 and sys.argv[1]=='verify':
 for n in ['finalmanifest.json','scientific-freeze.json']:
  j=json.loads((L/n).read_bytes())
  for e in j['entries']:
   p=L/e['path'];assert p.stat().st_size==e['bytes'] and sha(p)==e['sha256'],str(p)
 print('PASS final manifest and scientific freeze');sys.exit(0)
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
assert sha(guard)=='825ee0d48177cd12354cdbf36fd36b61f0503ff3241356a7bf638ee0bc49fa45'
http=[json.loads(x) for x in (L/'http.jsonl').read_text().splitlines()]
for r in http:
 if 'sha256' in r:assert sha(L/'sources'/r['name'])==r['sha256']
for p in L.glob('history-*.json'):
 for h in json.loads(p.read_bytes())['hits']:assert sha(L/h['copy'])==h['sha256']
assert sha(L/'sources/public-proof.lean')==sha(L/'sources/public-original.lean')
assert sha(L/'sources/public-check.py')=='b862fce6a3a376f76896aa06bde0e1e1c7dca8908788b3c901f7422f243662ee'
chron=json.loads((L/'sources/proof-history.json').read_bytes())[0]
save('provenance.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),result='zero; selected Matuzas conjecture unresolved; Li public exclusion',http=http,guard=dict(path=str(guard),sha256=sha(guard),AS_bytes=512*1024*1024,sampled_group_RSS_bytes=512*1024*1024,CPU_seconds=210,wall_seconds=230,sampling_ms=40,caps_raised=False,sampling_qualification='Unsampled transients not excluded'),registry=dict(omega='490f6bccbf445ab8e111a16b0b8670a5dd7c9a9c',openai='7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a',both_intervals_capped300=True,semantic_clearance=False),public_proof_chronology=dict(sha=chron['sha'],author=chron['commit']['author'],committer=chron['commit']['committer'],original_current_bytes_identical=True),history=[entry(p) for p in sorted(L.glob('history-*.json'))],context=[entry(L/('context-'+n)) for n in ['ledger.json','prior-campaign-context.json','NEXT.md']],limitations=['401 optional code search stopped','PDF text font warnings retained','Retained roles plus immediate new roles not every newly nested report','Public proof read, not compiled','No general period comparison proved','Published Chuang typeset body not fetched; v2 body used'],actions=dict(children=False,git=False,shared_edits=False,count_edits=False,browser_tabs=False,public_actions=False,authored_lean=False,paper=False)))
excluded={'finalmanifest.json','manifest-verification.json','scientific-freeze.json'}
files=[p for p in sorted(L.rglob('*')) if p.is_file() and p.name not in excluded]
science=[p for p in files if not p.name.startswith('context-') and p.name!='context-reading.json']
save('scientific-freeze.json',dict(entries=[entry(p) for p in science],excludes='Mutable context snapshots and context-reading; especially NEXT; integrity containers'))
files.append(L/'scientific-freeze.json')
save('finalmanifest.json',dict(entries=[entry(p) for p in files],excludes=['finalmanifest.json','manifest-verification.json']))
for n in ['finalmanifest.json','scientific-freeze.json']:
 for e in json.loads((L/n).read_bytes())['entries']:assert sha(L/e['path'])==e['sha256']
save('manifest-verification.json',dict(status='PASS',finalmanifest_sha256=sha(L/'finalmanifest.json'),scientific_freeze_sha256=sha(L/'scientific-freeze.json'),source_hashes_verified=True,history_copy_hashes_verified=True,public_original_equals_current=True,guard_unchanged=True))
print('PASS final manifest and scientific freeze')
