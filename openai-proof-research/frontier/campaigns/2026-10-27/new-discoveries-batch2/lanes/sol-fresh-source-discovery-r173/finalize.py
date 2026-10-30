import json,hashlib,datetime
from pathlib import Path
L=Path(__file__).resolve().parent;B=L.parents[1];R=L.parents[5]
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
history=json.loads((L/'history-receipt.json').read_text())
retained={str(k):[r for r in history['records'] if f'sol-fresh-source-discovery-r{k}/' in r[0]] for k in [111,112,113]}
assert all(retained.values())
save('retained-originals.json',retained)
# Read complete structured ledgers; preserve bounded semantic inventory.
ctx=[]
for n in ['ledger.json','prior-campaign-context.json']:
 b=(L/('context-'+n)).read_bytes();j=json.loads(b)
 ctx.append(dict(name=n,sha256=sha(b),keys=list(j),sections={k:len(v) for k,v in j.items() if isinstance(v,(list,dict))},limits='Entire JSON parsed. Actual source arguments, not metadata alone, govern eligibility.'))
save('context-audit.json',ctx)
save('search-record.json',dict(recorded_utc=now(),tool='web.run public search, no browser',queries=['"Two inequalities for the medians of a triangle" conjecture','"Liu" "medians" "Conjecture 3" "2024"','"Two inequalities for the medians" "doi"','"Liu" "medians" "conjectures" "2025" "2026"','site:mathdb.com "Liu" "medians" conjecture','site:arxiv.org "medians" "Liu" inequality conjecture','site:clopen.solutions "medians"'],findings='Source publisher PDF/issue and companion 2012,2016,2018,2020,2025 bodies identified; no matching public proof body identified in returned results.',limits='Search-output evidence, not preserved HTTP response bytes; dates here are recording UTC. Current full GitHub registries not obtained. No absence/novelty clearance. Exact HTTP primary retrieval times and hashes separately in http.jsonl.'))
http=[json.loads(s) for s in (L/'http.jsonl').read_text().splitlines()]
save('failures.json',dict(http_errors=[r for r in http if 'error' in r],process_failures=[],deviations=['First native bounded inventory output was truncated when large NEXT/ledger/context were concatenated; subsequent copies preserved full bytes and JSON was parsed under guard.','Numerical differential-evolution diagnostics reached their iteration cap for Conjectures 1 and 4; these are finite diagnostics only.','No machine-readable source revision history or DOI/arXiv identifier found for selected publisher paper; no claim of global nonexistence.'],access_notes=['JIA2016 status200 final URL carries cookies_not_supported suffix; actual full article body present. No bypass.']))
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
primary=[]
for f in sorted((L/'sources').iterdir()):
 b=f.read_bytes();primary.append(dict(path=str(f.relative_to(L)),bytes=len(b),sha256=sha(b)))
save('primary-hashes.json',primary)
save('provenance.json',dict(utc=now(),lane=str(L),credit=0,baseline=dict(additional=9,total=39,next=40),guard=dict(path=str(guard),sha256=sha(guard.read_bytes()),AS_bytes=536870912,group_RSS_bytes=536870912,CPU_seconds=210,wall_seconds=230,nominal_sample_ms=40,environment=dict(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',PYTHONDONTWRITEBYTECODE='1'),unchanged=True),primary_http=http,history=dict(records=len(history['records']),changed=len(history['changed']),missing=history['missing'],bases=history['bases']),source_versions={'medians':'Published 2024 volume8 issue1 pages35-47, currently served bytes; no publisher revision chronology supplied','weighted':'Published JMI2020 DOI10.7153/jmi-2020-14-11; source bibliography prints2021','refinements':'Published JMI2018 DOI10.7153/jmi-2018-12-05','earlier':'JIA2016 article9 DOI10.1186/s13660-015-0947-2'},coverage_limits=['No current/historical full registry body clearance; parked reconstruction unchanged.','No independently reviewed ordinary full proof, no Lean or manuscript.','Search results do not prove absence; exact body comparisons bounded.'],writes='Assigned lane only; no live NEXT frozen',integrity_verification='Separate verify.py verifies manifest bytes/hashes and freeze coverage; solo mathematical independence not claimed'))
exclude={'scientific-freeze.json','finalmanifest.json','manifest-verification.json'}
def rows(files):
 out=[]
 for f in sorted(files):
  b=f.read_bytes();out.append(dict(path=str(f.relative_to(L)),bytes=len(b),sha256=sha(b)))
 return out
files=[p for p in L.rglob('*') if p.is_file() and p.name not in exclude]
save('scientific-freeze.json',dict(utc=now(),records=rows(files),limits='Frozen assigned-lane payload, including earlier context copy only. No live NEXT or external file frozen. No self hash.'))
save('finalmanifest.json',dict(utc=now(),records=rows(files+[L/'scientific-freeze.json']),excluded=['finalmanifest.json','manifest-verification.json'],no_self_hash=True))
print('frozen',len(files),'manifest',len(files)+1)
