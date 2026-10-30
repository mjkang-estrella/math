import json,hashlib,datetime,re
from pathlib import Path
L=Path(__file__).resolve().parent;R=L.parents[5]
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
(L/'inputs').mkdir(exist_ok=True)
inputs=[R/'AGENTS.md',L.parents[1]/'AGENTS.md',R/'sources/upstream.json',L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']
for k in [169,170,171]:inputs.append(L.parent/('sol-fresh-source-discovery-r'+str(k))/'SUMMARY.md')
inputs.append(L.parent/'root-prefix-reversal-routine-exclusion-r1/DECISION.md')
copied=[]
for i,p in enumerate(inputs):
 if not p.is_file():copied.append(dict(path=str(p),missing=True));continue
 b=p.read_bytes();dest=L/'inputs'/(str(i)+'-'+p.parent.name+'-'+p.name);dest.write_bytes(b);copied.append(dict(path=str(p),copy=str(dest.relative_to(L)),sha256=sha(b)))
save('input-provenance.json',dict(utc=now(),records=copied))
pat=re.compile(r'2610[.]37522|Minimum Subpacketization|Weijun Fang|Jing Qiu|Shu.Tao Xia|Fang.Wei Fu|10[.]63561/jmsc[.]v3i1[.]1226|Amao|Reginald.Ihedike|Monomial Ideals in Few Variables|1801[.]07672|tiny squares',re.I)
rows=[]
for p in [R/'sources/CONTENTS.md',R/'sources/preprints-tree.json',R/'frontier/campaigns/2026-10-26/new-discoveries/ledger.json']:
 if not p.is_file():rows.append(dict(path=str(p),missing=True));continue
 b=p.read_bytes();s=b.decode(errors='replace');m=list(pat.finditer(s));rows.append(dict(path=str(p),sha256=sha(b),bytes=len(b),hits=[s[max(0,x.start()-100):x.end()+200] for x in m]))
save('older-catalogue-screen.json',dict(utc=now(),pattern=pat.pattern,records=rows))
http=[json.loads(x) for x in (L/'http.jsonl').read_text().splitlines()]
save('provenance.json',dict(utc=now(),status='ZERO; full RS conjecture unresolved; monomial claim literally publicly refuted',model='gpt-6.1-sol',reasoning_effort='high',service='standard/default; no tier change requested',counts=dict(additional=9,total=39,next=40,credit=0),primary_retrievals=http,history='history-receipt.json; exact-screen.json; older-catalogue-screen.json; inherited-history-qualification.json',registry='registry-path-screen.json; raw first attempt retained separately; saved snapshots only',scope_limits=['No current whole-registry clearance','Capped historical transitions and missing merge trees parked','No matching saved path is not body clearance or global novelty','No worldwide priority claim','Qiu2026 local subspace result read as quoted only','No full source result or eligible nominee'],search_queries=['site.arxiv.org conjecture 2026 log-concavity combinatorial polynomials October','site.arxiv.org conjecture 2025 irreducibility polynomials recurrence','site.arxiv.org/html 2026 conjecture divisibility we conjecture','site.arxiv.org/html 2026 conjecture unimodal open problems','monomial ideals tiny squares two variables','2610.37522 subpacketization conjecture proof','Tamo Ye Barg optimal repair Reed Solomon subpacketization Theorem 5 2018 arxiv','Amao Reginald-Ihedike monomial correction'],access_policy='No GitHub/API/raw/codeload/patch/diff, ScienceDirect, Google challenge retry, browser, proxy or TLS changes',guard=dict(path=str(inputs[3]),sha256=sha(inputs[3].read_bytes()),AS=536870912,sampled_group_RSS=536870912,cpu_seconds=210,wall_seconds=230,nominal_sample_ms=40,unsampled_transients_not_ruled_out=True),failed_checks='progress.md and http.jsonl; no hidden retries or numerical-as-proof claims',writes='assigned lane only',freeze='Only local immutable snapshots, never shared live NEXT invariants'))
save('failures.json',dict(retrieval_failures=[r for r in http if 'error' in r],failed_mathematical_routes=['Unqualified two-overlap lcm identity false','GF9 example violates 24 necessary repair pairs, so cannot refute source','Single global normalization has rational anchor labels','Per-helper normalization does not yield one global tuple','Prime-level simultaneous subline selection unproved'],process_deviations=['Initial oversized native context reads truncated','Initial reconnaissance chained pwd/rg with semicolon','First registry raw-line regex matched hash substrings; corrected path parser retained separately','Mistaken TYB v3 HTML URL404; actual accessed abstract has v1 only']))
exclude={'scientific-freeze.json','finalmanifest.json','manifest-verification.json'}
records=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in exclude:
  b=p.read_bytes();records.append(dict(path=str(p.relative_to(L)),bytes=len(b),sha256=sha(b)))
save('scientific-freeze.json',dict(utc=now(),policy='Immutable lane-local scientific sources, notes and runnable checks; no live shared-file invariant',records=records))
records=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in {'finalmanifest.json','manifest-verification.json'}:
  b=p.read_bytes();records.append(dict(path=str(p.relative_to(L)),bytes=len(b),sha256=sha(b)))
save('finalmanifest.json',dict(utc=now(),exclude=['finalmanifest.json','manifest-verification.json'],records=records))
print('frozen',len(json.loads((L/'scientific-freeze.json').read_text())['records']),'payload',len(records))
