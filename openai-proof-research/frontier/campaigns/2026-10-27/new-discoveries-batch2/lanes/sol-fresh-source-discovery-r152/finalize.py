import json,hashlib,datetime,sys
from pathlib import Path
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
def rec(p):return dict(path=str(p.relative_to(L)),bytes=p.stat().st_size,sha256=sha(p))
excluded={'context-NEXT.md','finalmanifest.json','manifest-verification.json','finalize-run.log','verify-run.log'}
if sys.argv[1]=='finalize':
 h=json.loads((L/'history-kazemi.json').read_bytes())
 science111=[r for r in h['records'] if any('/sol-fresh-source-discovery-r'+n+'/' in r[0] for n in ['111','112','113'])]
 assert len(science111)>=7
 guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
 assert sha(guard)=='825ee0d48177cd12354cdbf36fd36b61f0503ff3241356a7bf638ee0bc49fa45'
 http=[json.loads(s) for s in (L/'http.jsonl').read_text().splitlines()]
 provenance=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),local_date='2026-10-29',retrieval_utc_date='2026-10-30',status='ZERO qualifying discoveries; complete ordinary routine-source proof, not nominated',target='Kazemi2026 Conjecture6.1 all n>=2 chi_td(Q_(2^n+1))=2^(2^n-n+1)+2',source_online_date='2026-01-07',dependency_publication_date='2017-02-03',retrievals=http,source_files=[rec(p) for p in sorted((L/'sources').iterdir()) if p.is_file()],history=dict(records=len(h['records']),distinct_bodies=len({r[1] for r in h['records']}),changed=h['changed'],missing=h['missing'],hits=h['hits'],baseline_indexes=h['baselines'],original_r111_r113=science111,limits=h['limits']),omega='490f6bccbf445ab8e111a16b0b8670a5dd7c9a9c',openai='7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a',registry_limits=['aa026->a19a capped300','a19a->490f capped300','Fresh fixed Library paths only; not full registry body semantics','Retained baseline path hits not all theorem bodies read','No current beyond-fixed-head claim or priority clearance'],literature_limits=['Original1993 and van Wee theorem bodies unread; actual2017 theorem/corollary used','2014 product and2015 coloring primary bodies unread','No exhaustive companion, citing or specialist-index coverage'],procedural_limits=['Companion author aliases were not separately screened before companion download; target author/title/DOI and claim alias screen preceded target download','Search tool navigation results retained by URLs and explicit prose, not raw search-result bytes'],guard=dict(path=str(guard),sha256=sha(guard),AS_bytes=536870912,group_RSS_bytes=536870912,CPU_seconds=210,wall_seconds=230,nominal_sampling_ms=40,qualification='Sampling misses possible transients; actual scheduling interval not instrumented; caps unchanged'),check_log=rec(L/'checks-run.log'),public_prior_proof_claim=False,scientific_result='Complete ordinary full source proof; routine counting adaptation excluded',mutable_NEXT_excluded=True,no_Lean_or_manuscript=True)
 save('provenance.json',provenance)
 scientific=[p for p in sorted(L.rglob('*')) if p.is_file() and str(p.relative_to(L)) not in excluded and p.name!='scientific-freeze.json' and not p.name.endswith('.log')]
 save('scientific-freeze.json',dict(utc=provenance['utc'],entries=[rec(p) for p in scientific],exclusions=['context-NEXT.md','operational logs','manifest and verification receipts','scientific-freeze self']))
 payload=[p for p in sorted(L.rglob('*')) if p.is_file() and str(p.relative_to(L)) not in excluded]
 save('finalmanifest.json',dict(utc=provenance['utc'],entries=[rec(p) for p in payload],exclusions=sorted(excluded)))
 print('Created scientific freeze and manifest')
elif sys.argv[1]=='verify':
 receipts={}
 for name in ['scientific-freeze.json','finalmanifest.json']:
  j=json.loads((L/name).read_bytes());bad=[]
  for r in j['entries']:
   p=L/r['path']
   if not p.is_file() or sha(p)!=r['sha256'] or p.stat().st_size!=r['bytes']:bad.append(r['path'])
  assert not bad,(name,bad)
  receipts[name]=dict(sha256=sha(L/name),verified_entries=len(j['entries']))
 j=json.loads((L/'finalmanifest.json').read_bytes())
 actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and str(p.relative_to(L)) not in excluded}
 assert actual=={r['path'] for r in j['entries']}
 assert 'context-NEXT.md' not in actual
 for n in ['SUMMARY.md','discovery.md','progress.md','provenance.json','PROOF.md','checks.py','run-checks.sh']:assert (L/n).is_file()
 assert not list(L.rglob('*.lean'))
 save('manifest-verification.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',receipts=receipts,membership='exact',mutable_NEXT='excluded'))
 print(json.dumps(receipts))
