from pathlib import Path
import json,hashlib,datetime,subprocess,os,sys
L=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
copies=[]
for src,dst in [
 (L.parent/'sol-fresh-source-discovery-r123/sources/krasniqi-public-proof.md',L/'sources/cached-krasniqi-public-proof.md'),
 (L.parent/'sol-fresh-source-discovery-r123/discovery.md',L/'reopened-r123-discovery.md'),
 (L.parents[1]/'AGENTS.md',L/'context-batch-AGENTS.md'),
 (L.parents[5]/'AGENTS.md',L/'context-ancestor-AGENTS.md')]:
 b=src.read_bytes();dst.write_bytes(b);copies.append(dict(source=str(src),copy=dst.name,sha256=sha(b)))
save('cached-copy-provenance.json',copies)
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
save('guard-binding.json',dict(path=str(guard),sha256=sha(guard.read_bytes()),AS=512*1024*1024,group_RSS=512*1024*1024,CPU=210,wall=230,nominal_sample_ms=40))
p=subprocess.run(['sh',str(L/'run-checks.sh')],capture_output=True,text=True)
(L/'checks.json').write_text(p.stdout);(L/'checks.guard.json').write_text(p.stderr)
assert p.returncode==0
save('failures.json',dict(utc=now,checks_failed=False,retrieval_failures=[r for r in map(json.loads,(L/'http.jsonl').read_text().splitlines()) if 'error' in r or 'challenge' in r.get('final_url','')],process_deviations=['Krasniqi duplicate fetched before early-screen output was inspected','Forum requested after PDF403 inside same sequential batch; challenge not used as source'],install_or_cap_change=False))
save('search-record.json',dict(utc=now,tool='native web search; leads only, exact primary bytes fetched separately under guard',queries=['conjecture 2026 inequality probability arxiv','conjecture 2025 convexity open problem integral','conjecture 2025 logarithmic mean','conjecture 2026 complete monotonicity','Sharp bounds for the product and sum conjecture Xu proof','we conjecture 2026 log-concave','g95C4zIEPg','One-Bit Distributed Mean Estimation with Unknown Variance arxiv','Kipnis Duchi 2022 one bit mean estimation arxiv','2501.18502 conjecture proof','Interaction Is Not Necessary for Order-Optimal 1-Bit Mean Estimation arxiv','Kumar Vatedka periodic quantizer','s40840-025-02023-z Conjecture proof'],limits='Queries are a compact activity summary, not a verbatim complete results archive; no global novelty/current-head clearance. No web search snippets used as proof.'))
save('provenance.json',dict(utc=now,lane=str(L),credit=0,baseline=dict(additional=9,total=39,next=40),targets=[dict(id='10.1007/s40840-025-02023-z',statement='Conjecture1 all a,b>0 unequal and all lambda in(0,1]',decision='routine full source adaptation, excluded'),dict(id='2501.18502v4',statement='Section6 concluding unnumbered universal strict asymptotic minimax gap',decision='unresolved; periodic Fisher helper is not a source refutation')],primary_versions={'onebit':'v4 2026-06-23','kipnis':'v4 2022-05-09','hu':'v1 2026-08-03','means':'published article49(2026)27'},history={'records':1750,'changed_new':8,'missing':0,'retained':'r111-r113 originals','coverage':'bounded inherited qualified ORIGINAL union'},access_limits=['OpenReview journal body403; forum challenge200','No exact journal/arxiv byte equivalence certified','Cai author PDF failed empty exception','Miao2607.24358 body unread','Current registry bodies and capped history gaps remain PARKED; cached lexical catalogue only'],external_actions=False,children=False,lean=False,manuscript=False,shared_edits=False,context='archival only',guard=str(guard)))
save('primary-hashes.json',{str(p.relative_to(L)):sha(p.read_bytes()) for p in sorted((L/'sources').iterdir()) if p.is_file()})
def rows(paths):return {str(p.relative_to(L)):dict(sha256=sha(p.read_bytes()),bytes=p.stat().st_size) for p in paths}
excluded={'scientific-freeze.json','finalmanifest.json','manifest-verification.json'}
files=[p for p in sorted(L.rglob('*')) if p.is_file() and p.name not in excluded]
science=[p for p in files if not p.name.startswith('context-')]
save('scientific-freeze.json',dict(utc=now,limits='Immutable scientific snapshot; administrative context archival only; no source resolution claimed.',records=rows(science)))
files=[p for p in sorted(L.rglob('*')) if p.is_file() and p.name not in {'finalmanifest.json','manifest-verification.json'}]
save('finalmanifest.json',dict(utc=now,excludes=['finalmanifest.json','manifest-verification.json'],records=rows(files)))
print(json.dumps(dict(files=len(files),scientific=len(science),checks='PASS')))
