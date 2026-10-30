from pathlib import Path
import hashlib,json,datetime

out=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
guard=out.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
assert sha(guard)=='825ee0d48177cd12354cdbf36fd36b61f0503ff3241356a7bf638ee0bc49fa45'
freeze=json.loads((out/'review-freeze.json').read_text())
assert len(freeze['files'])==50
rows=[]
for r in freeze['files']:
    orig=Path(r['path']);copy=out/'frozen'/orig.relative_to(freeze['root'])
    for p in (orig,copy):
        assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],str(p)
    rows.append({'original':str(orig),'copy':str(copy.relative_to(out)),
                 'bytes':r['bytes'],'sha256':r['sha256'],'both_match':True})
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
(out/'integrity-final.json').write_text(json.dumps({'utc':now,'status':'PASS',
    'originals_verified':50,'copies_verified':50,'files':rows},indent=2)+'\n')
proof=out/'frozen/PROOF.md'
provenance={'utc':now,'role':'independent review sub-agent, solo',
    'candidate':freeze['root'],'candidate_proof_sha256':sha(proof),
    'freeze_sha256':sha(out/'review-freeze.json'),
    'recommendation':{'ordinary_proof':'PASS','classical_complete_bridge':'PASS',
       'discovery_credit':'recommend routine exclusion; root decides','Lean':'not attempted',
       'paper':'not attempted','further_credit_investment':'not warranted'},
    'source_scope':{'sirola':'2402.14163v2 introduction Conjecture; Definition1.2; N0; both kinds; all n>1; arbitrary domains',
       'earlier_subsumer':'El Fadil, Tatra83(2023)51-60, Theorem3.1 p55, proof p56; phi=X',
       'garg':'2511.21427v2 Theorem1 inspected; not a premise; printed Lemma5 typo expressly excluded'},
    'read_evidence':['frozen/sources/dumas.txt','frozen/sources/elfadil.txt',
       'frozen/sources/elfadil.pdf','elfadil-pages55-56.txt','frozen/sources/garg.txt'],
    'fresh_retrieval':'live-source-evidence.json; two HTTP200 matching frozen bytes; no retries',
    'independent_checker':{'script':'independent_check.py','sha256':sha(out/'independent_check.py'),
       'evidence':'independent-evidence.json','candidate_or_root_code_run':False,
       'mathematical_status':'diagnostics only; universal argument in review.md'},
    'integrity':{'initial':'integrity-initial.json','final':'integrity-final.json','all50_originals_and_copies':'PASS'},
    'context':'Ancestor/batch AGENTS.md and current ledger/prior-context/NEXT read; complete JSONs parsed; context-reconciliation.json',
    'counts_unchanged':{'additional':9,'total':39,'next':40},
    'historical_limits':{'Omega':'b3ff232c65bd3740230b1219236122e11ecd2cea',
       'delta':'19 commits,7 paths from b62773edfb6a6f7806de09b593b2e3b6834685c7',
       'OpenAI':'4eaee87548250b2682affda7d05d947c05554bae',
       'remaining_gaps':'two older300-path caps; no absence or worldwide-priority claim; reviewer did not repeat broad registry audit'},
    'guard':{'path':str(guard),'sha256':sha(guard),'AS_MiB':512,'groupRSS_MiB':512,
       'CPU_seconds':210,'wall_seconds':230,'nominal_sample_ms':40,'caps_raised':False,
       'env':{'PYTHONDONTWRITEBYTECODE':'1','OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1'},
       'limitation':'unsampled peaks possible'},
    'failures':['One combined source-reading output was truncated; complete relevant proof ranges reread in bounded chunks.'],
    'no_helper_or_http_failures':True,'writes_only_this_lane':True,
    'git':False,'children':False,'public_mutations':False,'browser_tabs':False,
    'acceptance_or_count_authority':False}
(out/'provenance.json').write_text(json.dumps(provenance,indent=2,ensure_ascii=False)+'\n')
files=[]
for p in sorted(out.rglob('*')):
    if p.is_file() and p.name!='finalhashes.json':
        files.append({'path':str(p.relative_to(out)),'bytes':p.stat().st_size,'sha256':sha(p)})
(out/'finalhashes.json').write_text(json.dumps({'utc':now,'scope':'all lane files except this self-referential manifest','files':files},indent=2)+'\n')
print(json.dumps({'status':'PASS','originals':50,'copies':50,'manifest_files':len(files),
    'review_sha256':sha(out/'review.md'),'finalhashes_sha256':sha(out/'finalhashes.json')}))
