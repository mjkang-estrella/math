from pathlib import Path
import json, hashlib, subprocess
lane=Path(__file__).resolve().parent.parent

def write(rel,text):
    subprocess.run(['python3','-I','-B',str(lane/'write_lane.py'),rel],input=text,text=True,check=True)

d=json.loads((lane/'results/CHECKPOINT-termination.json').read_text())
d['status']='PARTIAL_NOT_LITERAL_ENDPOINT'
d['mathdb_id']=324571
d['credit']=0
d['campaign_new']=55
d['campaign_target']=60
d['prior_credited']=39
d['formal_endpoint_present']=False
d['partial_replay']='results/PARTIAL-REPLAY.json'
d['axiom_audit']='62 named declarations printed; allowed axiom union only. Whole-environment/private/generated body-origin DAG not executed.'
d['controls']='Constant sample and symbolic odd-arrival positive controls strict+checker green. NegativeSameSide expected exit1; also has a secondary failed no-earlier-match subproof, so not a clean isolated negative control.'
d['deviations'] += ['Replay runner and negative-control runner invocations overlapped briefly. No shell background operator used, but no global aggregate-RSS cap is claimed across those groups.', 'Runner output display used a runpy main wrapper, retaining caps/true-exit receipts and printing saved log after SystemExit. It is not the exact CLI spelling in TASK.', 'No final paper/PDF or full literal endpoint was completed.']
rs=[]
for f in sorted((lane/'receipt').glob('*.json')):
    r=json.loads(f.read_text())
    assert r['group_members_left']==[]
    rs.append({'path':str(f.relative_to(lane)),'label':r['label'],'exit':r['exit'],
               'sha256':hashlib.sha256(f.read_bytes()).hexdigest()})
d['completed_receipts_before_finalize']=rs
d['sources_and_oleans']={str(f.relative_to(lane)):hashlib.sha256(f.read_bytes()).hexdigest()
 for folder in ['src','build','replay/src','replay/build'] for f in sorted((lane/folder).glob('*')) if f.is_file()}
write('results/CHECKPOINT.json',json.dumps(d,indent=2)+'\n')
write('results/324571.json',json.dumps({'mathdb_id':324571,'status':'PARTIAL_NOT_LITERAL_ENDPOINT',
 'credit':0,'campaign_new':55,'campaign_target':60,'prior_credited':39,
 'acceptance':'Independent final review and root acceptance absent',
 'checkpoint':'results/CHECKPOINT.json'},indent=2)+'\n')
lines=['# Partial implementation — MathDB 324571','',
 'No universal discrepancy bound or strict-supremum theorem is present. Credit remains zero; campaign remains 55/60 beyond 39 prior.', '',
 'Ten modules (including controls and named axiom audit) passed strict Lean 4.34.1 and leanchecker. A fresh source-only extraction of those same ten modules, starting with an empty build and using upstream-only dependencies, passed all twenty compiler/checker runs. Source equality and post-checker olean hashes are in results/PARTIAL-REPLAY.json.', '',
 'Proved: the chronological prefix/least-match semantics and first-arrival color uniqueness; infinite iid product probability measure on Nat colors; arbitrary finite measurable cylinders; coordinate law; measurable winner and genuine winning PMF; normalized conditional pair law; positive finite square collision mass; disjoint-position/only-common-color block winner inclusion; aligned-pair geometric failure probability and stopping-tail bound; almost-sure termination and a.e. null-fallback invariance.', '',
 'The 62 named-declaration axiom reports use only propext, Classical.choice, and Quot.sound. This does not replace the required whole-environment/private/generated/transitive body-origin audit. The positive controls compile. The intended negative same-side mutation fails with exit 1, with an additional failed subproof retained in its log.', '',
 '## Exact unpaid work','']
lines += ['- '+u for u in d['unpaid']]
lines += ['', '## Source map','',
 'Final Sections 2 and 9.1 conditional pair: ShoePair / ShoeConditional. Final Section 9.1 strict chronological stopping: ShoeBase / ShoeStopping / ShoeBlock. Infinite iid construction and finite cylinders: ShoeProbability. New geometric termination bridge: ShoeDiagonal / ShoeTermination. Final Section 4 total variation and Section 9.2 Conjecture 4 equation (19): NOT IMPLEMENTED. No final-source universal endpoint is claimed.', '',
 '## Retained limits','',
 'Supplied ordinary/literal/source qualification is documentary input, not a Lean theorem. Bounded prior nonmatches remain bounded. Galbraith–Holmes2012 body404/unread remains an explicit access limit. No worldwide novelty, acceptance, or credit is claimed. No network, children, git, peer reads, ledger writes, installation, or mathematical Python experiment was used.', '',
 'Process deviations and failed receipts are listed in results/CHECKPOINT.json. In particular, the initial runner-help call and uncapped runner-source inspection are disclosed, and the replay/negative invocations overlapped briefly. The resource reports are sampled per-group, not global cgroup claims. The present partial summary is not the requested finished paper.', '']
write('SUMMARY.md','\n'.join(lines))
