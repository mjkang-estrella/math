"""Bounded hash/receipt and exhaustive axiom-output verification (no mathematical oracle)."""
import hashlib,json,pathlib,re,resource,time
import signal
signal.alarm(50)
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(45,45))
base=pathlib.Path(__file__).resolve().parent
root=base.parent
start=time.monotonic()
def digest(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''): h.update(b)
    return h.hexdigest()
inputs=[
'root-log-arctangent-candidate-r1/PROOF.md',
'root-log-arctangent-source-r3/AUXILIARY.md',
'root-log-arctangent-source-r3/SOURCE-REVIEW.md',
'root-log-arctangent-formal-r1/ADOPTION.md',
'root-log-arctangent-formal-r1/SOURCE-COMPONENT.md',
'root-log-arctangent-formal-r1/source-component-receipt.json',
'root-log-arctangent-formal-r1/formal/MeanSourceDefs.lean',
'root-log-arctangent-formal-r1/formal/run_lean.py',
'sol-log-arctangent-investment-review-r3/review.md']
assert (base/'formal/MeanSourceDefs.lean').read_bytes()==(root/inputs[6]).read_bytes()
assert digest(base/'formal/MeanSourceDefs.lean')=='6a64dfdbc059d35dbdf8985660fc0bd61ef60d7e4f1246829cc68c139ad64db3'
assert (base/'formal/run_lean.py').read_bytes()==(root/inputs[7]).read_bytes()
names=json.loads((base/'declarations.json').read_text())
receipts=[]
for p in sorted((base/'logs').glob('fresh-source-replay-*.json')):
    r=json.loads(p.read_text()); assert r['exit']==0 and r['termination_reason'] is None
    assert r['sampled_group_peak_rss']<3*1024**3
    assert r['source_sha256']==digest(base/'fresh-source-replay'/r['args'][-1])
    receipts.append({'path':str(p.relative_to(base)),**r})
assert len(receipts)==4
logs=list((base/'logs').glob('fresh-source-replay-Checks*.log'))
assert len(logs)==1
audit=logs[0].read_text()
reports=re.findall(r"'LogArctangentSource\.(\w+)' depends on axioms: \[([^\]]*)\]",audit)
assert [n for n,_ in reports]==names
allowed={'propext','Classical.choice','Quot.sound'}
for n,ax in reports: assert set(ax.split(', '))<=allowed
for module in ['MeanSourceDefs','Stolarsky','Transfer']:
    s=(base/'formal'/f'{module}.lean').read_text()
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',s)
    assert 'set_option autoImplicit false' in s and 'set_option warningAsError true' in s
    assert (base/'formal'/f'{module}.lean').read_bytes()==(base/'fresh-source-replay'/f'{module}.lean').read_bytes()
mathlib=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib')
rev=(mathlib/'.git/HEAD').read_text().strip()
assert rev=='d13f23b723b8a846827a245b89c10fc7d3f11612'
lean=pathlib.Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
lsha=digest(lean)
assert lsha=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
files=[p for p in base.rglob('*') if p.is_file() and p.suffix in {'.lean','.py','.md','.log','.json'} and p.name!='provenance.json']
result={'status':'PASS conditional integration component only','endpoint':'LogArctangentSource.sourceClaim_of_strictMono_gap','sole_substantive_premise':'StrictMonoOn LogArctangentSource.centeredLogGap (Set.Ioi 0)','strongest_remaining_gap':'Proof of the displayed strict monotonicity; no unconditional SourceClaim claimed','credit':0,'accepted_total':33,'additional_accepted':3,'source_commit_label':'709a70438e (supplied provenance label; no git authentication operation)','lean_binary':str(lean),'lean_sha256':lsha,'mathlib':str(mathlib),'mathlib_head_read_directly':rev,'frozen_input_hashes':{n:digest(root/n) for n in inputs},'files':{str(p.relative_to(base)):digest(p) for p in files},'declarations':names,'axiom_reports':dict(reports),'allowed_axioms':sorted(allowed),'strict_replay_receipts':receipts,'limits':{'Lean_sampled_group_RSS_ceiling_bytes':3*1024**3,'Lean_wall_seconds':180,'diagnostic_AS_hard_bytes':512*1024**2,'diagnostic_CPU_hard_seconds':45,'BLAS_OMP_MKL_NumExpr_threads':1},'diagnostic_elapsed':time.monotonic()-start,'external_actions':False}
(base/'provenance.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'declarations':len(names),'fresh_replay_commands':len(receipts),'max_sampled_RSS':max(r['sampled_group_peak_rss'] for r in receipts),'elapsed':time.monotonic()-start}))
