#!/usr/bin/env python3
"""Offline READ-ONLY verifier. Never fetches, edits, prepares, repairs or reseals.
--preseal is permitted only before the single final seal exists.
Evidence integrity/finite checks are distinct from the written analytic verdict.
"""
import hashlib,json,os,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
SRC='frontier/sources/i92_anchored_rank_approximation_r2'
EXP='frontier/experiments/i92_anchored_rank_approximation_r2'
REPORT='frontier/reviews/i92-anchored-rank-approximation-r2.md'
SEAL=SRC+'/seal.json'
I90='frontier/sources/i90_anchored_rank_approximation'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
I90HASH='89f356914c26239322fdd3f1bb42dd9a124be0d6867ce65d02e3bf1276813438'
I88HASH='a4af4b269cef192734166e228ca2e95d6fd08ee25f03d4163a2fc4de0c9277c6'
DRIFT={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
def need(ok,msg):
    if not ok:raise AssertionError(msg)
def read(p):return (ROOT/p).read_bytes()
def load(p):return json.loads(read(p))
def sha(b):return hashlib.sha256(b).hexdigest()
def inv():
    result={REPORT}
    need(not (ROOT/REPORT).is_symlink(),'Report symlink')
    for d in (SRC,EXP):
        for p in (ROOT/d).rglob('*'):
            need(not p.is_symlink(),'Owned symlink '+str(p))
            if p.is_file():result.add(p.relative_to(ROOT).as_posix())
    result.discard(SEAL);return result

def runpy(p):
    result=subprocess.run([sys.executable,'-B',str(ROOT/p)],cwd=ROOT,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'),capture_output=True)
    need(result.returncode==0,p+' failed: '+result.stderr.decode(errors='replace')+'\n'+result.stdout.decode(errors='replace'))
    return result.stdout

def main():
    preseal=sys.argv[1:]==['--preseal'];need(not sys.argv[1:] or preseal,'Only --preseal supported')
    if preseal:
        need(not (ROOT/SEAL).exists(),'Cannot run --preseal after sealing')
    else:
        s=load(SEAL)
        need(s['pin']==PIN and s['owned_directories']==[SRC,EXP] and s['owned_report']==REPORT and s['self_exclusion']==SEAL,'Seal scope')
        rr=s['files'];need(len(rr)==len({r['path'] for r in rr}) and {r['path'] for r in rr}==inv(),'Exact owned domain')
        for r in rr:
            b=read(r['path']);need(len(b)==r['bytes'] and sha(b)==r['sha256'],'Owned bytes '+r['path'])
    refs=load(SRC+'/immutable-references.json')
    need(len(refs)==len({r['path'] for r in refs}),'Duplicate immutable references')
    for r in refs:
        need('i91' not in r['path'] and 'i93' not in r['path'],'Unrelated/concurrent lane dependency')
        b=read(r['path']);need(len(b)==r['bytes'] and sha(b)==r['sha256'],'Immutable reference '+r['path'])
    inputs=load(SRC+'/inputs.json');need({r['original'] for r in inputs if r['may_drift']}==DRIFT,'Drift allowlist')
    drift=[]
    for r in inputs:
        need(sha(read(r['snapshot']))==r['sha256'],'Snapshot '+r['snapshot'])
        if sha(read(r['original']))!=r['sha256']:
            need(r['may_drift'] and r['original'] in DRIFT,'Nonledger drift');drift.append(r['original'])
    need(sha(read(I90+'/seal.json'))==I90HASH,'Original I90 seal')
    need(sha(read('frontier/sources/i88_nonlinear_banach_discovery/seal.json'))==I88HASH,'Original I88 seal')
    need(read(SRC+'/original-i90-report.md')==read('frontier/iterations/i90-anchored-rank-approximation.md'),'Original I90 report copy')
    need(read(SRC+'/finalized-i90-parent-response.json')==read('frontier/experiments/i90-parent-verification.json'),'Finalized I90 parent copy')
    need(read(SRC+'/original-i90-brief.txt').decode()==load('frontier/iterations/iteration90-anchored-rank-approximation-task.json')['brief'],'Original I90 brief copy')
    brief=read(SRC+'/original-i92-brief.txt').decode()
    need('I92' in brief and I90HASH in brief and 'FULL I90 REPORT:' in brief and 'FINALIZED PARENT REPLAY / RESPONSE:' in brief,'Complete supplied I92 brief boundaries')
    for r in load(SRC+'/read-manifest.json'):
        b=read(r['path']);ls=b.decode().splitlines(keepends=True)
        need(sha(b)==r['sha256'] and 1<=r['start']<=r['end']<=len(ls),'Read source '+r['path'])
        need(sha(''.join(ls[r['start']-1:r['end']]).encode())==r['passage_sha256'],'Read passage '+r['path'])
    print('I92 owned/snapshot/reference checks; original reports, briefs and parent response PASS',flush=True)
    # The frozen, fully read I90 verifier checks all original Git bodies and maps,
    # I88 domain, I90 searches, six primary extractions, and its finite diagnostics.
    old=runpy('frontier/experiments/i90_anchored_rank_approximation/verify.py')
    need(b'"status": "EVIDENCE PASS"' in old,'Inherited evidence result')
    print('Frozen I90/I88 evidence replay PASS: 10373 original positions, 749 manuscripts, six primary PDF replays',flush=True)
    tree=load('sources/preprints-tree.json');domain=load('frontier/sources/i88_nonlinear_banach_discovery/search-domain.json')
    need(len(tree['tree'])==13223 and not tree['truncated'] and len(domain)==10373,'Complete domain counts')
    fam='Failure-of-Bounded-Approximation-in-a-Lipschitz-Free-Space-over-a-Uniformly-Discrete-Metric-Space-September-26-2026'
    sel=[r for r in domain if r['path'].split('/')[1]==fam]
    need(len(sel)==11 and sel==load(SRC+'/selected-inventory.json'),'Exact selected original inventory')
    got=sorted(p.relative_to(ROOT).as_posix() for p in (ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus').rglob('*') if p.is_file())
    need(len(got)==9340 and got==read(SRC+'/i14-rg-inventory.txt').decode().splitlines(),'I14 rg original inventory')
    need(set(got)=={r['original_local'] for r in domain if r['kind']=='corpus'},'I14 map inventory')
    for r in load(SRC+'/primary-evidence.json'):
        need(sha(read(r['pdf']))==r['pdf_sha256'] and sha(read(r['text']))==r['text_sha256'],'Primary interface bytes')
        response=load(r['response']);need(response['status']==200 and response['sha256']==r['pdf_sha256'],'Inherited primary response')
    pdf=next(r for r in sel if r['path'].endswith('/main.pdf'))
    extra=subprocess.run(['pdftotext','-layout',str(ROOT/pdf['original_local']),'-'],capture_output=True,check=True)
    need(extra.stdout==read(pdf['local']),'F primary PDF extraction replay')
    search=runpy(EXP+'/search.py');need(b'EXACT SEARCH MULTISETS PASS' in search,'Search replay status')
    diag=runpy(EXP+'/diagnostics.py');need(diag==read(EXP+'/diagnostics.json'),'Independent finite diagnostics')
    print(json.dumps(dict(status='PRESEAL CHECKS PASS; NOT SEALED' if preseal else 'EVIDENCE PASS',owned_files=len(inv()),immutable_references=len(refs),read_records=len(load(SRC+'/read-manifest.json')),selected_originals=len(sel),pinned_blobs=10373,manuscripts=749,corpus_originals=9340,outside_originals=1033,inherited_pdf_extraction_hashes=776,primary_pdf_replays=7,new_search_multisets=[q['records'] for q in load(SRC+'/queries.json')],inherited_search_multisets=[84,554,8],allowed_ledger_drift=drift,diagnostics='FINITE DIAGNOSTICS ONLY; NOT A GENERAL PROOF',analytic_verdict='SEE WRITTEN REPORT; NOT ESTABLISHED BY THIS VERIFIER',contribution_verdict='SEPARATE I93/PARENT GATE; NO COUNT CHANGE'),indent=2))
if __name__=='__main__':
    try:main()
    except Exception as e:
        print('EVIDENCE FAIL:',type(e).__name__+':',str(e),file=sys.stderr);sys.exit(1)
