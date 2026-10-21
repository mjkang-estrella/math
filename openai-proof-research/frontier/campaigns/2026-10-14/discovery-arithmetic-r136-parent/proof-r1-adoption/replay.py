#!/usr/bin/env python3
"""Read-only correctness-review intake and bounded symbolic certificate checks."""
import hashlib, importlib.util, json, math, stat, subprocess, sys
from fractions import Fraction
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parents[1];P=B.parents[2];R=B/'arithmetic-r136-proof-r1'
sp=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r161-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'149bde1bc3ac0697e47feae82579c7f8e0c3138f2bd537509496a487b33d10d8','MANIFEST.json':'4f6c5ecb2368c09dcf60ea030820cd95a0bd8f11ac0a9b42c04b377ae9be54ca','REPORT.md':'cf5c93078ebd0a20ea91b1305237844072a26e057c5d93dcd110b5edd2fcb88f'}
def read(f):return json.loads(f.read_text())
def dump(n,v):(O/n).write_text(json.dumps(v,indent=2)+'\n')
def finite_check():
    a=18961;B0_example=4;k=(3*a-1)//2
    prime=lambda n:n>=2 and all(n%d for d in range(2,math.isqrt(n)+1))
    leg=lambda n,p:-1 if pow(n%p,(p-1)//2,p)==p-1 else pow(n%p,(p-1)//2,p)
    assert a==67*283 and a+1==2*19*499 and all(prime(p)for p in [19,67,283,499]) and all(p%3==1 for p in [67,283])
    witnesses=[(1,67,'i'),(2,19,'ii'),(3,19,'ii'),(4,67,'i')]
    for n,p,side in witnesses:
        multiple=a if side=='i' else a+1;assert multiple%p==0 and multiple%(p*p)!=0 and leg(-n if side=='i' else n,p)==-1
    assert all(p%8==3 and leg(-2,p)==1 for p in [19,67,283,499]) and k==28441 and k%8==1
    # v=(2/s,1/s),u=(-(a+1)/(2s),-a/s), where s^2=k is a 2-adic unit square.
    A,C=2*a,-2*(a+1);v=(Fraction(2),Fraction(1));u=(Fraction(-(a+1),2),Fraction(-a))
    norm=lambda x:(A*x[0]*x[0]+C*x[1]*x[1])/k
    assert norm(v)==4 and norm(u)==-a*(a+1) and(A*v[0]*u[0]+C*v[1]*u[1])/k==0 and(v[0]*u[1]-v[1]*u[0])/k==-1
    return {'a':a,'B':B0_example,'witnesses':witnesses,'determinant':-4*a*(a+1),'small_vector_norm':4,'odd_local_symbols_and_two_adic_basis_identities':True,'passed':True,'scope':'Finite auxiliary-genus certificate only; no existential-B0 theorem counterexample or unbounded-family inference.'}
def main():
    before=snap(R);mode=stat.S_IMODE(R.stat().st_mode);status=read(O/'task-status.json')['structuredContent'];assert status['status']=='completed' and status['workState']=='result_available' and not status['hasPendingChildRuns'] and not status['hasPendingQuestion'] and status['pendingApproval'] is None
    assert all(sha(R/n)==v and v in status['summary']for n,v in ANCHORS.items());m=read(R/'MANIFEST.json');assert m['verdict']=='NEEDS_REPAIR' and len(m['files'])==82 and {n for n,e in before.items()if e['kind']=='file'}=={e['path']for e in m['files']}|set(ANCHORS)
    tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']}
    source=read(R/'private/source-authentication.json');assert len(source)==9
    for e in source:
        candidates=[R/x['path']for x in m['files']if x['sha256']==e['sha256']];assert candidates;raw=candidates[0].read_bytes();node=entries[e['path']];assert len(raw)==e['bytes']==node['size'] and hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==e['git_blob']==node['sha']
    primary=read(R/'private/primary-authentication.json');assert len(primary)==20
    for e in primary:
        f=R/e['file'];assert f.stat().st_size==e['bytes'] and sha(f)==e['sha256']
    stable=[]
    for e in read(R/'private/author-input-identities.json'):
        f=P/e['project_path'];assert f.stat().st_size==e['bytes'] and sha(f)==e['sha256'];stable.append({'path':e['project_path'],'sha256':e['sha256']})
    for e in read(R/'private/closure-input-checks.json')['checks']:
        f=P/e['path'];assert f.stat().st_size==e['bytes'] and sha(f)==e['sha256'] and e['matches_supplied_anchor']
    # Original history identities are the two exact author-selected intervals, not a broad scan.
    for line in(B/'fresh-arithmetic-discovery-r136/private/selected-history.jsonl').read_text().splitlines():
        e=json.loads(line);f=P/e['path'];a,b=e['bytes'];matches=[R/x['path']for x in m['files']if x['sha256']==e['selected_sha256']];assert matches and f.stat().st_size==e['total'] and sha(f)==e['sha256'] and oct(stat.S_IMODE(f.stat().st_mode))==e['mode'] and matches[0].read_bytes()==f.read_bytes()[a:b];stable.append({'path':e['path'],'sha256':e['sha256']})
    result=subprocess.run([sys.executable,'-I','-B',str(R/'verify_packet.py'),'--root',str(R),'--final-sha256',ANCHORS['FINAL.md'],'--manifest-sha256',ANCHORS['MANIFEST.json'],'--report-sha256',ANCHORS['REPORT.md']],cwd=P,capture_output=True,text=True,timeout=30);assert result.returncode==0,(result.stdout,result.stderr)
    certificate=finite_check();assert snap(R)==before and stat.S_IMODE(R.stat().st_mode)==mode and all(sha(P/e['path'])==e['sha256']for e in stable)
    dump('observed-root.json',{'root':before,'root_mode':mode});dump('finite-certificate.json',certificate);dump('replay.json',{'anchors':ANCHORS,'payload_files':82,'whole_root_files':85,'source_objects':9,'primary_PDF_text_pairs':10,'stable_named_originals':stable,'read_only_verifier':{'returncode':result.returncode,'stdout':result.stdout.strip()},'finite_symbolic_certificate_independently_recomputed':True,'root_unchanged':True,'limits':'Parent read full mathematical review, FINAL/REPORT, verifier and reading account, recovering review in two byte chunks and first7000 reading-account bytes separately after combined truncation. Protected source/primary/history proof bodies authenticated, not semantically reread by parent. Sealed diagnostic/control generators were not rerun. Finite identities do not refute an unknown B0 theorem; byte checks are not mathematical gates.'});print(json.dumps({'payload':82,'files':85,'source_objects':9,'primary_pairs':10,'stable_originals':len(stable),'finite_symbolic_certificate_passed':True,'root_unchanged':True}))
if __name__=='__main__':main()
