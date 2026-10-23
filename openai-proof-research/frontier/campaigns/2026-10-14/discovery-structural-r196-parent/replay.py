#!/usr/bin/env python3
"""Parent artifact replay and bounded algebra checks, with verifier limits explicit."""
import datetime,hashlib,itertools,json,shutil,stat,subprocess,sys,tempfile
from pathlib import Path
P=Path(__file__).resolve().parent; C=P.parent; PROJECT=C.parents[2]; A=C/'fresh-structural-discovery-r196'
ANCHORS={'FINAL.md':'3ed6bc313b4488595ae10fdede6579bfe3025766674c4224bcc7a7d82fd64f27',
         'MANIFEST.json':'b1cbd217cb68fbf5620775354dfff1361fa20285005a7872ca2404a2e7188ac8',
         'REPORT.md':'363ed73b3685338d481389a8e06ff600740ebe91672d30ba796b9624e29be51d'}
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def snap(root):
    assert not any(p.is_symlink()for p in root.rglob('*'))
    return {str(p.relative_to(root)):{'bytes':p.stat().st_size,'sha256':sha(p),'mode':stat.S_IMODE(p.stat().st_mode)}for p in root.rglob('*')if p.is_file()}
def verify(root,aa):
    return subprocess.run([sys.executable,'-I','-B',str(A/'verify_packet.py'),'--root',str(root),
        '--final-sha256',aa['FINAL.md'],'--manifest-sha256',aa['MANIFEST.json'],'--report-sha256',aa['REPORT.md']],capture_output=True,text=True,timeout=30)
def finite_checks():
    rows=[]
    for q in range(3,7):
        for d in range(q,2*q+3):
            edges={tuple(sorted((v,(v+s)%d)))for v in range(d)for s in range(1,q)}
            colors=[-1]*d
            def solve(v):
                if v==d:return True
                for color in range(q)if v else range(1):
                    if all(colors[u]!=color for u in range(v)if (u,v)in edges):
                        colors[v]=color
                        if solve(v+1):return True
                colors[v]=-1;return False
            exists=solve(0);assert exists==(d%q==0),(q,d)
            if exists:
                assert all(colors[u]!=colors[v]for u,v in edges)
                assert all(((v%q)!=c or ((v+s)%d)%q!=c)for v in range(d)for s in range(1,q)for c in range(q))
            rows.append({'q':q,'d':d,'coloring_exists':exists})
    def mul(a,b):return tuple(sum(a[2*i+k]*b[2*k+j]for k in range(2))for i in range(2)for j in range(2))
    def bracket(a,b):return tuple(x-y for x,y in zip(mul(a,b),mul(b,a)))
    h=(1,0,0,-1);e=(0,1,0,0);f=(0,0,1,0);lie=[]
    for q in range(3,13):
        x,y=e,f
        for _ in range(q-1):x=bracket(h,x);y=bracket(h,y)
        value=bracket(x,y);coefficient=(-1)**(q-1)*2**(2*q-2)
        assert value==tuple(coefficient*z for z in h)
        lie.append({'q':q,'coefficient':coefficient})
    return {'coloring_cases':rows,'sl2_cases':lie,'meaning':'Bounded bookkeeping checks only, not geometric/formal applicability proofs.'}
def main():
    before=snap(A);assert read(A/'ANCHORS.json')['anchors']==ANCHORS
    v=verify(A,ANCHORS);assert v.returncode==0,(v.stdout,v.stderr)
    m=read(A/'MANIFEST.json');names={x['path']for x in m['files']};assert len(names)==len(m['files'])==78
    outside={'MANIFEST.json','REPORT.md','ANCHORS.json'}|{'private/controls/'+x for x in ('FINAL.md','FROZEN.md','REPORT.md','MANIFEST.json')}
    assert set(before)==names|outside and not names&outside
    fz=read(A/'private/freeze-anchor.json');assert sha(A/'FROZEN.md')==fz['sha256']and (A/'FROZEN.md').stat().st_size==fz['bytes']==2277
    assert sha(A/'prefreeze-feasibility.md')==fz['prefreeze_sha256'] and fz['utc']<m['sealed_utc']
    tree=read(PROJECT/'sources/preprints-tree.json');assert not tree['truncated']and len(tree['tree'])==13223
    lookup={x['path']:x for x in tree['tree']};rows=[]
    for x in read(A/'private/source-authentication.json'):
        rows.append({'path':x['upstream_path'],'local':x['local_path'],**{k:x[k]for k in ('bytes','sha256','git_blob','url')}})
    rows+=read(A/'private/companion-authentication.json');assert len(rows)==37
    for x in rows:
        p=PROJECT/x['local'];b=p.read_bytes();e=lookup[x['path']]
        assert len(b)==x['bytes']==e['size'] and sha(p)==x['sha256']
        assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']==e['sha']
        assert x['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path']
    folders={x['path'].split('/')[1]for x in rows};assert len(folders)==3
    assert {x['path']for x in rows}=={k for k,e in lookup.items()if len(k.split('/'))>1 and k.split('/')[1]in folders and e['type']=='blob'}
    ledger=read(A/'private/reading-ledger.json')
    for x in ledger['source_and_companion_readings']:
        p=A/x['path'];assert sha(p)==x['sha256'] and p.stat().st_size==x['bytes']
    for x in ledger['primary_readings']:
        p=A/x['path'];b=p.read_bytes();s=b.decode();assert sha(p)==x['sha256']
        for (a,z),(ba,bz)in zip(x['unicode_character_extents'],x['corresponding_utf8_byte_extents']):
            assert b[ba:bz].decode()==s[a:z]
    history=read(A/'private/history-selected-extents.json');assert len(history)==3
    for x in history:
        start,end=x['byte_extent']
        with (PROJECT/x['original']).open('rb')as f:f.seek(start);b=f.read(end-start)
        assert hashlib.sha256(b).hexdigest()==x['sha256'] and b==(A/x['selected_copy']).read_bytes()
    controls=[];fixture=A/'private/controls';ca={n:sha(fixture/n)for n in ANCHORS}
    with tempfile.TemporaryDirectory(prefix='s196-controls-',dir=P)as td:
        d=Path(td)/'fixture';shutil.copytree(fixture,d)
        def check(name,expect,aa=ca):
            r=verify(d,aa);assert (r.returncode==0)==expect,(name,r.stderr);controls.append({'case':name,'accepted':r.returncode==0})
        check('intact copied fixture',True)
        p=d/'FROZEN.md';b=p.read_bytes();p.write_bytes(b+b'!');check('modified selected file',False);p.write_bytes(b)
        check('wrong manifest anchor',False,{**ca,'MANIFEST.json':'0'*64})
        p=d/'REPORT.md';b=p.read_bytes();p.write_bytes(b+b'!');check('modified outside report',False);p.write_bytes(b)
        p=d/'extra.txt';p.write_text('extra');check('unselected file is outside author verifier coverage',True);p.unlink()
        p=d/'FROZEN.md';mode=stat.S_IMODE(p.stat().st_mode);p.chmod(mode^0o100);check('mode is outside author verifier coverage',True);p.chmod(mode)
    finite=finite_checks();assert snap(A)==before
    result={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':ANCHORS,
            'verifier':json.loads(v.stdout),'selected_files':78,'selected_bytes':sum(x['bytes']for x in m['files']),
            'root_files':len(before),'parent_exact_inventory_matched':True,'author_verifier_limits':['Does not reject unselected extra files','Does not bind modes'],
            'canonical_blobs':37,'canonical_folders':3,'history_extents':3,'reading_record_bindings_matched':True,'controls':controls,
            'root_bytes_modes_unchanged':True,'frozen':fz,'author_proof_sha256':sha(A/'author-proof.md'),'author_proof_bytes':(A/'author-proof.md').stat().st_size,
            'finite_rechecks':finite}
    (P/'observed-root.json').write_text(json.dumps(before,indent=2)+'\n');(P/'replay.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items()if k not in ('finite_rechecks','anchors','controls')},indent=2))
if __name__=='__main__':main()
