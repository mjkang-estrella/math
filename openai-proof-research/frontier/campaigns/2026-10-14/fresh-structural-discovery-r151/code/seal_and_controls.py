"""One-time local seal and bounded copied controls. MIT.
Always run from the actual project root. No external writes or git operations.
"""
from pathlib import Path
import hashlib,json,os,stat,subprocess,sys,shutil
P=Path.cwd();R=P/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r151'
assert P==Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
sys.dont_write_bytecode=True
sys.path.insert(0,str(R/'code'))
from verify import inventory,verify,digest,ENV

def seal(root):
    assert not (root/'MANIFEST.json').exists(),'already sealed; refuse reseal'
    files,dirs=inventory(root)
    for n in ('FINAL.md','REPORT.md'):files.pop(n)
    m={'schema':'r151-exact-payload-v1','envelopes_excluded':list(ENV),'files':files,'directories':dirs}
    (root/'MANIFEST.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
    return tuple(digest(root/n) for n in ENV)

def snapshot(root):
    files,dirs=inventory(root)
    modes={'.':stat.S_IMODE(root.stat().st_mode)}
    for p in root.rglob('*'):
        s=p.lstat();modes[p.relative_to(root).as_posix()]=[stat.S_IMODE(s.st_mode),s.st_nlink]
    return {'files':files,'directories':dirs,'modes_links':modes}

def controls():
    D=R/'private/controls';D.mkdir(exist_ok=True);F=D/'selected-copy'
    assert not F.exists();F.mkdir()
    chosen=['notes/02-integrated-reduction-and-gap.md','code/payoff_diagnostic.py']
    identities=[]
    for rel in chosen:
        q=F/rel;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(R/rel,q)
        identities.append({'source_relative':rel,'sha256':digest(R/rel),'size':q.stat().st_size})
    (F/'FINAL.md').write_text('Disposable selected-copy fixture; not the incoming original packet.\n')
    (F/'REPORT.md').write_text('Own two-file membership. Its manifest was computed afresh.\n')
    anchors=seal(F);results=[]
    def check(name,expect,aa=anchors):
        before=snapshot(F)
        proc=subprocess.run([sys.executable,'-B',str(R/'code/verify.py'),str(F),'--final',aa[0],'--manifest',aa[1],'--report',aa[2]],capture_output=True,text=True,timeout=20,cwd=P)
        after=snapshot(F)
        assert before==after,'verifier changed fixture'
        assert (proc.returncode==0)==expect,(name,proc.stdout,proc.stderr)
        results.append({'case':name,'expected_accept':expect,'returncode':proc.returncode,'stdout':proc.stdout.strip(),'before':before,'after':after})
    check('baseline',True)
    q=F/chosen[0];b=q.read_bytes();q.write_bytes(b+b'changed\n');check('changed payload',False);q.write_bytes(b)
    q.unlink();check('missing payload',False);q.write_bytes(b)
    extra=F/'.hidden-extra';extra.write_text('extra');check('hidden extra',False);extra.unlink()
    extra=F/'empty-extra';extra.mkdir();check('empty extra directory',False);extra.rmdir()
    check('wrong detached anchor',False,(anchors[0],'0'*64,anchors[2]))
    q=F/'REPORT.md';b=q.read_bytes();q.write_bytes(b+b'changed');check('changed outside REPORT',False);q.write_bytes(b)
    check('restored baseline',True)
    for x in identities:assert digest(R/x['source_relative'])==x['sha256']
    originals=json.loads((R/'private/incoming-originals.json').read_text());current=[]
    for x in originals:
        same=digest(P/x['path'])==x['sha256'];current.append({'path':x['path'],'same_since_late_snapshot':same,'mutable':x['mutable']})
        if not x['mutable']:assert same
    out={'selected_originals':identities,'selected_copy_anchors':dict(zip(ENV,anchors)),'results':results,'incoming_originals_recheck':current}
    (D/'results.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('controls',len(results),'all behaved as expected; verifier snapshots unchanged')

if __name__=='__main__':
    if sys.argv[1:] == ['controls']:controls()
    elif sys.argv[1:] == ['seal']:
        anchors=seal(R);print(json.dumps({'anchors':dict(zip(ENV,anchors)),'verification':verify(R,anchors)},indent=2))
    else:raise SystemExit('use controls or seal')
