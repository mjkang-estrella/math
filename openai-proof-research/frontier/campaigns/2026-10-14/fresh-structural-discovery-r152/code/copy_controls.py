# Original code, MIT. Writes ONLY its private disposable fixture before final sealing.
from pathlib import Path
import json,hashlib,subprocess,os,stat,shutil
ROOT=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r152')
assert Path.cwd()==Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
D=ROOT/'private/controls/fixture'
if D.exists():raise SystemExit('fixture already exists; no automatic replacement')
D.mkdir()
selected={'note.md':ROOT/'notes/02-integrated-reduction-and-gap.md','verify_packet.py':ROOT/'code/verify_packet.py'}
def digest(b):return hashlib.sha256(b).hexdigest()
identities={}
for dest,src in selected.items():
    data=src.read_bytes();(D/dest).write_bytes(data)
    identities[dest]={'original_path':str(src),'size':len(data),'sha256':digest(data)}
(D/'FINAL.md').write_text('Disposable selected-copy control, not an inherited archive.\n')
(D/'REPORT.md').write_text('Artifact control only.\n')
m={'schema':'r152-exact-payload-v1','files':{p:{'size':(D/p).stat().st_size,'sha256':digest((D/p).read_bytes())} for p in selected},'directories':['.']}
(D/'MANIFEST.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
anchors={n:digest((D/n).read_bytes()) for n in ['FINAL.md','MANIFEST.json','REPORT.md']}
def snapshot():
    out={}
    for base,dirs,files in os.walk(D):
        for name in ['.']+dirs+files:
            p=Path(base) if name=='.' else Path(base)/name
            s=p.lstat();key=str(p.relative_to(D));out[key]={'mode':stat.S_IMODE(s.st_mode),'nlink':s.st_nlink,'kind':'dir' if p.is_dir() else 'file','sha256':None if p.is_dir() else digest(p.read_bytes())}
    return out
cases=[]
def run(name,expect,override=None):
    before=snapshot();a=override or anchors
    cmd=['python','-B',str(ROOT/'code/verify_packet.py'),str(D),'--final-sha256',a['FINAL.md'],'--manifest-sha256',a['MANIFEST.json'],'--report-sha256',a['REPORT.md']]
    r=subprocess.run(cmd,capture_output=True,text=True,timeout=15)
    assert (r.returncode==0)==expect,(name,r.stdout,r.stderr)
    assert snapshot()==before,name+' modified fixture'
    cases.append({'name':name,'expected_accept':expect,'exit_code':r.returncode,'output':r.stdout.strip() or r.stderr.strip(),'read_only_snapshot_equal':True})
run('baseline',True)
p=D/'note.md';original=p.read_bytes();p.write_bytes(original+b'altered\n');run('changed payload',False);p.write_bytes(original)
p.unlink();run('missing payload',False);p.write_bytes(original)
p=D/'.extra';p.write_text('extra');run('hidden extra file',False);p.unlink()
p=D/'empty';p.mkdir();run('empty extra directory',False);p.rmdir()
a=dict(anchors);a['MANIFEST.json']='0'*64;run('wrong external manifest anchor',False,a)
p=D/'REPORT.md';original=p.read_bytes();p.write_bytes(original+b'altered');run('changed outside report',False);p.write_bytes(original)
run('restored baseline',True)
for dest,meta in identities.items():assert digest(Path(meta['original_path']).read_bytes())==meta['sha256']
(ROOT/'private/controls/receipt.json').write_text(json.dumps({'selected_original_identities':identities,'fresh_selected_copy_manifest':m,'detached_fixture_anchors':anchors,'cases':cases,'originals_unchanged':True},indent=2)+'\n')
print(json.dumps({'cases':len(cases),'all_expected':True,'all_verifier_invocations_read_only':True,'originals_unchanged':True}))
