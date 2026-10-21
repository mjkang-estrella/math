"""Writes only an own-root small copied fixture; run before final sealing."""
from pathlib import Path
import hashlib,json,os,shutil,stat
from verify import inventory,verify,digest,ENVELOPES
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r158')
F=R/'private/copied-controls'; F.mkdir(exist_ok=False)
for src,dest in [('notes/02-integrated-reduction-and-ending.md','math.md'),('code/finite_partitions.py','finite.py'),('receipts/finite-partitions.json','finite.json')]: shutil.copyfile(R/src,F/dest)
(F/'FINAL.md').write_text('Own three-member selected fixture; no inherited manifest.\n')
(F/'REPORT.md').write_text('Copied artifact controls only; no mathematical grade.\n')
files,dirs=inventory(F)
(F/'MANIFEST.json').write_text(json.dumps({'schema':'r158-exact-payload-v1','envelopes':list(ENVELOPES),'files':{k:v for k,v in files.items() if k not in ENVELOPES},'directories':dirs},sort_keys=True,indent=2)+'\n')
anchors=[digest(F/n) for n in ENVELOPES]
def snap():
 files,dirs=inventory(F); modes={}
 for base,ds,fs in os.walk(F):
  for n in ds+fs:
   p=Path(base)/n; st=p.lstat(); modes[str(p.relative_to(F))]=[stat.S_IMODE(st.st_mode),st.st_nlink,st.st_mtime_ns]
 return files,dirs,modes
rows=[]
def test(name,expected,a=anchors):
 before=snap()
 try: result=verify(F,a); ok=True; detail=result
 except Exception as e: ok=False; detail=str(e)
 after=snap(); assert before==after; assert ok==expected,(name,ok,expected)
 rows.append({'case':name,'expected_accept':expected,'accepted':ok,'nonmutation':True,'detail':detail})
test('baseline',True)
p=F/'math.md'; b=p.read_bytes(); p.write_bytes(b+b'X'); test('changed payload',False); p.write_bytes(b)
p=F/'finite.py'; b=p.read_bytes(); p.unlink(); test('missing payload',False); p.write_bytes(b)
p=F/'.extra'; p.write_text('x'); test('hidden extra',False); p.unlink()
p=F/'empty-extra'; p.mkdir(); test('empty directory extra',False); p.rmdir()
a=anchors.copy(); a[1]='0'*64; test('wrong detached manifest anchor',False,a)
p=F/'REPORT.md'; b=p.read_bytes(); p.write_bytes(b+b'X'); test('changed report',False); p.write_bytes(b)
test('restored baseline',True)
(R/'receipts/copied-controls.json').write_text(json.dumps({'membership':'own selected three-member payload, exact fixture manifest','anchors':dict(zip(ENVELOPES,anchors)),'cases':rows,'scope':'artifact expectations only; no mathematical gate'},indent=2)+'\n')
print('Eight copied-control expectations met; every verifier invocation left its input unchanged.')
