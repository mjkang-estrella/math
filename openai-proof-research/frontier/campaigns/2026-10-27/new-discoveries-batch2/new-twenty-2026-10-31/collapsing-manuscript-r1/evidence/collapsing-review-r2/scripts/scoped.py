from run import *
import zipfile,stat
B='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin'
P=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
F=R/'scoped-fresh';assert not F.exists();F.mkdir()
with zipfile.ZipFile(R.parent/'expanded-corpus-r73/lean-packet/source-only-packet.zip') as z:
 for i in z.infolist():
  p=pathlib.PurePosixPath(i.filename);assert not p.is_absolute() and '..' not in p.parts and not stat.S_ISLNK(i.external_attr>>16) and p.suffix not in ['.olean','.ilean','.so']
 z.extractall(F)
F=F/'proof';E=os.environ.copy();E.update(PATH=B+':/usr/bin:/bin',LEAN_PATH=':'.join([str(F)]+[str(p) for p in P.glob('*/.lake/build/lib/lean')]),LEAN_NUM_THREADS='1',MALLOC_ARENA_MAX='2')
pre=['systemd-run','--user','--scope','-q','-p','MemoryMax=6G','-p','MemorySwapMax=0','-p','CPUQuota=200%']
for label,cmd in [('scoped-build',[B+'/lean','-j1','-DwarningAsError=true','-o','MathDB378395.olean','MathDB378395.lean']),('scoped-checker',[B+'/leanchecker','MathDB378395']),('scoped-audit',[B+'/lean','-j1','-DwarningAsError=true','ReviewAudit.lean'])]:
 assert run(label,pre+cmd,F,E)==0
