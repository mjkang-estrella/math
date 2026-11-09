from pathlib import Path
import os,sys,subprocess
r=Path(__file__).resolve().parents[1];build=r/'extracted/review-build';p=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages');l='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'
wrapper=r/'bin';wrapper.mkdir(exist_ok=True)
(wrapper/'lean').write_text('#!/bin/sh\nexec '+l+' -j1 -M3500 "$@"\n');(wrapper/'lean').chmod(0o755)
e=os.environ.copy();e.update(LEAN_PATH=':'.join([str(build)]+[str(t/'.lake/build/lib/lean') for t in sorted(p.iterdir()) if t.is_dir()]),TMPDIR=str(r/'tmp'),XDG_CACHE_HOME=str(r/'tmp/cache'),MALLOC_ARENA_MAX='2',LEAN_NUM_THREADS='1',PYTHONDONTWRITEBYTECODE='1',PATH=str(wrapper)+':'+str(Path(l).parent)+':'+e['PATH'])
def call(label,cmd):subprocess.run([sys.executable,'-I',str(r/'scripts/capped.py'),str(r/'logs'/(label+'.log'))]+cmd,env=e,cwd=build,check=True)
call('leanchecker-RefutationLocal-fixed',[str(Path(l).with_name('leanchecker')),'RefutationLocal'])
(build/'PrintAxioms.lean').write_text('import RefutationLocal\n#print axioms ContactPilot.refutationLocal\n#print axioms ContactPilot.local_contact_unique\n#print axioms ContactPilot.bidisk_local_contact_six\n')
call('axioms',[l,'-j1','-M3500','-DwarningAsError=true','PrintAxioms.lean'])
call('independent',[sys.executable,'-I',str(r/'scripts/independent.py')])
