#!/usr/bin/env python3
"""Build with installed Tectonic and lane-local resource cache; never fetch."""
import hashlib,json,os,shutil,subprocess
from pathlib import Path
b=Path(__file__).resolve().parents[1]
tool=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/t088p133-manuscript-r2/tools/tectonic')
(b/'paper/tmp').mkdir(parents=True,exist_ok=True)
(b/'paper/build').mkdir(parents=True,exist_ok=True)
if not (b/'paper/cache/tectonic').exists():
 shutil.copytree(Path.home()/'.cache/tectonic',b/'paper/cache/tectonic')
env=dict(os.environ);env.update(TMPDIR=str(b/'paper/tmp'),XDG_CACHE_HOME=str(b/'paper/cache'),SOURCE_DATE_EPOCH='1793145600',TZ='UTC')
cmd=[str(tool),'--only-cached','--keep-logs','--keep-intermediates','--outdir',str(b/'paper/build'),str(b/'main.tex')]
with (b/'paper/build/tectonic.stdout').open('wb') as out,(b/'paper/build/tectonic.stderr').open('wb') as err:
 p=subprocess.run(cmd,cwd=b,env=env,stdout=out,stderr=err)
assert p.returncode==0,(b/'paper/build/tectonic.stderr').read_text()
shutil.copyfile(b/'paper/build/main.pdf',b/'paper.pdf')
(b/'paper/build-command.json').write_text(json.dumps({'command':cmd,'environment':{k:env[k] for k in ['XDG_CACHE_HOME','SOURCE_DATE_EPOCH','TZ']},'tectonic_version':subprocess.check_output([str(tool),'--version'],text=True).strip(),'tectonic_sha256':hashlib.sha256(tool.read_bytes()).hexdigest(),'exit_code':p.returncode},indent=2)+'\n')
