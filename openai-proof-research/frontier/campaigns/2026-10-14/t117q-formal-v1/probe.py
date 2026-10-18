# MIT. Development compile only; final builder independently recreates outputs.
from pathlib import Path
import tempfile,os,subprocess,json
here=Path(__file__).absolute().parent
cache=here.parent/'formal/.lake/packages'
libs=[str((cache/p['name']/'.lake/build/lib/lean').resolve()) for p in json.loads((here/'lake-manifest.json').read_text())['packages'] if (cache/p['name']/'.lake/build/lib/lean').is_dir()]
with tempfile.TemporaryDirectory(prefix='t117q-probe-',dir='/var/tmp') as d:
 p=Path(d);(p/'T117Q.lean').write_bytes((here/'T117Q.lean').read_bytes())
 env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join([d]+libs)
 r=subprocess.run(['/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean','-o','T117Q.olean','T117Q.lean'],cwd=p,env=env,text=True,capture_output=True)
 print(r.stdout+r.stderr);print('EXIT',r.returncode)
