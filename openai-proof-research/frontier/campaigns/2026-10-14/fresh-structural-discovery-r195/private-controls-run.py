"""Build and test tiny copied artifacts only; never mutate original packet files."""
import hashlib
import json
import runpy
from pathlib import Path
root = Path(__file__).resolve().parent
verify = runpy.run_path(str(root / 'verify_packet.py'))['verify']
control = root / 'private-controls'
control.mkdir(exist_ok=True)
for name, original_name in [('FINAL.md','FINAL.md'),('REPORT.md','FROZEN.md'),('sample.txt','FROZEN.md')]:
    (control/name).write_bytes((root/original_name).read_bytes())
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
files = [dict(path=name,bytes=(control/name).stat().st_size,sha256=sha(control/name)) for name in ['FINAL.md','sample.txt']]
(control/'MANIFEST.json').write_text(json.dumps({'files':files},sort_keys=True)+'\n')
anchors = [sha(control/name) for name in ['FINAL.md','MANIFEST.json','REPORT.md']]
results=[]
verify(control,*anchors); results.append('unchanged tiny control accepted')
for name in ['sample.txt','FINAL.md','MANIFEST.json','REPORT.md']:
    path=control/name; original=path.read_bytes();path.write_bytes(original+b'!')
    try:
        verify(control,*anchors)
    except (ValueError,json.JSONDecodeError):
        results.append(name+' copied corruption rejected')
    else:
        raise AssertionError('corruption accepted: '+name)
    finally:
        path.write_bytes(original)
(control/'extra.txt').write_bytes(b'extra\n')
try:
    verify(control,*anchors)
except ValueError:
    results.append('extra copied file rejected')
else:
    raise AssertionError('extra file accepted')
(control/'extra.txt').unlink()
verify(control,*anchors)
(root/'private/control-results.json').write_text(json.dumps({'scope':'Artifact controls only; no mathematical verdict','results':results},indent=2)+'\n')
print('\n'.join(results))
