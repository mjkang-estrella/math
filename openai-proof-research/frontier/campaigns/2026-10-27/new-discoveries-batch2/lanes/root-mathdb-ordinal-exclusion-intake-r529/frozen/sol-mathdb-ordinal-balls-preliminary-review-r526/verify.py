"""Read-only exact-payload and direct binding verifier; no math execution."""
from pathlib import Path
import json,hashlib,sys
D=Path(__file__).resolve().parent
EXCLUDED={'manifest.json','verification-receipt.txt'}
def digest(p):
 b=p.read_bytes();return dict(size=len(b),sha256=hashlib.sha256(b).hexdigest())
def check(p,e):
 got=digest(p)
 if any(got[k]!=e[k] for k in ('size','sha256')):raise ValueError('hash/size mismatch: '+str(p))
try:
 m=json.loads((D/'manifest.json').read_text());assert set(m['excluded_exact_paths'])==EXCLUDED
 entries=m['files'];assert len({e['path'] for e in entries})==len(entries)
 actual={str(p.relative_to(D)) for p in D.rglob('*') if p.is_file()}-EXCLUDED
 mode=sys.argv[1] if len(sys.argv)>1 else None
 if mode=='--negative-hash':entries[0]['sha256']='0'*64
 elif mode=='--negative-size':entries[0]['size']+=1
 elif mode=='--negative-extra':actual.add('IN_MEMORY_UNLISTED_FILE')
 elif mode:raise ValueError('unknown option')
 if actual!={e['path'] for e in entries}:raise ValueError('exact inventory mismatch')
 for e in entries:
  p=D/e['path'];assert not p.is_symlink() and p.resolve().is_relative_to(D);check(p,e)
 refs=json.loads((D/'flatbindings.json').read_text())
 for e in refs:check(Path(e['path']),e)
 I=D.parent/'root-mathdb-candidate-intake-r525'
 im=json.loads((I/'manifest.json').read_text());ia={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(im['excluded_exact_paths'])
 assert ia=={e['path'] for e in im['files']}
 for e in im['files']:check(I/e['path'],e)
 for e in json.loads((I/'bindings.json').read_text()):check(Path(e['original']),e);check(Path(e['copy']),e)
 print(json.dumps(dict(status='PASS',payload_files=len(entries),direct_references=len(refs),intake_files=len(im['files']),intake_original_copy=True,manifest=digest(D/'manifest.json'),read_only=True,math_executed=False)))
except Exception as e:
 print(json.dumps(dict(status='FAIL',reason=str(e),mode=sys.argv[1:])),file=sys.stderr);sys.exit(1)
