from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;S=P.parent/'sol-pendulum-source-moments-formal-r1'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
assert sha(S/'component-source.zip')=='05cef5c6617e1372f925340e70d5f4c5444afe2844840eb0fbc8ac902bd5fcb0'
for f,h in json.loads((S/'manifest.json').read_text()).items():assert sha(S/f)==h,f
files=[]
for p in sorted(S.rglob('*')):
 if not p.is_file() or 'EXTRACTED' in p.relative_to(S).parts or '__pycache__' in p.parts or any(p.name.endswith(e) for e in ['.olean','.olean.private','.olean.server','.ilean','.ir','.ir.sig','.o','.so','.pyc']):continue
 files.append({'path':str(p),'bytes':p.stat().st_size,'sha256':sha(p)})
(P/'review-freeze.json').write_text(json.dumps({'files':files},indent=2)+'\n');print('Frozen',len(files),'source/report files; delivered archive hash PASS')
