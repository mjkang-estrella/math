from pathlib import Path
import hashlib,json,re
P=Path(__file__).resolve().parent;S=P.parent/'sol-steiner-gp-fixed-gap-closure-r3'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
rows=json.loads((S/'final-manifest.json').read_text())['files']
for r in rows:
 p=S/r['path'];assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes'],str(p)
original=json.loads((S/'before.json').read_text())['files'];assert len(original)==251
for r in original:
 for k in ['path','copy']:
  p=Path(r[k]);assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes'],str(p)
dec=json.loads((S/'citation-decisions.json').read_text());assert len(dec)==19 and [r['record'] for r in dec if r['decision'].startswith('HOLD')]==[10,19]
ints=json.loads((S/'interval-commits.json').read_text());assert [len(r['commits']) for r in ints]==[6,8]
for r in ints:assert len(r['commits'])==r['total'] and r['commits'][-1]['sha']==r['head']
blocks=hunks=0
for p in (S/'retrieved/diffs').glob('*.diff'):
 expected=None;old=new=0
 with p.open() as f:
  for line in f:
   if line.startswith('@@ ') or line.startswith('diff --git '):
    if expected is not None:assert (old,new)==expected,(str(p),expected,old,new)
    expected=None
    if line.startswith('@@ '):
     m=re.match(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@',line);assert m
     expected=(int(m[2] or 1),int(m[4] or 1));old=new=0;hunks+=1
    else:blocks+=1
   elif expected is not None:
    if line.startswith(' '):old+=1;new+=1
    elif line.startswith('-'):old+=1
    elif line.startswith('+'):new+=1
 if expected is not None:assert (old,new)==expected
saved=json.loads((S/'final-verification.json').read_text());assert blocks==saved['diff_files'] and hunks==saved['hunks']
files=[{'path':str(p),'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(S.rglob('*')) if p.is_file() and '__pycache__' not in p.parts]
(P/'review-freeze.json').write_text(json.dumps({'files':files},indent=2)+'\n')
out={'status':'PASS','manifest_entries':len(rows),'original_copy_entries':len(original),'diff_blocks':blocks,'hunks':hunks,'review_freeze_paths':len(files),'coverage_complete':False,'formal_pass':False,'credit':0}
(P/'replay-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
