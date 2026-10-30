from pathlib import Path
import hashlib,json,datetime,re,sys
L=Path(__file__).resolve().parent
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(1024*1024):h.update(b)
 return h.hexdigest()
def check():
 before=json.loads((L/'before.json').read_text());assert len(before['files'])==251
 for x in before['files']:
  for p in [Path(x['path']),Path(x['copy'])]:assert p.stat().st_size==x['bytes'] and sha(p)==x['sha256'],str(p)
 original=L/'copies/root-steiner-gp-source-review-adoption-r2/payload/retrieved/source-citations.json'
 records=json.loads(original.read_text())['results'];dec=json.loads((L/'citation-decisions.json').read_text());assert len(records)==len(dec)==19
 assert {x['id'] for x in records}=={x['id'] for x in dec}
 assert [x['record'] for x in dec if x['decision'].startswith('HOLD')]==[10,19]
 cov=json.loads((L/'coverage.json').read_text());assert cov['recommendation']=='HOLD' and not any(x['certified_complete'] for x in cov['intervals'])
 intervals=json.loads((L/'interval-commits.json').read_text());assert [len(x['commits']) for x in intervals]==[6,8]
 for x in intervals:assert len(x['commits'])==x['total'] and x['commits'][-1]['sha']==x['head']
 files=hunks=0
 for p in (L/'retrieved/diffs').glob('*.diff'):
  expected=None;old=new=0
  def end():
   if expected is not None:assert (old,new)==expected,(str(p),expected,old,new)
  with p.open() as f:
   for line in f:
    if line.startswith('@@ '):
     end();m=re.match(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@',line);assert m,line
     expected=(int(m[2] or 1),int(m[4] or 1));old=new=0;hunks+=1
    elif line.startswith('diff --git '):end();expected=None;files+=1
    elif expected is not None:
     if line.startswith(' '):old+=1;new+=1
     elif line.startswith('-'):old+=1
     elif line.startswith('+'):new+=1
     elif line.startswith('\\ No newline'):pass
  end()
 return {'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'frozen_original_and_copy_entries':251,'citations':19,'classified':17,'unresolved':2,'diff_files':files,'hunks':hunks,'integrity':'PASS','closure':'HOLD / NOT CERTIFIED COMPLETE'}
result=check()
if '--seal' in sys.argv:
 (L/'after.json').write_text(json.dumps(result,indent=2))
 rows=[{'path':str(p.relative_to(L)),'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['final-manifest.json','final-verification.json']]
 (L/'final-manifest.json').write_text(json.dumps({'files':rows,'excludes':['final-manifest.json','final-verification.json'],'note':'Integrity seal only; bounded evidence closure is HOLD.'},indent=2))
else:
 d=json.loads((L/'final-manifest.json').read_text())
 for x in d['files']:
  p=L/x['path'];assert p.stat().st_size==x['bytes'] and sha(p)==x['sha256'],str(p)
 result['manifest_sha256']=sha(L/'final-manifest.json');result['manifest_entries']=len(d['files'])
 (L/'final-verification.json').write_text(json.dumps(result,indent=2))
print(json.dumps(result))
