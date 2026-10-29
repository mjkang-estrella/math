import json,subprocess,re,time,sys
from pathlib import Path
lane=Path(__file__).resolve().parent;root=lane.parents[5]
pattern=r'(^|[^0-9.])2209[.]00986(v[0-9]+)?([^0-9.]|$)'
rx=re.compile(pattern)
assert rx.search('arXiv:2209.00986v2') and not rx.search('12209.00986') and not rx.search('2209.009860')
assert rx.search('2209.00986/Problem12.6')
semantic='--semantic' in sys.argv
if semantic:pattern=r'common.transversal|Aivazidis|Loukaki|sum of element orders|Giuga|arithmetic derivative|2209[.]00986'
batch=[];count=0
with (lane/('semantic-supplement.jsonl' if semantic else 'exact-id-supplement.jsonl')).open('w') as out:
 def run():
  global count
  if not batch:return
  r=subprocess.run(['rg','--threads','1','-n','-o','-i','--no-heading','--max-count','2',pattern,'--',*batch],cwd=root,capture_output=True,text=True)
  assert r.returncode in (0,1),r.stderr[:500]
  seen={}
  for line in r.stdout.splitlines():
   path=line.split(':',1)[0];seen[path]=seen.get(path,0)+1
   if seen[path]<=4:out.write(json.dumps({'native_original_file_match':line[:1000]})+'\n')
  count+=len(batch);batch.clear()
 for line in (lane/'audit-manifest.jsonl').open():
  batch.append(json.loads(line)['path'])
  if len(batch)==200:run()
 run()
print(json.dumps({'status':'PASS','files_screened':count,'selftests':4,'pattern':pattern,'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())}))
