from work import *
rows=json.loads((L/'interval-commits.json').read_text());out=[]
for row in rows:
 for c in row['commits']:
  allf=[];page=1
  while True:
   d=api(f"commits/{c['sha']}?per_page=100&page={page}");fs=d['files'];allf+=fs
   if len(fs)<100:break
   page+=1
   if page>30:raise RuntimeError('3000 commit-file ceiling')
  q=L/f"retrieved/commit-files/{c['sha']}.json";q.parent.mkdir(exist_ok=True);q.write_text(json.dumps(allf))
  out.append({'commit':c['sha'],'pages':page,'files':len(allf),'file':str(q.relative_to(L))})
  (L/'commit-file-coverage.json').write_text(json.dumps(out,indent=2));print(c['sha'],len(allf),page,flush=True)
