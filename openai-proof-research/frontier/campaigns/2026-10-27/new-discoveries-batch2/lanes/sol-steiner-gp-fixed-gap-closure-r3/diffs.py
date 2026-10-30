from work import *
rows=json.loads((L/'interval-commits.json').read_text());out=[]
for row in rows:
 for c in row['commits']:
  sha=c['sha'];d=fetch(f'https://github.com/the-omega-institute/trureturing/commit/{sha}.diff',f'diffs/{sha}.diff')
  if not d:continue
  s=d.decode();blocks=re.split(r'(?=^diff --git )',s,flags=re.M)[1:];records=[]
  for b in blocks:
   h=b.splitlines();m=re.match('diff --git a/(.*?) b/(.*?)$',h[0]);assert m
   old,new=m.groups();rec={'old_path':old,'new_path':new,'removed':'deleted file mode' in b,'added':'new file mode' in b,'renamed':'rename from ' in b,'index':next((v for v in h if v.startswith('index ')),None)}
   records.append(rec)
  out.append({'commit':sha,'parents':c['parents'],'file':f'retrieved/diffs/{sha}.diff','files':records});print(sha,len(records),flush=True)
(L/'diff-coverage.json').write_text(json.dumps(out,indent=2))
