from work import *
rows=json.loads((L/'interval-commits.json').read_text());out=[]
for row in rows:
 for c in row['commits']:
  sha=c['sha'];d=fetch(f'https://github.com/the-omega-institute/trureturing/commit/{sha}.patch',f'patches/{sha}.patch')
  if d is None:continue
  s=d.decode();paths=re.findall(r'^diff --git a/(.*?) b/(.*?)$',s,re.M);counts=[int(n) for n in re.findall(r'^ (\d+) files? changed',s,re.M)]
  names=[{'old_path':a,'new_path':b} for a,b in paths];out.append({'commit':sha,'parents':c['parents'],'diffstat_files':counts,'diff_blocks':len(paths),'count_matches':sum(counts)==len(paths),'paths':names})
  print(sha,len(paths),counts,flush=True)
(L/'patch-coverage.json').write_text(json.dumps(out,indent=2))
