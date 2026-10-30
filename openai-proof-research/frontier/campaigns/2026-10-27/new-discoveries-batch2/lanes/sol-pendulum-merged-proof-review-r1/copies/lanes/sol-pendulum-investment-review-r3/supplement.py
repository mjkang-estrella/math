from audit import B,L,sha
import pathlib,json,shutil,urllib.request,datetime,hashlib
R=L/'research';old=json.loads((R/'registry-topic-screen.json').read_text());aliases=old['aliases'];rows=[]
head=L/'copies/lanes/sol-fresh-source-discovery-r166/sources/openai-head.json';d=json.loads(head.read_text())
patch=[dict(path=f['filename'],has_patch='patch'in f,matches=[a for a in aliases if a.lower() in f.get('patch','').lower()]) for f in d['files']]
tree=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/sources/preprints-tree.json');shutil.copyfile(tree,R/'openai-pinned-preprints-tree.json');dt=json.loads(tree.read_text());print('OLDPREPRINT',str(dt)[:250])
def get(path,repo,head):
 url=f'https://raw.githubusercontent.com/{repo}/{head}/{path}';n='body-'+hashlib.sha256(url.encode()).hexdigest()[:16]+pathlib.Path(path).suffix
 try:
  with urllib.request.urlopen(url,timeout=20) as h:b=h.read(4*1024*1024)
  (R/n).write_bytes(b);rows.append(dict(path=path,url=url,file=n,sha256=sha(R/n),matches=[a for a in aliases if a.lower() in b.decode(errors='replace').lower()]))
 except Exception as e:rows.append(dict(path=path,url=url,error=str(e)))
for r in json.loads((R/'problems.json').read_text())['tree']:
 if r['type']=='blob' and any(s in r['path'].lower() for s in ['incomplete-beta','elliptic-tail','pendul','liquid','time-map']):get('Problems/'+r['path'],'the-omega-institute/trureturing','2b143c68ca72fcaccfe71d6233cb2c6db4c8c059')
paths=[r['path'] for r in dt.get('tree',[]) if r['type']=='blob'];hits=[s for s in paths if any(t in s.lower() for t in ['ellipt','pendul','beta','convex','time_map','liquid'])]
print('OPENAI_OLD_PATH_HITS',hits)
out=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),openai_current_commit_files=len(patch),openai_current_patch_screen=patch,openai_old_tree_sha256=sha(tree),openai_old_topic_paths=hits,bodies=rows)
(R/'supplement-screen.json').write_text(json.dumps(out,indent=2));print('NEWBODIES',rows)
