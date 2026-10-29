import subprocess,json,hashlib,datetime,re
from pathlib import Path
P=Path(__file__).resolve().parent
def git(repo,*args):
 return subprocess.check_output(['git','-c','pack.threads=1','-c','index.threads=1','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','--git-dir='+str(P/(repo+'.git')),*args],text=True)
records={}
for repo in ('omega','openai'):
 tree=P/(repo+'-tree.txt'); lines=tree.read_text().splitlines()
 records[repo]={'head':git(repo,'rev-parse','HEAD').strip(),'commit':git(repo,'show','-s','--format=%H%n%cI%n%s','HEAD').strip(),'tree_entries':len(lines),'tree_sha256':hashlib.sha256(tree.read_bytes()).hexdigest(),'complete_recursive_git_ls_tree':True}
 paths=[line.split('\t',1)[1] for line in lines]
 matches=[p for p in paths if re.search(r'irregular|irregulator|bensmail|catherinot|fioravantes|marcille|oijid|2511[.-]14514',p,re.I)]
 records[repo]['target_path_matches']=matches
 if repo=='openai':
  (P/'openai-CONTENTS.md').write_text(git(repo,'show','HEAD:CONTENTS.md'))
 else:
  for path in matches:
   if path.startswith(('Problems/','D5/')):
    dest=P/'current-bodies'/path;dest.parent.mkdir(parents=True,exist_ok=True)
    dest.write_text(git(repo,'show','HEAD:'+path))
records['utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
records['route']='Public Git smart HTTP ls-remote and shallow blob-filtered bare clones, no GitHub API retry, no credentials, no alternate host/proxy.'
records['failures']=['First clone of each repository failed unable to create thread / invalid index-pack under AS512MiB; retried with pack.threads=1 and index.threads=1, same caps; both succeeded.']
records['limits']='Complete path inventory and selected current bodies only; not yet body audit of every potentially relevant record; no global absence or priority claim.'
(P/'CURRENT-REGISTRIES.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps({k:v for k,v in records.items() if k!='failures'},indent=2))
