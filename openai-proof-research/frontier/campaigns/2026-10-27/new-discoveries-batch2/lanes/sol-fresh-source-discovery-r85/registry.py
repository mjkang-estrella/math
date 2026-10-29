import json,re
from pathlib import Path
b=Path(__file__).parent
out={}
for label,p in [('r83',b.parent/'sol-fresh-source-discovery-r83/sources/omega-compare.json'),('new',b/'sources/omega-delta.json')]:
 j=json.loads(p.read_text());fs=j.get('files',[]);cs=j.get('commits',[])
 out[label]={'total_commits':j.get('total_commits'),'returned_commits':len(cs),'returned_files':len(fs),'commit_bound':250,'file_bound':300,'at_file_bound':len(fs)>=300,'all_reported_commits_returned':len(cs)==j.get('total_commits'),'filenames':[f['filename'] for f in fs], 'relevant_filename_or_returned_patch_hits':[f['filename'] for f in fs if re.search(r'Miller.?Reiner|differential.poset|parametrized.Smith|Schubert.shenanigans',f['filename']+'\n'+f.get('patch',''),re.I)],'limits':'file list below endpoint bound is bounded delta evidence; returned patches may omit content; no full semantic current-registry clearance'}
(b/'registry-audit.json').write_text(json.dumps(out,indent=2));print(json.dumps({k:{x:v[x] for x in v if x!='filenames'} for k,v in out.items()},indent=2))
