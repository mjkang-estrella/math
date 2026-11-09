import pathlib,json,sys,re
D=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(D/'scripts'));from fetch import get
r=json.loads((D/'outputs/registry-screen.json').read_text())
get('omega-root.json',f"https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{r['heads']['omega']}")
o=json.loads((D/'sources/omega-root.json').read_text())
for p in o.get('tree',[]):
 if p['path'] in ['D5','Problems']:
  get('omega-'+p['path']+'.json',p['url']+'?recursive=1')
# unchanged OpenAI HEAD: bind cached full path scope by actual hash, no body clearance
import hashlib
p=D.parent/'fresh-corpus-r10/sources/registry-preprints.json'
if p.exists():
 data=p.read_bytes();r['openai_cached_path_scope']={'path':str(p),'sha256':hashlib.sha256(data).hexdigest(),'head_unchanged':True};text=data.decode()
else:text=''
texts={p.name:p.read_text(errors='replace') for p in [D/'sources/projects.yml',*list((D/'sources').glob('pool-*')),*list((D/'sources').glob('omega-D5.json')),*list((D/'sources').glob('omega-Problems.json'))]}
terms=['pinnacle','Gessel','Zhuang','Brimkov','Crupi','Ficarra','frustrat','Larman','Morita','binariz','Forking','homological linear','internal partition','off-diagonal common','graphical regular','correctable','joints']
r['keyword_path_matches']={t:[{'file':f,'line':j+1,'text':l[:500]} for f,s in texts.items() for j,l in enumerate(s.splitlines()) if t.lower() in l.lower()] for t in terms}
r['github_hit_assessment']='pinnacle education website and Comp_Sci_Sem_2 Bee Movie false positives; inspect descriptions; no matching mathematical proof in these 8 bounded queries.'
r['scope']='Lean Pool LeanPool/projects.yml and all 10 candidates files; all exact source IDs and target IDs; selected authors/keywords. Omega fresh D5/Problems paths; OpenAI cached path listing at unchanged HEAD. Path screening is not exhaustive theorem-body clearance.'
(D/'outputs/registry-screen.json').write_text(json.dumps(r,indent=2))
