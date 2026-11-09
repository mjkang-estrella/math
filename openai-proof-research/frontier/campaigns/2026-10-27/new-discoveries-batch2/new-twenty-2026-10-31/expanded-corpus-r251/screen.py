from pathlib import Path
import json,re,hashlib
L=Path(__file__).resolve().parent;O=L/'outputs';O.mkdir(exist_ok=True)
R=json.loads((L/'reservation.json').read_text())
terms={str(r['mathdb_id']):[str(r['mathdb_id']),r['source_url'].split('/')[-1]] for r in R['rows']}
kw={333904:['average distance','jordan curve'],333949:['queen','chess'],334146:['distinguishing stability','alikhani','soltani'],334195:['mou','pasechnik','2-tough'],334251:['nath','sellers','core partition'],334294:['naserasr','projective cube'],334350:['svinin'],334351:['svinin'],334352:['svinin'],334379:['pfaffian','cluster count'],334436:['threshold graph','diagonal harmonics','meszaros'],334438:['internal energy','potts'],334441:['pin(2)','bar-natan'],334561:['equirepresentation','equi-n','fair representation'],334677:['zerbib','tuza'],334709:['prefix normal','burcsi','liptak'],334732:['stapledon','chromatic polynomial'],334765:['plain eigenvalue','koolen'],334796:['pseudo-disk','palvolgyi'],334797:['pseudo-disk','palvolgyi']}
files=list((L/'http').glob('pool-*'));files+=[L/'http/openai-current-CONTENTS.md']
trees={}
for name in ['leanpool','omega']:
 p=L/f'http/{name}-tree.json';t=json.loads(p.read_text());trees[name]={'sha':t['sha'],'truncated':t.get('truncated'),'paths':len(t['tree'])}
 f=L/f'{name}-paths.txt';f.write_text('\n'.join(x['path'] for x in t['tree']));files.append(f)
res={}
for i,ts in terms.items():
 ts+=kw[int(i)];hits=[]
 for p in files:
  for n,line in enumerate(p.read_text(errors='replace').splitlines(),1):
   matched=[s for s in ts if s.lower() in line.lower()]
   if matched:hits.append({'path':str(p.relative_to(L)),'line':n,'terms':matched,'text':line[:500]})
 res[i]={'terms':ts,'hits':hits,'limitation':'Substring/path screen; incidental hits not prior proofs; no full-body global clearance.'}
searches=[]
for p in (L/'http').glob('github-search-*.json'):
 if p.name.endswith('receipt.json'):continue
 x=json.loads(p.read_text());searches.append({'file':p.name,'total_count':x.get('total_count'),'receipt':p.name+'.receipt.json'})
(O/'registry-screen.json').write_text(json.dumps({'trees':trees,'repository_searches':searches,'by_id':res},indent=2));print(trees)
