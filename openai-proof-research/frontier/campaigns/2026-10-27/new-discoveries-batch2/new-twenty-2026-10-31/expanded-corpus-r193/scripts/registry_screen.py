import json,pathlib,re,hashlib
D=pathlib.Path(__file__).resolve().parents[1];x=json.loads((D/'extracted.json').read_text());vs=json.loads((D/'outputs/versions.json').read_text());out={}
for name in ['pool','omega','openai']:
 head=json.loads((D/f'sources/{name}-head.body').read_text())['sha'];t=json.loads((D/f'sources/{name}-tree.body').read_text());paths=[z['path'] for z in t['tree']];out[name]={'sha':head,'truncated':t.get('truncated'),'path_count':len(paths)}
 if name=='pool':scope='\n'.join(p.read_text(errors='replace') for p in (D/'sources').glob('pool-file-*.body'))
 else:
  files=[D/"sources"/(name+"-"+z+".body") for z in (["D5","Problems"] if name=="omega" else ["preprints"])]; scopes=[json.loads(p.read_text()) for p in files]; scope="\n".join(z["path"] for t in scopes for z in t["tree"]);out[name]["truncated"]=any(t.get("truncated",False) for t in scopes);out[name]["path_count"]=sum(len(t["tree"]) for t in scopes)
 out[name]['scope']='projects.yml and all candidates files' if name=='pool' else 'recursive path listing only; truncated scope where flagged'
 out[name]['screen']={}
 for i,v in x.items():
  terms=[i,v['source_url'].split('/')[-1]]+[a.split(',')[0] for a in vs[i]['authors']]+v['title'].split()[:3]
  # exclude generic English words; surname matches are leads only
  terms=[z for z in terms if len(z)>3 and z.lower() not in ['conjecture','total','second','period','bound','equality']]
  out[name]['screen'][i]={'terms':terms,'hits':[line[:500] for line in scope.splitlines() if any(z.lower() in line.lower() for z in terms)][:30]}
queries=[]
for p in sorted((D/'sources').glob('github-search-*.receipt.json')):
 r=json.loads(p.read_text());b=p.with_name(p.name.replace('.receipt.json','.body'));o=json.loads(b.read_text()) if b.exists() else {};queries.append({'receipt':str(p.relative_to(D)),'url':r['url'],'status':r.get('status'),'total_count':o.get('total_count'),'items':o.get('items',[])})
out['github_repository_search']=queries;out['limitation']='Bounded screens do not establish novelty; path screens are not proof-body review.'
(D/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2))
print({k:({a:b for a,b in v.items() if a!='screen'} if isinstance(v,dict) else len(v) if isinstance(v,list) else v) for k,v in out.items()})
