import pathlib,json,importlib.util,re
D=pathlib.Path(__file__).resolve().parents[1];sp=importlib.util.spec_from_file_location('h',D/'scripts/http.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h);o={}
for key,repo,wanted in [('omega','the-omega-institute/trureturing',['D5','Problems']),('openai','openai/math',['preprints'])]:
 sha=json.loads((D/'sources'/f'{key}-head/body').read_text())['sha'];h.get(key+'-root','https://api.github.com/repos/'+repo+'/git/trees/'+sha)
 root=json.loads((D/'sources'/f'{key}-root/body').read_text());o[key]={}
 for name in wanted:
  node=next((x for x in root.get('tree',[]) if x['path']==name),None)
  if not node:o[key][name]={'missing_root_entry':True};continue
  h.get(key+'-'+name+'-tree','https://api.github.com/repos/'+repo+'/git/trees/'+node['sha']+'?recursive=1');tree=json.loads((D/'sources'/(key+'-'+name+'-tree')/'body').read_text())
  terms=['determinantal','seacrest','variance','yancey','kriesell','inducibility','gapset','wronskian','orthogonal','primality','matroid','splitting']
  o[key][name]={'sha':node['sha'],'truncated':tree.get('truncated'),'count':len(tree.get('tree',[])),'keyword_paths':[x['path'] for x in tree.get('tree',[]) if any(t in x['path'].lower() for t in terms)]}
(D/'outputs/registry-scopes.json').write_text(json.dumps(o,indent=2))
