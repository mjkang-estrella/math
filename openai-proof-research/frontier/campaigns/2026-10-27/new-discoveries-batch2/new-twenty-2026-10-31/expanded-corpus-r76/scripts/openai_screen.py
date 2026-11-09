from fetch import *
h=json.loads((D/'sources/openai-head.json').read_text())['sha'];get(('openai-tree.json',f'https://api.github.com/repos/openai/math/git/trees/{h}'))
a=json.loads((D/'sources/openai-tree.json').read_text())
for x in a['tree']:
 if x['path']=='preprints':get(('openai-preprints.json',f"https://api.github.com/repos/openai/math/git/trees/{x['sha']}?recursive=1"))
words=['moufang','associator','drapal','vojt','gepner','kaiser','carmichael','alfaro','firefight']
out={}
for name in ['openai-preprints','omega-D5','omega-Problems']:
 a=json.loads((D/f'sources/{name}.json').read_text());out[name]={'truncated':a.get('truncated'),'entries':len(a.get('tree',[])),'hits':[x for x in a.get('tree',[]) if any(w in x['path'].lower() for w in words)]}
(D/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2)[:5000])
