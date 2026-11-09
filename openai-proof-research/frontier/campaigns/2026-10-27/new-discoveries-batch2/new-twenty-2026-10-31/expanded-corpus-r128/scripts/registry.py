import pathlib,json,importlib.util,re
D=pathlib.Path(__file__).resolve().parents[1];s=importlib.util.spec_from_file_location('f',D/'scripts/fetch.py');f=importlib.util.module_from_spec(s);s.loader.exec_module(f)
sha=json.loads((D/'sources/omega-head.json').read_text())['sha']; base='https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'
print(f.get(('omega-root.json',base+sha)))
o=json.loads((D/'sources/omega-root.json').read_text())
for x in o['tree']:
 if x['path'] in ['D5','Problems']:print(f.get(('omega-'+x['path']+'.json',base+x['sha']+'?recursive=1')))
for name in ['D5','Problems']:
 p=D/('sources/omega-'+name+'.json')
 if p.exists():
  x=json.loads(p.read_text());hits=[v for v in x['tree'] if re.search('MeshPatternS21|Toeplitz|Lalanne|Wreath|GaussKuzmin|Maxout|CoverIdeal|SpectralCorrelation|Rainbow|Hurwitz|Markov.*Mirror|Mirror.*Markov',v['path'],re.I)]
  (D/f'outputs/registry-{name}-hits.json').write_text(json.dumps(hits,indent=2)+'\n');print(name,x.get('truncated'),[v['path'] for v in hits])
