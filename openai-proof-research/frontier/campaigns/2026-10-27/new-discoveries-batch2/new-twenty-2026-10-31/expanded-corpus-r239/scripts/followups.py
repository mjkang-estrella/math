import pathlib,json,importlib.util,urllib.parse
D=pathlib.Path(__file__).resolve().parents[1];spec=importlib.util.spec_from_file_location('lh',D/'scripts/http.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
for a in ['2103.00618','2404.10521','2510.00139','2609.30888','2607.23926','2205.05329']:
 h.get(a+'.abs.html','https://arxiv.org/abs/'+a);h.get(a+'.pdf','https://arxiv.org/pdf/'+a)
h.get('Schroeder-correction.pdf','https://archive.intlpress.com/site/pub/files/_fulltext/journals/joc/2024/0015/0001/JOC-2024-0015-0001-e007.pdf')
for repo in ['openai/math','the-omega-institute/trureturing']:
 k=repo.replace('/','-');sha=json.loads((D/'sources'/(k+'-head.json')).read_text())['sha'];h.get(k+'-root.json','https://api.github.com/repos/'+repo+'/git/trees/'+sha)
 if repo=='openai/math':h.get('openai-current-preprints-tree.json','https://api.github.com/repos/'+repo+'/git/trees/'+sha+':preprints?recursive=1')
h.get('one-third-repo-head.json','https://api.github.com/repos/ertwro/one_third_two_thirds/commits/HEAD')
h.get('one-third-repo-readme.txt','https://raw.githubusercontent.com/ertwro/one_third_two_thirds/HEAD/README.md')
