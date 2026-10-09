import pathlib,json,re,collections
root=pathlib.Path('frontier/sources/i14_spectral_width_novelty_r3');m=json.loads((root/'corpus-manifest.json').read_text()); pats={'urysohn':r'urysohn','spectral_scalar':r'spectral[\s~-]+scalar','torical_band':r'tori(?:cal|c|us)[\s~$\\{}-]*band','general_coefficient':r'(?:coefficient|parameter).{0,100}(?:scalar|curvature)|(?:scalar|curvature).{0,100}(?:coefficient|parameter)','weighted_curvature':r'(?:weighted|stabili[sz]ed)[\s~-]+scalar','macroscopic_dimension':r'macroscopic[\s~-]+dimension'};results={};titles=collections.defaultdict(set)
for e in m['files']:
 assert e['status']=='verified';s=(root/'corpus'/e['path']).read_text(errors='replace'); ss=re.sub(r'\s+',' ',s)
 for name,pat in pats.items():
  matches=list(re.finditer(pat,ss,re.I))
  if matches:
   results.setdefault(name,[]).append({'path':e['path'],'count':len(matches),'contexts':[ss[max(0,x.start()-160):x.end()+240] for x in matches]});titles[name].add(e['path'].split('/')[1])
p=pathlib.Path('frontier/experiments/i14_spectral_width_novelty_r3');(p/'corpus-search.json').write_text(json.dumps({'files_searched':len(m['files']),'patterns':pats,'matches':results,'titles':{k:sorted(v) for k,v in titles.items()}},indent=2)+'\n')
for k,v in titles.items(): print(k,len(v)); print('\n'.join(sorted(v)))
