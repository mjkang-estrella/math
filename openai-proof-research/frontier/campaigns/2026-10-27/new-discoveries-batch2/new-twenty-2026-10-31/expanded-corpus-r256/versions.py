import pathlib,json,re,hashlib
L=pathlib.Path(__file__).resolve().parent; out={};jobs=[]
for p in L.glob('*.abs.html'):
 s=p.read_text(); vs=sorted(set(re.findall(r'\[v(\d+)\]',s)),key=int); ar=re.search(r'arxiv.org/abs/(\d+\.\d+)',s)
 if not ar:continue
 a=ar[1];out[a]={'versions':vs,'history_excerpt':s[s.find('<h2>Submission history'):s.find('<h2>Submission history')+2000]}
 for v in vs[:-1]:jobs.append([a+'v'+v+'.pdf','https://arxiv.org/pdf/'+a+'v'+v])
(L/'versions.json').write_text(json.dumps(out,indent=2));(L/'jobs-versions.json').write_text(json.dumps(jobs));print(json.dumps({a:v['versions'] for a,v in out.items()},indent=2))
# Complete body structural inventory, acquisition != review.
inv={}
for p in L.glob('*.txt'):
 if p.name.endswith('.statement.txt'):continue
 hits=[{'line':i+1,'text':t} for i,t in enumerate(p.read_text(errors='replace').splitlines()) if re.search(r'(?i)^(definition|theorem|proposition|lemma|corollary|conjecture|example|remark)|figure|table ',t)]
 inv[p.name]=hits
(L/'body-inventory.json').write_text(json.dumps(inv,indent=2))
