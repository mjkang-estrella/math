exec(compile((__import__('pathlib').Path(__file__).parent/'research.py').read_text(),'research.py','exec'))
import re,html
out={}
for key in ['a209d5dc0c353563','88dd7de6ea8bfb5b']:
 t=(P/'sources'/(key+'.txt')).read_text(); heads=re.findall(r'"currentOid":"([a-f0-9]{40})"',t); out[key]={'currentOid':list(dict.fromkeys(heads))}; print(key,out[key])
for key in ['7af89af8c8e6efb0','6ba6dc2024d1c0d2','5fc57b80f25fe40e','14429a70095c21a0']:
 t=(P/'sources'/(key+'.txt')).read_text(); clean=html.unescape(re.sub('<[^>]+>',' ',t)); clean=re.sub(r'\s+',' ',clean)
 spans=[]
 for term in ['Submitted on','Submission history','Journal reference:','Journal reference','last revised']:
  n=clean.find(term)
  if n>=0: spans.append(clean[n:n+450])
 out[key]=spans; print(key,spans)
root=P.parents[5]; ls=(root/'sources/CONTENTS.md').read_text().splitlines(); hits=[]
for n,s in enumerate(ls):
 if 'crown' in s.lower(): continue
 if any(t in s.lower() for t in ['bicoloring','typical rank','hinged','roberts','saturated graphs','alternating descent','coefficientwise total','nesting poset','additive complexity']): hits.append({'line':n+1,'text':s})
js('catalog-scoped.json',hits)
print('CATALOG',json.dumps(hits)[:7000]); js('current-registry-and-versions.json',out)
