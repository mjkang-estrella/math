import xml.etree.ElementTree as E,re,json,sympy as S,math
root=E.parse('sources/reliability-figure7c.svg').getroot();paths=[e.attrib['d'] for e in root if e.tag.endswith('path')]
centres=[];segments=[]
for d in paths:
 if 'C' in d:
  vals=re.findall(r'ZM([0-9.]+) ([0-9.]+)',d);assert len(vals)==1;centres.append(tuple(map(float,vals[0])))
 else:
  vals=list(map(float,re.findall(r'[0-9.]+',d)))
  if 'H' in d:points=[vals[:2],[vals[2],vals[1]]]
  else:points=[vals[:2],vals[2:]]
  segments.append(points)
edges=[]
for pts in segments:
 ends=[min(range(10),key=lambda i:math.dist(pt,centres[i])) for pt in pts];edges.append(ends)
L=S.zeros(10)
for a,b in edges:L[a,a]+=1;L[b,b]+=1;L[a,b]-=1;L[b,a]-=1
x=dict(source='arxiv 2005.02848v1 Figure 7(c)',vertices=centres,edges=edges,spanning_trees=int(L[:9,:9].det()),FCG_10_5_spanning_trees=1815,conclusion='source own displayed graph already beats its FCG conjecture near p=0; zero-credit source-internal contradiction')
print(x);json.dump(x,open('outputs/reliability-source-figure.json','w'),indent=2)
