import pathlib,json,math,itertools,hashlib
P=pathlib.Path(__file__).resolve().parent;L=P.parent
out={'carmichael561':{'composite_factors':[3,11,17],'all_residues_tested':561,'all_pass':all(pow(a,561,561)==a for a in range(561))},'grassmann':[],'fishburn':[]}
for k in range(2,21):
 m=4*k+2;n=4*k+9;C=lambda r:math.comb(m,r) if 0<=r<=m else 0
 size=28*C(2*k)+22*C(2*k+3)+C(2*k+5)+7*C(2*k+4)+7*C(2*k+2)+28*C(2*k+1)+sum(math.comb(n,i) for i in range(2*k+7,n+1,2))
 out['grassmann'].append({'k':k,'size':size,'deficit':2**(n-2)-size})
for n in range(1,8):
 counts=[0,0,0];four=0
 for p in itertools.permutations(range(1,n+1)):
  if any(p[j+1]>p[j] and p[j]-1 in p[j+2:] for j in range(n-1)):continue
  pats=set()
  for inds in itertools.combinations(range(n),4):
   a=[p[i] for i in inds];pats.add(''.join(str(1+sum(y<x for y in a)) for x in a))
  for i,t in enumerate(['3214','4132','4213']):counts[i]+=t not in pats
  four+=not pats.intersection({'1324','2143','1423','3124'})
 out['fishburn'].append({'n':n,'triple_counts':counts,'four_count':four,'formula':(n+2)*(n*n-2*n+3)//6})
(P/'calculation-results.json').write_text(json.dumps(out,indent=2)+'\n')
ctx={}
for name in ['accepted-exclusions.json','historical-dispositions.json']:
 o=json.loads((L/'root-mathdb-accepted-exclusions-r304'/name).read_text());ctx[name]=o
ids={x['mathdb_id'] for x in json.loads((P/'assigned-records.json').read_text())}
print('Accepted family titles:')
for f in ctx['accepted-exclusions.json']['families']:print(f.get('number'),f.get('title'),f.get('scope'))
print('Assigned ID mentions in historical dispositions:')
s=json.dumps(ctx['historical-dispositions.json'],ensure_ascii=False)
for i in ids:
 pos=s.find(str(i))
 if pos>=0:print(i,s[max(0,pos-140):pos+550])
print(json.dumps(out,indent=2))
