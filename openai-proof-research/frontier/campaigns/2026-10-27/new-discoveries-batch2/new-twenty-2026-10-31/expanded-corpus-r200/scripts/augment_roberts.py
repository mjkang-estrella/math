import pathlib
D=pathlib.Path(__file__).resolve().parents[1];p=D/'scripts/roberts.py';s=p.read_text()
s=s.replace('rows=[]\nfor sh in shapes:', '''yam=[]
for j,p in enumerate(perms):
 tab=[]
 for x in p:
  for row in tab:
   k=next((k for k,z in enumerate(row) if z>x),len(row))
   if k==len(row):row.append(x);break
   row[k],x=x,row[k]
  else:tab.append([x])
 if [z for row in tab for z in row]==list(range(1,n+1)):
  lam=tuple(map(len,tab));block={x:i for i,row in enumerate(tab) for x in row};yam.append((j,lam,[block[x] for x in p]))
rows=[]
for sh in shapes:''')
s=s.replace('for root,counts in comps.items():', '''fixed={}
 for j,lam,word in yam:
  jam=False
  for a in range(max(word)):
   left=[i for i,x in enumerate(word) if x==a][::-1];right=[i for i,x in enumerate(word) if x==a+1][::-1]
   for k in range(min(len(left),len(right)-1)):
    lo,hi=sorted([left[k],right[k+1]])
    if any(x<=lo and hi<=y for x,y in pistols):jam=True
  if not jam:fixed.setdefault(find(j),C.Counter())[lam]+=1
 for root,counts in comps.items():''')
s=s.replace("if v or any(x<0 or x.denominator!=1 for x in coeff.values()):", "if v or any(x<0 or x.denominator!=1 for x in coeff.values()) or any(z>coeff.get(lam,0) for lam,z in fixed.get(root,{}).items()):")
s=s.replace("'counts':dict(counts)","'fixed':{str(k):z for k,z in fixed.get(root,{}).items()},'counts':dict(counts)")
s=s.replace("'components':len(comps)","'components':len(comps),'fixed_words':sum(sum(x.values()) for x in fixed.values())")
s=s.replace("roberts-{n}-{target}.json","roberts-fixed-{n}-{target}.json").replace("Schur positivity necessary condition only; fixing and injection not checked","Schur positivity and fixed-word coefficient-capacity necessary conditions only; full signature-preserving injection not checked")
p.write_text(s)
