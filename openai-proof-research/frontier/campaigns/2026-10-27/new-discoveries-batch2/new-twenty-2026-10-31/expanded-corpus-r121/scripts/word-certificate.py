import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1]
def square(w):
 for a in range(len(w)):
  for d in range(1,(len(w)-a)//2+1):
   if w[a:a+d]==w[a+d:a+2*d]:return [a,d,w[a:a+d]]
 return None
def extensions(w):
 return [(j,c,w[:j]+c+w[j:]) for j in range(len(w),-1,-1) for c in '123']
w='3123';path=[w];records=[]
while True:
 ex=extensions(w);valid=[(j,c,u) for j,c,u in ex if square(u) is None]
 assert square(w) is None
 o=dict(word=w,internal_valid=[(j,c,u) for j,c,u in valid if 0<j<len(w)],valid=valid)
 records.append(o)
 if not valid:break
 w=valid[0][2];path.append(w)
assert len(path)==22
out=dict(seed=path[0],path=path,records=records,terminal_obstructions=[dict(position=j,letter=c,square=square(u)) for j,c,u in extensions(w)])
(D/'outputs/word-certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
