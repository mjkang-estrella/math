import pathlib,json,hashlib,re
D=pathlib.Path(__file__).parent
for e in json.loads((D/'derivative-bindings.json').read_text()):
 p=pathlib.Path(e['path']);b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==e['sha256'];t=b.decode();print('\nFILE',p.name)
 pats={'irregular.txt':['Conjecture','Theorem 2.3','Proof. Let H'],'idp.txt':['Conjecture 5.1','Conjecture 5.2'],'idp-successor.txt':['Theorem 1','Theorem 2.1','Proof. We first'],'plactic.txt':['Theorem 3.1','Proof.','Theorem 2.8']}[p.name]
 for pat in pats:
  pos=t.find(pat);print(pat,pos,t[max(0,pos-200):pos+4000])
