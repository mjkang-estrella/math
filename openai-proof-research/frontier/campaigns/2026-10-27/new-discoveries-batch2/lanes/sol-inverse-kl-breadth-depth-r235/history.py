from pathlib import Path
import hashlib,json,re
L=Path(__file__).resolve().parent
root=L.parents[5]
patterns={'inverse':r'2609\.13417|Gao.{0,20}Xie|inverse.{0,35}(Kazhdan|log.concav)', 'dice':r'non.transitive dice|Easlick|2610\.40321', 'zonotopal':r'zonotopal|2610\.38469|cycle congruence', 'triangulations':r'2610\.39116|intersecting.{0,20}triangulation', 'chessboard':r'2610\.37827|chessboard|Segre.{0,25}resolution', 'signed':r'2610\.38412|nice partition|signed.graphic arrangement', 'capped':r'2610\.37578|capped graphs', 'coprime':r'2610\.37512|coprime match|M.number', 'immanants':r'2610\.39021|hook.{0,20}immanant'}
bindings=[];hits=[]
for p in root.rglob('*.md'):
 if L in p.parents or any(x in p.parts for x in ['originals','frozen','legacy-aliases','.git']):continue
 if p.name not in ['SUMMARY.md','SCOUTING.md','discovery.md','PROOF.md','review.md','FINDINGS.md']:continue
 data=p.read_bytes()
 if len(data)>300000:continue
 sha=hashlib.sha256(data).hexdigest();bindings.append({'path':str(p),'sha256':sha})
 # Bind immutable reference before scientific reading, no source copies.
 for key,pat in patterns.items():
  for no,line in enumerate(data.decode(errors='replace').splitlines(),1):
   if re.search(pat,line,re.I):hits.append({'family':key,'path':str(p),'sha256':sha,'line':no,'text':line[:1600]})
(L/'history-bindings.json').write_text(json.dumps(bindings,indent=2))
(L/'history-hits.json').write_text(json.dumps(hits,indent=2))
print('bound reports',len(bindings),'hits',len(hits))
for k in patterns:
 rows=[x for x in hits if x['family']==k];print(k,len(rows))
 for x in rows[:4]:print(x['path'],x['line'],x['text'][:230])
