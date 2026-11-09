from pathlib import Path
import re,json,collections,itertools,hashlib
L=Path(__file__).parent;E=L/'extracted';s=(E/'IndependentAudit.log').read_text()
rows=[];counts=collections.Counter();allaxioms=set()
for block in re.split(r'(?m)^DECL\|',s)[1:]:
 header=block.splitlines()[0].split('|');name,_,origin,_,unsafe=header
 assert unsafe=='false'
 safety=re.search(r'(?m)^SAFETY\|'+re.escape(name)+r'\|([^\n]+)',block)[1]
 assert safety in ('nondefinition','Lean.DefinitionSafety.safe')
 match=re.search("'"+re.escape(name)+r"' (does not depend on any axioms|depends on axioms: \[([^\]]*)\])",block);assert match,name
 axioms=[] if match[2] is None else [re.sub(r'\.\{[^}]*\}','',v.strip()) for v in match[2].split(',')]
 assert set(axioms)<= {'propext','Classical.choice','Quot.sound'}
 assert re.search(r'(?m)^'+re.escape(name)+r'(?: |\.|\n|\{|\()',block)
 rows.append(dict(name=name,origin=origin,safety=safety,axioms=axioms));counts[origin]+=1;allaxioms.update(axioms)
assert len({r['name'] for r in rows})==120
assert dict(counts)==dict(Closure=30,Words=28,Geometry=5,Attractor=50,Endpoint=7)
guards={}
for mod in ['Closure','Words','Geometry','Attractor','Endpoint','IndependentAudit']:
 r=json.loads((E/(mod+'.guard.json')).read_text());assert r['exit_code']==0 and r['reason'] is None;guards[mod]=r
for mod in counts:
 assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|partial)\b',(E/(mod+'.lean')).read_text())
result=dict(status='PASS',count=len(rows),origins=dict(counts),axioms=sorted(allaxioms),declarations=rows,guards=guards)
(L/'independent-audit.json').write_text(json.dumps(result,indent=2)+'\n')
# Separate finite corroboration; no worker checker or receipt is imported.
theta=lambda e,s: ''.join(str(1-int(x)) for x in s[::-1]) if e else s[::-1]
s='';steps=[]
for letter,e in zip('00101',[1,1,1,1,0]):
 u=s+letter;k=next(k for k in range(len(u)+1) if theta(e,u+theta(e,u[:k]))==u+theta(e,u[:k]))
 s=u+theta(e,u[:k]);steps.append(dict(word=s,added=k,suffix=len(u)-k))
assert s=='010110010101100101101001101010011010'
factors=['001010','010101','101011','001011','101101','110100','110101','101010','010100','1100','0011']
starts=[[i for i in range(len(s)+1) if i+len(f)<=len(s) and s[i:i+len(f)]==f] for f in factors]
assert starts==[[5],[6],[7],[13],[15],[17],[23],[24],[25],[3,11],[21,29]],starts
cover=[{p for i in ii for p in range(i,i+len(f))} for f,ii in zip(factors,starts)]
survivors=sum(all(set(g)&c for c in cover) for g in itertools.combinations(range(36),4));assert survivors==0
(L/'finite-corroboration.json').write_text(json.dumps(dict(steps=steps,occurrences=dict(zip(factors,starts)),four_subsets=58905,survivors=survivors,role='corroboration; not a Lean premise'),indent=2)+'\n')
print(json.dumps(dict(status='PASS',origins=dict(counts),axioms=sorted(allaxioms),finite_survivors=survivors)))
