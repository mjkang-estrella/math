from pathlib import Path
import json,re,hashlib,itertools
B=Path(__file__).resolve().parent;R=B/'replay';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
text=(R/'IndependentAudit.log').read_text();blocks=re.split(r'(?m)^DECL\|',text)[1:];rows=[]
for b in blocks:
 header,body=b.split('\n',1);name,_,origin,_,unsafe=header.split('|')
 assert unsafe=='false' and origin in ['Definitions','Witness']
 safety=re.search(r'^SAFETY\|'+re.escape(name)+r'\|(.+)$',body,re.M).group(1)
 assert safety in ['nondefinition','Lean.DefinitionSafety.safe']
 ax=re.search("'"+re.escape(name)+r"' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",body)
 assert ax,(name,body)
 axioms=[] if ax.group(2) is None else [re.sub(r'\.\{.*?\}','',a.strip()) for a in ax.group(2).split(',')]
 assert set(axioms)<= {'propext','Classical.choice','Quot.sound'}
 typ=body.split('\n',1)[1].split("'"+name+"'")[0].strip();assert typ.startswith(name)
 rows.append(dict(name=name,origin=origin,unsafe=False,partial=False,safety=safety,type=typ,transitive_axioms=axioms))
assert len(rows)==len({r['name'] for r in rows})==71
assert 'error:' not in text and 'warning:' not in text
for n in ['Definitions','Witness']:
 assert sha(R/(n+'.lean'))==sha(B/'extracted'/(n+'.lean'))==sha(B.parent/'sol-das-ap-irreducible-source-formal-r1'/(n+'.lean'))
 assert json.loads((R/(n+'.guard.json')).read_text())['exit_code']==0
 assert not (R/(n+'.log')).read_text()
 assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|partial|implemented_by|extern)\b',(R/(n+'.lean')).read_text())
(B/'declaration-inventory.json').write_text(json.dumps(rows,indent=2))
# Independent finite check uses all outgoing subsets, no imported worker code.
A=[[0,1,0,0,1],[1,0,0,0,-1],[0,0,0,1,0],[0,0,1,0,-1],[0,-1,1,-1,0]]
def ap(a):
 b=[[int(a[i][j]==1)+int(a[j][i]==-1) for j in range(5)] for i in range(5)]
 def cut(m):return all(any(m[i][j]!=0 for i in range(5) if mask>>i&1 for j in range(5) if not mask>>j&1) for mask in range(1,31))
 return [cut(a),all(1 in row for row in a),all(any(a[i][j]==1 for i in range(5)) for j in range(5)),cut(b)]
assert all(ap(A));deletions=[]
for i,j in itertools.product(range(5),repeat=2):
 if A[i][j]:
  a=[r[:] for r in A];a[i][j]=0;flags=ap(a);assert not all(flags)
  deletions.append(dict(cell_zero_based=[i,j],sign=A[i][j],conditions_after_deletion=flags))
assert len(deletions)==10 and all(A[i][i]==0 for i in range(5))
(B/'math-check.json').write_text(json.dumps(dict(matrix=A,AP=ap(A),count=10,bound=8,deletions=deletions),indent=2))
print(json.dumps(dict(declarations=len(rows),origins={n:sum(r['origin']==n for r in rows) for n in ['Definitions','Witness']},unsafe=0,partial=0,axioms=sorted(set(a for r in rows for a in r['transitive_axioms'])),all_deletions=len(deletions)),indent=2))
