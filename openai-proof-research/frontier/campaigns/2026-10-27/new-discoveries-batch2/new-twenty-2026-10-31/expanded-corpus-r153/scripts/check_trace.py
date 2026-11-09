import pathlib,json,itertools
L=pathlib.Path(__file__).resolve().parents[1];exec((L/'scripts/delta.py').read_text().split('out=[]')[0]);r=json.loads((L/'outputs/delta-trace.json').read_text());A=r['original']
def valid(A):return all(len(row)==len(A) and sum(row)==6 and row[i]==0 and all(row[j]==A[j][i] for j in range(len(A))) for i,row in enumerate(A))
assert valid(A)
for x in r['pure_reduction_sequence']:
 assert x in wyes(A);A=red(A,x);assert valid(A)
assert A==r['Gprime'];states=[A];ops=[]
for op,arg in r['operations']:
 if op=='expand':assert tuple(arg) in tris(A);A=exp(A,arg)
 else:assert arg in wyes(A);A=red(A,arg)
 assert valid(A)
 if A in states:
  j=states.index(A);states=states[:j+1];ops=ops[:j]
 else:states.append(A);ops.append([op,arg])
assert A==r['result'];r['loop_erased_operations']=ops
B=r['Gprime'];ends=[i for i,row in enumerate(B) if sorted(v for v in row if v)==[1,1,2,2]];mid=[i for i,row in enumerate(B) if sorted(v for v in row if v)==[1,1,1,1,2]]
allowed=[(i,j,k) for i,j in itertools.combinations(ends+mid,2) for k in range(len(B)) if k not in(i,j) and B[i][j]==B[i][k]==B[j][k]==1]
r['chain_endpoints']=ends;r['chain_interiors']=mid;r['eligible_triangle_transitions']=allowed
(L/'outputs/delta-trace-checked.json').write_text(json.dumps(r,indent=2));print('validated all matrices 6-regular loopless symmetric; pure reductions',r['pure_reduction_sequence'],'loop-erased moves',len(ops),'endpoints',ends,'interiors',mid,'allowed triangles',allowed);print(ops)
