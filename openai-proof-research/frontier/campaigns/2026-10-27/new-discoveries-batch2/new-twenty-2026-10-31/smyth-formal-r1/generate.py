from pathlib import Path
G=[[13,12,8,4,2],[13,13,7,3,3],[12,12,8,6,1],[14,12,6,4,3],[13,11,7,7,1],[14,11,6,6,2],[15,11,5,5,3],[16,10,5,4,4]]
def ok(l):
 l=sorted(l,reverse=True)
 return any(all(sum(l[:j])<=sum(g[:j]) for j in range(6)) for g in G)
for label,b,a in [('S',19,20),('T',20,19)]:
 vals=[]
 for i in range(b+1):
  v=sum(ok([i,j,b-i-j,k,a-k]) for j in range(b-i+1) for k in range(a+1))
  vals.append(v)
  Path(f'src/{label}{i:02}.lean').write_text(f'import CountBase\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace Smyth1512\ntheorem count_{label}{i:02} : (row {b} {a} {i}).length = {v} := by decide\nend Smyth1512\n')
 print(label,vals,sum(vals))
