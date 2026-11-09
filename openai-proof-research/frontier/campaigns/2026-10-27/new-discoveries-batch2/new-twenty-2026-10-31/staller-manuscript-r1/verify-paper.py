from pathlib import Path
import re,json
r=Path(__file__).resolve().parent;s=(r/'paper.tex').read_text();N=[{0,1,5},{0,1,2,6},{1,2,3},{2,3,4},{3,4,5},{0,4,5,6},{1,5,6}]
blocks=re.findall(r'\\begin\{longtable\}.*?\\end\{longtable\}',s,re.S);rows=[]
for line in blocks[0].splitlines():
 if re.match(r'^\d &',line):rows.append([v.strip() for v in line.removesuffix(r' \\').split('&')])
assert len(rows)==26;prefix={};cover={};nodes=set();leaves=0
for row in rows:
 h=[int(x) for x in row[:7] if x!='--'];v=int(row[7]);assert len(h)==len(set(h));S=set(h[::2]);D=set(h[1::2]);assert N[v]<=S and len(S)<=4
 for i,x in enumerate(h):
  p=tuple(h[:i]);nodes.add(p)
  if i%2==0:
   assert p not in prefix or prefix[p]==x;prefix[p]=x
  else:cover.setdefault(p,set()).add(x)
 nodes.add(tuple(h));leaves+=1
for p,choices in cover.items():assert choices==set(range(7))-set(p)
assert len(nodes)==70
count=0
for line in blocks[1].splitlines():
 if not re.match(r'^\d &',line):continue
 a,d,b,e,F,C=[v.strip() for v in line.removesuffix(r' \\').split('&')];a,d,b,e=map(int,[a,d,b,e]);assert len({a,d,b,e})==4
 free=set(map(int,F));assert free==set(range(7))-{a,d,b,e}
 actual={c for c in range(7) if c not in {a,b} and any(n<={a,b,c} for n in N)}
 assert actual==(set() if 'varnothing' in C else set(map(int,C)))
 for c in free:assert not any(n<={a,b,c} for n in N);count+=1
assert count==105
out={'paper_upper_nodes':len(nodes),'upper_leaves':leaves,'lower_completions':count,'all_pass':True};(r/'paper-table-verification.json').write_text(json.dumps(out,indent=2));print(out)
