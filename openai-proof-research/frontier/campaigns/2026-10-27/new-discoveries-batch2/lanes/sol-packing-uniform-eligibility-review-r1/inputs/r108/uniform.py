exec((__import__('pathlib').Path(__file__).parent/'check.py').read_text().split('# Exact source model')[0])
rows=[]
for m in range(3,7):
 for K in range(2*m+1,2*m+5):
  pi=tuple(range(1,m))+(K-1,)+tuple(range(m+1,K-m))+(K,m)+tuple(range(K-m,K-1))
  seq=[];want=1
  for j in range(1,10):
   want*=2*j-1
   try:z=count(pi,m,j)
   except RuntimeError as e:rows.append({'m':m,'K':K,'cap':str(e),'j':j});break
   seq.append(z)
   if z!=want:
    rows.append({'m':m,'K':K,'pi':pi,'j':j,'actual':z,'double_factorial':want,'seq':seq});break
  else:rows.append({'m':m,'K':K,'pi':pi,'match_through':9,'seq':seq})
print(json.dumps(rows,indent=2));(L/'uniform-results.json').write_text(json.dumps(rows,indent=2))
