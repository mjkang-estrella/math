from pathlib import Path
p=Path(__file__).parent/'bent.py';s=p.read_text();a=s.index('walsh=[]');b=s.index('limit=min',a)
s=s[:a]+'''basis=[]
for a in [1<<i for i in range(n)]:
 z=0
 for x in range(N):
  if a&x:z|=1<<x
 basis.append(z)
walsh=[0]
for z in basis:walsh += [v^z for v in walsh]
'''+s[b:]
s=s.replace('for z in walsh):','for z in walsh[:32]):')
a=s.index(' for a in range(32,N):');b=s.index(' else:found',a)
s=s[:a]+''' for z in walsh[32:]:
  if abs(N-2*(tt^z).bit_count()) != 1<<(n//2):break
'''+s[b:]
s=s.replace(' g=m^(m>>1)',' if m and m%1000000==0:print(json.dumps({"completed":m}),flush=True)\n g=m^(m>>1)')
p.write_text(s)
