import pathlib
D=pathlib.Path(__file__).resolve().parents[1];p=D/'scripts/totient-lazy.py';s=p.read_text()
a=s.index(' choices=[]');b=s.index('\ndef graph(k):',a)
s=s[:a]+'''
 def assign(j,used):
  if j==len(shape):return {str(m):list(used)}
  t=shape[j]
  for x in candidates:
   if x in used or (t and x%2):continue
   w=embed(x,t)
   if w is None:continue
   rest=assign(j+1,used+(x,))
   if rest is not None:
    rest.update(w);return rest
  return None
 return assign(0,())
'''+s[b:]
s=s.replace("'outputs/totient.json'","'outputs/totient-lazy.json'")
p.write_text(s)
