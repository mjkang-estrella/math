exec(open(__file__.replace('body_read.py','read.py')).read().split("for n in")[0])
for n in ['finite-original']:
 f=P/('sources/'+n+'.html');s=plain(f.read_text());(P/('sources/'+n+'.txt')).write_text(s)
 for term in ['Conjecture','Theorem 1.','Theorem 2.','1.1']:
  start=0
  for k in range(8):
   i=s.find(term,start)
   if i<0:break
   print(n,s[max(0,i-100):i+1500]);start=i+len(term)
r=json.loads((P/'registry-screen.json').read_text()) if False else None
