import pathlib,json,hashlib,re
W=pathlib.Path(__file__).resolve().parent
b=[]
for p in sorted((W/'sources').glob('*')):b.append({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'size':p.stat().st_size})
(W/'source-bindings.json').write_text(json.dumps(b,indent=2)+'\n')
for batch in range(3):
 out=[]
 for p in sorted((W/'sources').glob('*.txt'))[batch*15:(batch+1)*15]:
  lines=p.read_text().splitlines();sel=set()
  for i,s in enumerate(lines):
   if re.search(r'conjectur|question|problem|theorem 1\.|theorem 2\.|theorem 3\.',s,re.I):
    if re.search(r'\[\d+\]|references',s,re.I):continue
    sel.update(range(max(0,i-2),min(len(lines),i+11)))
  out.append('\n### '+p.name+'\n'+'\n'.join(str(i+1)+': '+lines[i] for i in sorted(sel))[:21000])
 (W/('passages-'+str(batch)+'.txt')).write_text('\n'.join(out))
