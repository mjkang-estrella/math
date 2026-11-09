import pathlib,json,re,hashlib
L=pathlib.Path(__file__).resolve().parent; out=[]
for p in sorted((L/'sources').glob('*.txt')):
 b=p.read_bytes(); h=hashlib.sha256(b).hexdigest(); s=b.decode(); ls=s.splitlines(); hits=[i for i,v in enumerate(ls) if re.search(r'Conjecture\s+\d|conjecture is|conjecture was|disprove|proved by|Problem\s+\d',v,re.I)]
 spans=[]
 for i in hits[:14]:
  a=max(0,i-2); z=min(len(ls),i+11)
  if spans and a<=spans[-1][1]:spans[-1][1]=z
  else:spans.append([a,z])
 out.append({'file':str(p.relative_to(L)),'text_sha256_before_read':h,'version_marks':re.findall(r'arXiv:\S+',s)[:2],'spans':spans})
 print('\nSOURCE',p.name,'VERSION',out[-1]['version_marks'])
 for a,z in spans:print('\n'.join(str(k+1)+': '+ls[k] for k in range(a,z)))
(L/'passage-locators.json').write_text(json.dumps(out,indent=2)+'\n')
