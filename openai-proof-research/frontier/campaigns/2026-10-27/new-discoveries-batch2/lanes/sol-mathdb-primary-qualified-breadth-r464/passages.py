import pathlib,json,re,hashlib
L=pathlib.Path(__file__).resolve().parent; out=[]
for s in json.loads((L/'sources.json').read_text()):
 if 'text_path' not in s: continue
 p=pathlib.Path(s['text_path']); assert hashlib.sha256(p.read_bytes()).hexdigest()==s['text_sha256']; lines=p.read_text().splitlines(); hits=[i for i,t in enumerate(lines) if re.search(r'conjecture|question|problem|theorem 1',t,re.I)]
 # Locators are NOT claims of reading. Keep contextual extracts separately for manual reading.
 ix=set(range(min(28,len(lines))))
 for i in hits[:5]: ix.update(range(max(0,i-3),min(len(lines),i+11)))
 entry={'ids':s['ids'],'url':s['url'],'path':str(p),'ranges':sorted(ix)};out.append(entry)
 with (L/('passage-'+str(s['ids'][0])+'.txt')).open('w') as f:
  f.write(str(s['ids'])+' '+s['url']+'\n')
  for i in sorted(ix):f.write(f'{i+1}: {lines[i]}\n')
(L/'passage-locators.json').write_text(json.dumps(out,indent=2)+'\n')
