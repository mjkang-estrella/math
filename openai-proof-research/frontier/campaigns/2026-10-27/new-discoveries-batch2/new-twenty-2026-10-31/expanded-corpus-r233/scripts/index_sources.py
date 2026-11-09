import pathlib,json,re,subprocess
P=pathlib.Path(__file__).resolve().parents[1]; rows=[]
patterns=r'paley|zircon|laplacian|circle|nucleus|sandpile|lieb|dacey|hessenberg|linked|rigid|thompson|derangement|cycle.?double|jacobian|m.property|reality.*tree|hibi'
for f in sorted((P/'receipts').glob('http-*.json')):
 r=json.loads(f.read_text())
 if r.get('status')!=200 or not r.get('body'):continue
 b=(P/r['body']).read_bytes()
 if '/abs/' in r['url']:
  s=b.decode();versions=sorted(set(re.findall(r'\[v(\d+)\]',s)))
  if not versions:versions=sorted(set(re.findall(r'arXiv:[0-9.]+v(\d+)',s)))
  rows.append({'url':r['url'],'receipt':str(f.relative_to(P)),'versions':versions,'title':re.findall(r'<title>(.*?)</title>',s),'abstract':re.findall(r'<blockquote class="abstract mathjax">(.*?)</blockquote>',s,re.S)})
 elif '/git/trees/' in r['url']:
  d=json.loads(b); paths=[x['path'] for x in d.get('tree',[]) if re.search(patterns,x['path'],re.I)]
  print(r['url'],'sha',d.get('sha'),'truncated',d.get('truncated'),'hits',len(paths));print('\n'.join(paths)[:12000])
 if b.startswith(b'%PDF'):
  out=P/'sources'/(f.stem+'.txt')
  if not out.exists():subprocess.run(['pdftotext','-layout',str(P/r['body']),str(out)],check=True)
(P/'inputs/source-index.json').write_text(json.dumps(rows,indent=2))
print('\nVersion histories:')
for r in rows:print(r['url'],r['versions'])
