import pathlib,json,hashlib,re,subprocess
L=pathlib.Path(__file__).resolve().parents[1]
for p in (L/'receipts').glob('http-*.json'):
 r=json.loads(p.read_text());b=L/r.get('body','missing')
 if b.is_file() and b.read_bytes().startswith(b'%PDF'):
  out=b.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(b),str(out)],check=True)
  print(p.name,r['url'],'->',out.name)
 if r['url'].startswith('https://arxiv.org/abs/') and b.is_file():
  s=b.read_text();print(r['url'],'versions',sorted(set(re.findall(r'v[0-9]+',s))))
# registry path screen, complete lean-pool tree
r=json.loads((L/'sources/http-0004.bin').read_bytes()); paths=[x['path'] for x in r['tree']];print('pool truncated',r.get('truncated'),len(paths))
terms=['welter','biplane','rado','young','homomes','interval','precolor','precolour','jockusch','cranston','kempe','keevash','frankl','wreath','tutaj','hopper']
for x in paths:
 if any(t in x.lower() for t in terms) or x.endswith('projects.yml'):print(x)
(L/'logs/lean-pool-path-screen.json').write_text(json.dumps({'truncated':r.get('truncated'),'terms':terms,'hits':[x for x in paths if any(t in x.lower() for t in terms)],'projects':[x for x in paths if x.endswith('projects.yml')],'candidates':[x for x in paths if x.startswith('candidates/')]} ,indent=2))
