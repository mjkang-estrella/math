import pathlib,json,re,hashlib
D=pathlib.Path(__file__).resolve().parents[1];res=json.loads((D/'reservation.json').read_text());terms=[str(x) for x in res['ids']]+[r['source_url'].split('/')[-1] for r in res['rows']]+['Kotlar','Erde','Matsui','Yamanouchi','Romik','Lapointe','Pinto','hyperoctahedral','Pegden','Nishiyama','Trotter','Nasser','Stasinski','Faben','plaid']
out={'utc':'2026-11-05','scope':'Lean Pool projects and all candidates files; path/content screen, not full proof audit','terms':terms,'github':[],'pool_files':[],'hits':[]}
for p in sorted((D/'sources').glob('*/receipt.json')):
 r=json.loads(p.read_text());url=r['url']
 if 'lean-pool/commits/HEAD' in url:out['lean_pool_HEAD']=json.loads((p.parent/'body').read_text())['sha']
 if 'search/repositories' in url:
  b=json.loads((p.parent/'body').read_text());out['github'].append({'query_url':url,'receipt':str(p.relative_to(D)),'status':r.get('status'),'total_count':b.get('total_count'),'hits':[x['full_name'] for x in b.get('items',[])]})
 if 'raw.githubusercontent.com/Vilin97/lean-pool/' in url and r.get('status')==200:
  s=(p.parent/'body').read_text();out['pool_files'].append({'url':url,'receipt':str(p.relative_to(D)),'sha256':r['sha256']})
  for line in s.splitlines():
   hits=[x for x in terms if re.search(r'(?<!\w)'+re.escape(x)+r'(?!\w)',line,re.I)]
   if hits:out['hits'].append({'url':url,'terms':hits,'line':line})
(D/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2));print(json.dumps(out['hits'],indent=2));print('queries',len(out['github']))
