import pathlib,json,sys,re
D=pathlib.Path(sys.argv[1]);tree=None;projects=None
for r in (D/'downloads').glob('*/receipt.json'):
 a=json.loads(r.read_text());u=a['url']
 if 'git/trees/' in u:tree=json.loads((r.parent/'body').read_text())
 if u.endswith('projects.yml'):projects=(r.parent/'body').read_text()
assert tree and not tree['truncated']
paths=[x['path'] for x in tree['tree'] if x['path'].startswith('candidates/') and x['type']=='blob']
urls=['https://raw.githubusercontent.com/Vilin97/lean-pool/01db1d7049cf9668bda1e9e106875ee1278b43e6/'+x for x in paths]
(D/'outputs/registry-urls.txt').write_text('\n'.join(urls)+'\n')
pattern=r'divine|345754|340618|projective cube|long.wagner|samotij|grytczuk'
hits=[]
for r in (D/'downloads').glob('*/receipt.json'):
 a=json.loads(r.read_text())
 if 'raw.githubusercontent.com/Vilin97/lean-pool' not in a['url'] or a.get('status')!=200:continue
 for i,line in enumerate((r.parent/'body').read_text().splitlines(),1):
  if re.search(pattern,line,re.I):hits.append(dict(url=a['url'],line=i,text=line))
(D/'outputs/registry-screen.json').write_text(json.dumps(dict(head='01db1d7049cf9668bda1e9e106875ee1278b43e6',candidate_paths=paths,hits=hits,limit='bounded literal topic and identifier search; not semantic proof clearance'),indent=2))
print('candidate files',len(paths),'hits',len(hits))
