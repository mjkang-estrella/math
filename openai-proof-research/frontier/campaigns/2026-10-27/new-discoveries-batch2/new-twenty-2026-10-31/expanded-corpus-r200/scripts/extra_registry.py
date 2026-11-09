import pathlib,json,re,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[1];out=[];urls=[]
for p in (D/'sources').glob('*/receipt.json'):
 r=json.loads(p.read_text())
 if '/git/trees/' in r['url'] and 'lean-pool' not in r['url'] and r.get('status')==200:
  t=json.loads((p.parent/'body').read_text());paths=[x['path'] for x in t['tree']];o={'url':r['url'],'receipt':str(p.relative_to(D)),'sha':t['sha'],'truncated':t.get('truncated'),'paths_count':len(paths),'matches':[x for x in paths if re.search('Erde|Matsui|Yamanouchi|Stasinski|Romik|Lapointe|Kotlar|Nishiyama|Trotter|Plaid|inv-maj|hook.length|hexagonal|Deligne.Simpson',x,re.I)]};out.append(o)
  if 'trureturing' in r['url']:
   for x in t['tree']:
    if x['path'] in ['D5','Problems'] and x['type']=='tree':urls.append('https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'+x['sha']+'?recursive=1')
(D/'outputs/other-registry-screen.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2));subprocess.run([sys.executable,'-I',str(D/'scripts/fetch.py'),*urls],check=True)
