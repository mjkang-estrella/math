import pathlib,json,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[1]
for p in (D/'sources').glob('*/receipt.json'):
 r=json.loads(p.read_text())
 if 'lean-pool/git/trees/' in r['url']:
  tree=json.loads((p.parent/'body').read_text());head=tree['sha'];paths=[x['path'] for x in tree['tree'] if x['type']=='blob' and (x['path'].startswith('candidates/') or x['path'].endswith('projects.yml'))];print(paths)
  (D/'outputs/pool-paths.json').write_text(json.dumps(paths));urls=[f'https://raw.githubusercontent.com/Vilin97/lean-pool/{head}/{x}' for x in paths]
  subprocess.run([sys.executable,'-I',str(D/'scripts/fetch.py'),*urls],check=True)
