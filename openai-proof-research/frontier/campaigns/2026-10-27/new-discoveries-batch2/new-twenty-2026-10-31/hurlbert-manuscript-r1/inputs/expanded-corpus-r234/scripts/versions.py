import pathlib,re,json,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[1];data=json.loads((D/'extracted.json').read_text())
for i,o in data.items():
 versions=re.findall(r'\[v([0-9]+)\]',(D/'sources'/f'{i}-abs.body').read_text())
 if len(versions)<2:continue
 for v in versions:
  name=f'{i}-v{v}';url=o['source_url'].replace('/abs/','/pdf/')+'v'+v
  subprocess.run([sys.executable,'-I','-B',str(D/'scripts/fetch.py'),name,url],check=True)
  if (D/'sources'/f'{name}.body').exists():subprocess.run(['pdftotext','-layout',str(D/'sources'/f'{name}.body'),str(D/'sources'/f'{name}.txt')])
