import pathlib,json,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[1]
for i,o in json.loads((D/'extracted.json').read_text()).items():
 a=o['source_url'].rsplit('/',1)[-1];args=[]
 for typ,url in [('abs',o['source_url']),('pdf','https://arxiv.org/pdf/'+a)]:
  if not (D/'sources'/f'{i}-{typ}.receipt.json').exists():args.extend([f'{i}-{typ}',url])
 if args:subprocess.run([sys.executable,'-I','-B',str(D/'scripts/fetch.py'),*args],check=True)
 if (D/'sources'/f'{i}-pdf.body').exists():subprocess.run(['pdftotext','-layout',str(D/'sources'/f'{i}-pdf.body'),str(D/'sources'/f'{i}.txt')])
