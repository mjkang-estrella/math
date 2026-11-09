import pathlib,json,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[1]
r=json.loads((D/'extracted.json').read_text()); seen=set()
for i,o in r.items():
 a=o['source_url'].split('/')[-1]
 if a in seen:continue
 seen.add(a)
 subprocess.run([sys.executable,'-I',str(D/'scripts/fetch.py'),a+'.html','https://arxiv.org/abs/'+a,a+'.pdf','https://arxiv.org/pdf/'+a],check=True)
