import pathlib,json,subprocess
D=pathlib.Path(__file__).resolve().parents[1]
x=json.loads((D/'extracted.json').read_text())
for i,v in x.items():
 subprocess.run(['python3','-I',str(D/'scripts/fetch.py'),i+'-abs',v['source_url']],check=True)
subprocess.run(['python3','-I',str(D/'scripts/fetch.py'),'pool-head','https://api.github.com/repos/Vilin97/lean-pool/commits/HEAD','omega-head','https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD','openai-head','https://api.github.com/repos/openai/math/commits/HEAD'],check=True)
