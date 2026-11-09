from pathlib import Path
import json,subprocess,sys,time,urllib.parse
D=Path(__file__).resolve().parents[1];h=json.loads((D/'downloads/pool-head/body').read_text())['sha'];t=json.loads((D/'downloads/pool-tree/body').read_text())
args=[]
for x in t['tree']:
 p=x['path']
 if p.startswith('candidates/') or p=='LeanPool/projects.yml': args.append('pool-'+p.replace('/','-')+'|https://raw.githubusercontent.com/Vilin97/lean-pool/'+h+'/'+p)
for a in args:subprocess.run([sys.executable,'-I','-B',str(D/'scripts/fetch.py'),a],check=True)
for i,q in enumerate(['"local antimagic" lean','"1805.04888"','"Mobius ladder" lean','"339235" lean']):
 time.sleep(3)
 subprocess.run([sys.executable,'-I','-B',str(D/'scripts/fetch.py'),f'github-query-{i}|https://api.github.com/search/repositories?q='+urllib.parse.quote(q)],check=True)
