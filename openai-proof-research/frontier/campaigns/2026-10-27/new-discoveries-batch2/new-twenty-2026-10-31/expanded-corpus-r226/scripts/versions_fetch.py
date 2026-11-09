from pathlib import Path
import re,json,subprocess,sys
L=Path(__file__).resolve().parents[1]; urls=[]
for p in sorted((L/'receipts').glob('*.json')):
 try:r=json.loads(p.read_text());u=r['url']
 except (KeyError,TypeError):continue
 if '/abs/240' not in u:continue
 aid=u.split('/')[-1];t=(L/'inputs'/(Path(r['body']).stem+'.txt')).read_text();a=t.find('Submission history');vs=re.findall(r'\[v(\d+)\]',t[a:]);
 for v in vs:urls.append(f'https://arxiv.org/html/{aid}v{v}')
existing={json.loads(p.read_text()).get('url') for p in (L/'receipts').glob('*.json') if p.name.startswith('2026')}
subprocess.run([sys.executable,'-I','-B',str(L/'scripts/fetch.py')]+[u for u in dict.fromkeys(urls) if u not in existing],check=True)
