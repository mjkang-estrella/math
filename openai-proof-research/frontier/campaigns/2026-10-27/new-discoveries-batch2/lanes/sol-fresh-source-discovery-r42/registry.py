import pathlib,json,subprocess,shutil,hashlib,datetime
P=pathlib.Path(__file__).resolve().parent
F=P/'fetch.py'
def fetch(name,url):subprocess.run(['python3',str(F),name,url],check=True)
repos={'omega':'the-omega-institute/trureturing','openai':'openai/math','aim':'MColbrook/AIM','count':'suvrit/count-ex-machina'}
# Count repository URL read from the earlier authentic HTTP log, not guessed.
old=P.parent/'sol-fresh-source-discovery-r41'
for line in (old/'http.jsonl').read_text().splitlines():
 row=json.loads(line)
 if 'count-head.json' in row.get('file',''):print('COUNT_URL',row.get('url'))
for key,repo in list(repos.items())[:3]:
 branch='dev' if key=='omega' else 'main'
 fetch(key+'-head.json',f'https://api.github.com/repos/{repo}/commits/{branch}')
fetch('omega-main.json','https://api.github.com/repos/the-omega-institute/trureturing/commits/main')
head=json.loads((P/'sources/omega-head.json').read_text())['sha']
fetch('omega-root.json',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{head}')
root=json.loads((P/'sources/omega-root.json').read_text())
for scope in ['D5','Problems']:
 sha=next(x['sha'] for x in root['tree'] if x['path']==scope)
 fetch('omega-'+scope+'.json',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{sha}?recursive=1')
fetch('omega-delta.json',f'https://api.github.com/repos/the-omega-institute/trureturing/compare/9518d571eb79b858755945ece5781939b971b01c...{head}')
