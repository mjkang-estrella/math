from intake import *
if fetch('https://math.ac.vn/uploads/files/IMH20210803.pdf','gorenstein-prior.pdf')==200:subprocess.run(['pdftotext','-layout',str(L/'sources/gorenstein-prior.pdf'),str(L/'sources/gorenstein-prior.txt')])
d=json.loads((L/'sources/registry-omega-head.json').read_text());tree=d['commit']['tree']['sha']
if fetch('https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'+tree,'registry-omega-root.json')==200:
 root=json.loads((L/'sources/registry-omega-root.json').read_text())
 for x in root['tree']:
  if x['path'] in ['D5','Problems']:
   fetch('https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'+x['sha']+'?recursive=1','registry-omega-'+x['path']+'.json')
