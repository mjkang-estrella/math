from research import *
o=json.loads((HERE/'omega-head.json').read_text());a=json.loads((HERE/'openai-head.json').read_text())
save('registry-heads.json',{'utc':utc(),'omega':o['sha'],'openai':a['sha'],'inherited_omega':'a7769c386bd6072628a21cf4680756d2a49bf221','omega_commit_date':o['commit']['committer']['date'],'scope':'single bounded refresh; not semantic clearance'})
print(o['sha'],a['sha'])
if o['sha']!='a7769c386bd6072628a21cf4680756d2a49bf221':fetch('https://api.github.com/repos/the-omega-institute/trureturing/compare/a7769c386bd6072628a21cf4680756d2a49bf221...'+o['sha'],'omega-delta.json')
