import pathlib,json,re
D=pathlib.Path(__file__).resolve().parents[1];t=[]
for owner,repo in [('Vilin97','lean-pool'),('the-omega-institute','trureturing')]:
 o=json.loads((D/'sources'/(owner+'-tree.json')).read_text());sha=json.loads((D/'sources'/(owner+'-head.json')).read_text())['sha']
 hits=[e['path'] for e in o['tree'] if re.search('projects.*json$|conjectures.*json$|registry.*json$|catalog.*json$',e['path'],re.I)]
 print(owner,hits[:20])
 for p in hits[:15]:t.append((owner+'-index-'+p.replace('/','_'),f'https://raw.githubusercontent.com/{owner}/{repo}/{sha}/'+p))
(D/'index-plan.json').write_text(json.dumps(t))
