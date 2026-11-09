import pathlib,json
L=pathlib.Path(__file__).resolve().parents[1];h=json.loads((L/'http/pool-head/body').read_text())['sha']; t=json.loads((L/'http/pool-tree/body').read_text());q=[]
for x in t['tree']:
 if x['type']=='blob' and (x['path'].startswith('candidates/') or x['path'] in ['README.md','projects.yml']):q.append(('poolraw-'+x['path'].replace('/','--'),'https://raw.githubusercontent.com/Vilin97/lean-pool/'+h+'/'+x['path']))
(L/'poolqueue.json').write_text(json.dumps(q));print(len(q));print([a[0] for a in q])
