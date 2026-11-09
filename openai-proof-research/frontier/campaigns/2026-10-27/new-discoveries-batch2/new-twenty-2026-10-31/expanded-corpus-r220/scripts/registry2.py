import sys,pathlib,json,re
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from fetch import fetch,L
h=json.loads((L/'receipts/leanpool-head.body').read_text())['sha'];t=json.loads((L/'receipts/leanpool-tree.body').read_text())
ps=[x['path'] for x in t['tree'] if x['path'].endswith('projects.yml') or x['path'].startswith('candidates/')]
print('HEAD',h,'truncated',t.get('truncated'),'candidate paths',len(ps));print('\n'.join(ps[:20]))
for i,p in enumerate(ps):
 if p.endswith('projects.yml') or (p.startswith('candidates/') and p.endswith(('.md','.yml','.yaml','.json'))):fetch(f'https://raw.githubusercontent.com/Vilin97/lean-pool/{h}/{p}',f'pool-file-{i}')
(L/'outputs/registry-paths.json').write_text(json.dumps(ps,indent=2))
