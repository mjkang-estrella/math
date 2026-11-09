import pathlib,json,subprocess,hashlib
D=pathlib.Path(__file__).resolve().parents[1]; B=D.parent.parent
r=json.loads((D/'extracted.json').read_text())
args=[]
for ar in sorted({x['source_url'].rsplit('/',1)[1] for x in r.values()}):args += ['abs-'+ar,'https://arxiv.org/abs/'+ar]
subprocess.run(['python3','-I','-B',str(D/'scripts/fetch.py'),*args],check=True)
for name in ['pool','omega','openai']:
 p=D/'sources'/f'{name}-head.body';o=json.loads(p.read_text());print(name,o['sha'])
 if name=='pool':subprocess.run(['python3','-I','-B',str(D/'scripts/fetch.py'),'pool-projects','https://raw.githubusercontent.com/Vilin97/lean-pool/'+o['sha']+'/projects.yml','pool-tree','https://api.github.com/repos/Vilin97/lean-pool/git/trees/'+o['sha']+'?recursive=1'],check=True)
for p in [D.parent/'ledger.json',B/'ledger.json',B/'prior-campaign-context.json']:
 o=json.loads(p.read_text());(D/'outputs'/('context-'+p.parent.name+'-'+p.name)).write_text(json.dumps(o,indent=2));print(p,hashlib.sha256(p.read_bytes()).hexdigest())
