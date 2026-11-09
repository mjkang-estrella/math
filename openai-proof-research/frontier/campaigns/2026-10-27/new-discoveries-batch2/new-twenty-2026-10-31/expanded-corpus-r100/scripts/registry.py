from pathlib import Path
import json,hashlib,re
D=Path.cwd();C=D.parent
pats=[str(x) for x in json.load(open('reservation.json'))['ids']]+['bruhat','shuffle','flaghilbert','betacycle','blockgraph','colouredcycle','pcn','repetition','reedmuller','triangularratio']
out={'live_heads':{},'limitation':'Only commits/HEAD requested live, as instructed. Cached older complete trees are path screens, not current proof-body clearance. No current global novelty claim.','cached_screens':[]}
for name in ['omega','openai']:
 p=D/'sources'/f'{name}-head.json';x=json.loads(p.read_bytes());out['live_heads'][name]={'sha':x['sha'],'utc':x['commit']['committer']['date'],'receipt':f'sources/{name}-head.json.receipt.json','changed_files_matches':[a['filename'] for a in x.get('files',[]) if any(s in re.sub('[^a-z0-9]','',a['filename'].lower()) for s in pats)]}
for p in list((C/'xor-magic-parent-final-r1/registries').glob('omega-*.body'))+[C/'fresh-corpus-r10/sources/registry-preprints.json']:
 try:x=json.loads(p.read_bytes())
 except:continue
 entries=x.get('tree',[]) if isinstance(x,dict) else x
 paths=[a.get('path','') for a in entries if isinstance(a,dict)]
 out['cached_screens'].append({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'truncated':x.get('truncated') if isinstance(x,dict) else None,'matches':[a for a in paths if any(s in re.sub('[^a-z0-9]','',a.lower()) for s in pats)]})
Path('outputs/registry-screen.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2)[:6000])
