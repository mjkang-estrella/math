from pathlib import Path
import os,re,json,hashlib
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research'); R=P/'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r140'
peer=re.compile(r'arithmetic.*r(?:112|111|110|109|108|107)(?!\d)|structural.*r(?:146|145|144|143)(?!\d)|analytic.*r(?:140|139|138|137|136|135)(?!\d)|h138-|t185r144-|t177c143-|t373e135-|k369r134-|t088p133-',re.I)
role=re.compile(r'corpus|source|primary|history.derivative|search|inventory|fixture|control|extract|render|vendor|build|cop(?:y|ies|ied)|frozen|role|formal|manuscript|release|parent|input|snapshot|context|pinned|archive|brief|intake|review|assess|disposition|contribution|task|prompt|catalog|survey|ledger|manifest|reading|limits|isolation|provenance|seal|verif|\.git|node_modules|\.cache',re.I)
needle=re.compile(r'Schr[oö]dinger|Carleson.*convergence|endpoint.*convergence|local smoothing|variation.norm|variational.*maximal',re.I)
result={'filters':{'peer':peer.pattern,'role':role.pattern,'needle':needle.pattern},'reads':0,'binary':0,'errors':[],'pruned':[],'hits':[]}
for root in ['frontier/campaigns','frontier/iterations','frontier/experiments','frontier/proposals','frontier/scouts','frontier/notes','frontier/findings']:
 start=P/root
 if not start.exists(): continue
 for current,ds,fs in os.walk(start,followlinks=False):
  ds[:]=sorted(d for d in ds if not (peer.search(d) or role.search(d) or (Path(current)/d).is_symlink()))
  for n in sorted(fs):
   if peer.search(n) or role.search(n): continue
   f=Path(current)/n
   if f.is_symlink():continue
   try:
    b=f.read_bytes()
    if b'\0' in b:result['binary']+=1;continue
    s=b.decode('utf8')
   except UnicodeDecodeError:result['binary']+=1;continue
   except OSError as e:result['errors'].append([str(f),str(e)]);continue
   result['reads']+=1
   hits=[{'line':i+1,'text':l[:1200]} for i,l in enumerate(s.splitlines()) if needle.search(l)]
   if hits:result['hits'].append({'path':str(f.relative_to(P)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'hits':hits})
(R/'private/history-search.json').write_text(json.dumps(result,indent=2))
print(json.dumps({'reads':result['reads'],'binary':result['binary'],'errors':result['errors'],'hits':[{'path':x['path'],'lines':[h['line'] for h in x['hits']]} for x in result['hits']]},indent=2))
