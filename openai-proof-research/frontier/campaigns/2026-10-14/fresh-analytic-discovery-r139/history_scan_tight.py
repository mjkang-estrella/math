from pathlib import Path
import os,re,json,hashlib
R=Path(__file__).resolve().parent;P=R.parents[3]
peer=re.compile(r'arithmetic.*r(?:111|110|109|108|107)(?!\d)|analytic.*r(?:139|138|137|136|135)(?!\d)|structural.*r(?:145|144|143)(?!\d)|h138-|t185r144-|t177c143-|t373e135-|k369r134-|t088p133-',re.I)
roles=re.compile(r'corpus|source|primary|history|search|inventory|fixture|control|extract|render|vendor|build|cop(?:y|ies|ied)|frozen|role|formal|manuscript|release|parent|private|payload|packet|public|submission|intake|brief|task|review|audit|manifest|receipt|ledger|snapshot|archive|cache|input|pinned|context|metadata|authenticat|provenance|diagnostic|verify|retrieve|prepare|fetch|read\.py|progress|status|identities|evidence|tmp|work|output|node_modules|\.git|\.venv',re.I)
needle=re.compile(r'Brenier|Letrouit|Source\s*374|I374|one.third.stability|Laguerre|transport.map|map.stability|semi.discrete.transport',re.I)
roots=['proposals','findings','experiments','notes','scouts','iterations','frontier/campaigns','frontier/iterations','frontier/experiments','frontier/proposals','frontier/scouts','frontier/notes','frontier/findings']
record={'roots':roots,'peer_pattern':peer.pattern,'role_pattern':roles.pattern,'needle':needle.pattern,'pruned_count':0,'binary_skips':0,'errors':[],'admitted':[],'hits':[]}
seen=set()
def walk(d):
 if not d.exists():return
 for e in os.scandir(d):
  if peer.search(e.name) or roles.search(e.name):record['pruned_count']+=1;continue
  if e.is_symlink():record['pruned_count']+=1;continue
  p=Path(e.path)
  # Avoid unknown recent running discoveries, even absent known peer alias.
  m=re.search(r'(?:discovery|analytic|arithmetic|structural).*r(\d+)',e.name,re.I)
  if m and int(m.group(1))>=130:record['pruned_count']+=1;continue
  if e.is_dir(follow_symlinks=False):walk(p);continue
  rel=str(p.relative_to(P))
  if rel in seen:continue
  seen.add(rel)
  try:
   b=p.read_bytes()
   if b'\0' in b:record['binary_skips']+=1;continue
   s=b.decode('utf8')
  except UnicodeError:record['binary_skips']+=1;continue
  except OSError as exc:record['errors'].append([rel,str(exc)]);continue
  record['admitted'].append({'path':rel,'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
  hits=[{'line':i,'text':l} for i,l in enumerate(s.splitlines(),1) if needle.search(l)]
  if hits:record['hits'].append({'path':rel,'hits':hits})
for root in roots:walk(P/root)
out=R/'private/history-search-tight.json'
assert not out.exists();out.write_text(json.dumps(record,indent=2)+'\n')
print('read',len(record['admitted']),'hit files',len(record['hits']),'pruned',record['pruned_count'],'binary',record['binary_skips'],'errors',len(record['errors']))
for h in record['hits']:print(h['path'])

# Prospective same-turn r111 steer added after this scanner was run; historical JSON pattern/records are preserved.
