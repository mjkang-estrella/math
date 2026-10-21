from pathlib import Path
import re,json,hashlib,os
ROOT=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
OUT=ROOT/'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r141'
active=re.compile(r'(arithmetic.*r(?:112|113)|structural.*r(?:146|147))',re.I)
recent=re.compile(r'(analytic.*r(?:140|139|138|137|136|135)|arithmetic.*r(?:111|110|109|108|107)|structural.*r(?:145|144|143)|h138-|t185r144-|t177c143-|t373e135-|k369r134-|t088p133-)',re.I)
roles=re.compile(r'(?:^|[_.-])(?:corpus|sources?|upstream|primary|private|history|search|inventory|inventories|fixtures?|controls?|extract\w*|render\w*|vendor|build|cop(?:y|ies|ied)|frozen|snapshots?|inputs?|evidence|roles?|formal\w*|manuscripts?|releases?|publications?|parent|intakes?|briefs?|reviews?|reviewers?|assessments?|dispatch\w*|tasks?|logs?|transcripts?|cache|\.git|venv|node_modules|downloads?|fetched|family-titles|authentications?)(?:$|[_.-])',re.I)
needle=re.compile(r'Navier[– -]?Stokes|solenoidal|(?:source|result|T)0?376\b|rapidly.vanishing|fixed.particle|spatial.clock|reciprocal.affine',re.I)
roots=['frontier/campaigns','frontier/iterations','frontier/experiments','frontier/proposals','frontier/scouts','frontier/notes','frontier/findings','iterations','experiments','proposals','scouts','notes','findings']
rows=[];omissions=[];stats={'utf8':0,'nonutf8_or_nul':0,'errors':[],'symlinks':0}; visited=set()
def blocked(s):return bool(active.search(s) or recent.search(s) or roles.search(s) or s=='fresh-analytic-discovery-r141')
for root in roots:
 base=ROOT/root
 if not base.exists():continue
 for d,ds,fs in os.walk(base,followlinks=False):
  # Every component tested before descent, including flat/compound names.
  keep=[]
  for n in ds:
   p=Path(d)/n
   if blocked(n) or p.is_symlink():omissions.append(str(p.relative_to(ROOT)))
   else:keep.append(n)
  ds[:]=keep
  for n in fs:
   p=Path(d)/n
   if blocked(n):omissions.append(str(p.relative_to(ROOT)));continue
   if p.is_symlink():stats['symlinks']+=1;continue
   rel=str(p.relative_to(ROOT))
   if rel in visited:continue
   visited.add(rel)
   try:
    b=p.read_bytes()
    if b'\0' in b:stats['nonutf8_or_nul']+=1;continue
    t=b.decode('utf8')
   except UnicodeError:stats['nonutf8_or_nul']+=1;continue
   except OSError as e:stats['errors'].append([rel,str(e)]);continue
   stats['utf8']+=1
   hits=[{'line':i+1,'text':x} for i,x in enumerate(t.splitlines()) if needle.search(x)]
   if hits:rows.append({'path':rel,'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'hits':hits})
(OUT/'private/history-search.json').write_text(json.dumps({'filters':[active.pattern,recent.pattern,roles.pattern],'roots':roots,'stats':stats,'pruned':omissions,'matches':rows},indent=2))
print(json.dumps(stats), 'matched',len(rows),'pruned',len(omissions))
for row in rows:
 print(row['path'],len(row['hits']))
 for h in row['hits'][:2]:print(' ',h['line'],h['text'][:380])
