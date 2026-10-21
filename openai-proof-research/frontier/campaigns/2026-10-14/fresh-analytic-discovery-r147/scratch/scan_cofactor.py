from pathlib import Path
import os,fnmatch,re,json
ROOT=Path.cwd();OUT=ROOT/'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r147'
rounds={'analytic':range(135,147),'structural':range(143,154),'arithmetic':range(107,119)}
patterns=[f'*{kind}*r{n}*' for kind,ns in rounds.items() for n in ns]+[f'*{s}*' for s in ['h138-','t185r144-','t177c143-','t373e135-','k369r134-','t088p133-']]
categories='corpus source primary history search inventory fixture control extract render vendor build copy frozen role formal manuscript release parent private input upstream shortlist context fetched scratch preprint catalogue catalog receipt brief intake bundle recovery manifest authentication task work family-title literature venv site-packages packet payload archive cache download external third-party hits index navigation audit log provenance evidence ledger helper readme direct.tex pinned- scan snapshot submissions retention retrieve record_evidence copied validation invocation checkpoint-output'.split()
def denied(name):
 s=name.casefold()
 return s in {'.git','node_modules','__pycache__'} or any(fnmatch.fnmatchcase(s,p) for p in patterns) or any(v in s for v in categories)
pat=re.compile(r'cofactor|adjugate|Piola|broken.action|focal.{0,40}Sobolev|Sobolev.{0,40}focal',re.I)
stats={'eligible_utf8':0,'nul':0,'non_utf8':0,'symlink':0,'errors':0};pruned=[];hits=[];skips=[]
for base,dirs,files in os.walk(ROOT,topdown=True,followlinks=False):
 kept=[]
 for n in sorted(dirs):
  p=Path(base)/n;rel=str(p.relative_to(ROOT))
  if p==OUT or denied(n):pruned.append(rel)
  elif p.is_symlink():stats['symlink']+=1;skips.append([rel,'symlink'])
  else:kept.append(n)
 dirs[:]=kept
 for n in sorted(files):
  p=Path(base)/n;rel=str(p.relative_to(ROOT))
  if denied(n):pruned.append(rel);continue
  if p.is_symlink():stats['symlink']+=1;skips.append([rel,'symlink']);continue
  try:b=p.read_bytes()
  except OSError as e:stats['errors']+=1;skips.append([rel,str(e)]);continue
  if b'\0' in b:stats['nul']+=1;skips.append([rel,'NUL']);continue
  try:t=b.decode('utf8')
  except UnicodeDecodeError:stats['non_utf8']+=1;skips.append([rel,'nonUTF8']);continue
  stats['eligible_utf8']+=1
  match=[{'line':i,'text':l} for i,l in enumerate(t.splitlines(),1) if pat.search(l)]
  if match:hits.append({'path':rel,'matches':match})
obj={'policy':{'patterns':patterns,'categories':categories,'no_size_cutoff':True,'hidden_ignored_json':True},'stats':stats,'pruned':pruned,'skips':skips,'hits':hits}
(OUT/'private/search/cofactor-history.json').write_text(json.dumps(obj,indent=2)+'\n')
print(json.dumps({'stats':stats,'pruned_count':len(pruned),'hit_files':len(hits),'hit_lines':sum(len(h['matches']) for h in hits)}))
for h in hits:
 print(h['path'])
 for m in h['matches']: print(' ',m['line'],m['text'][:900])
