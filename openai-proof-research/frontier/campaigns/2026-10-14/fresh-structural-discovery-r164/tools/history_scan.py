from pathlib import Path
import os,re,json,fnmatch,hashlib
P=Path.cwd(); R=P/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r164'
patterns=['*analytic*r158*','*arithmetic*r130*','*analytic*r159*','*arithmetic*r131*','*structural*r161*','*t126s161*','*structural*r163*','*structural*r164*','*t360s147*']
patterns += [f'*arithmetic*r{i}*' for i in range(112,130)]
patterns += [f'*analytic*r{i}*' for i in range(140,158)]
patterns += [f'*structural*r{i}*' for i in range(148,164)]
patterns += ['*h138-*','*t185r144-*','*t177c143-*','*t373e135-*','*k369r134-*','*t088p133-*']
coarse='corpus source primary history-derivative search inventory fixture control extract render vendor build copy copied frozen role formal manuscript release parent private input upstream shortlist context fetched scratch preprint catalogue catalog receipt brief intake bundle recovery manifest authentication task work family-title literature venv site-packages packet payload archive cache download external third-party hits index navigation audit log provenance evidence ledger helper readme direct.tex pinned- scan snapshot submissions retention retrieve record_evidence validation invocation checkpoint-output final report handoff disposition integrity checkpoint journal status progress new-ten terminal-summary summary.json tasks.json ten-findings twenty-findings second-history-screen history-screen history-broad-geometry prepare.py dispatch integration checks diagnostic stdout stderr dependency dependencies node_modules .git history review reading seal metadata admin generator'.split()
# Prefixes intentionally catch sources, inputs, snapshots, ledgers etc and compound aliases.
guard=re.compile('|'.join(re.escape(x) for x in coarse),re.I) # Deliberately coarse substring aliases, including outsideREPORT
def reason(p):
 s=p.as_posix().lower()
 for pat in patterns:
  if fnmatch.fnmatchcase(s,pat):return pat
 m=guard.search(s)
 return 'coarse:'+m.group(0) if m else None
policy={'full_path_case_insensitive_wildcards':patterns,'prefix_categories':coarse,'no_trailing_boundary':True,'symlinks':'skip before open/descent','no_size_cutoff':True,'limits':'Coarse guards omit genuine authored work; opaque aliases may escape. No perfect isolation or exhaustive clearance. Named completed originals are direct exceptions, not scan exceptions.'}
(R/'private/history/isolation-policy.json').write_text(json.dumps(policy,indent=2)+'\n')
if __name__=='__main__':
 needle=re.compile(r'hadwiger|colin.{0,9}verdi|clique.{0,12}minor|list.{0,8}colou?r|fractional.{0,10}chromatic|graph.{0,8}colou?r|correspondence.{0,8}colou?r|paintab|choosab|bipartite.{0,10}(?:hole|density)|antimatching',re.I)
 hits=[]; admitted=[]; omitted=[]; nonutf=[]
 # os.walk is top-down: rejected directories are removed BEFORE descent.
 for base in ['frontier','campaigns','iterations','experiments','proposals','scouts','notes','findings']:
  root=P/base
  if not root.is_dir():continue
  for here,dirs,files in os.walk(root,topdown=True,followlinks=False):
   for n in list(dirs):
    p=Path(here)/n; rel=p.relative_to(P); why=reason(rel)
    if why or p.is_symlink():
     dirs.remove(n); omitted.append([str(rel),why or 'symlink'])
   for n in files:
    p=Path(here)/n; rel=p.relative_to(P); why=reason(rel)
    if why or p.is_symlink():omitted.append([str(rel),why or 'symlink']);continue
    b=p.read_bytes()
    try:s=b.decode('utf-8')
    except UnicodeDecodeError:nonutf.append(str(rel));continue
    admitted.append({'path':str(rel),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
    lines=[{'line':i,'text':line} for i,line in enumerate(s.splitlines(),1) if needle.search(line)]
    if lines:hits.append({'path':str(rel),'hits':lines})
 (R/'private/history/scan-members.json').write_text(json.dumps({'admitted':admitted,'pruned':omitted,'nonutf8':nonutf},indent=2)+'\n')
 (R/'private/history/mechanism-hits.json').write_text(json.dumps(hits,indent=2)+'\n')
 print(json.dumps({'utf8_scanned':len(admitted),'pruned_paths':len(omitted),'nonutf8':len(nonutf),'hit_files':len(hits),'hits':[{'path':h['path'],'lines':[x['line'] for x in h['hits']]} for h in hits]},indent=2))
