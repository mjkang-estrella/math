"""Prospective coarse path guard. Run from actual project root. No symlinks."""
from pathlib import Path
import os, fnmatch, re, json, hashlib
ROOT=Path.cwd()
OWN=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r156')
# Literal individual predicates, applied case-insensitively to complete relative paths.
ROUND_PATTERNS='''*structural*r161* *arithmetic*r127* *structural*r162* *arithmetic*r128* *t360s147*
*analytic*r155* *analytic*r154* *analytic*r153* *analytic*r152* *analytic*r151* *analytic*r150* *analytic*r149* *analytic*r148* *analytic*r147* *analytic*r146* *analytic*r145* *analytic*r144* *analytic*r143* *analytic*r142* *analytic*r141* *analytic*r140* *analytic*r139* *analytic*r138*
*structural*r160* *structural*r159* *structural*r158* *structural*r157* *structural*r156* *structural*r155* *structural*r154* *structural*r153* *structural*r152* *structural*r151* *structural*r150* *structural*r149* *structural*r148* *structural*r147* *structural*r146*
*arithmetic*r126* *arithmetic*r125* *arithmetic*r124* *arithmetic*r123* *arithmetic*r122* *arithmetic*r121* *arithmetic*r120* *arithmetic*r119* *arithmetic*r118* *arithmetic*r117* *arithmetic*r116* *arithmetic*r115* *arithmetic*r114* *arithmetic*r113* *arithmetic*r112* *arithmetic*r111* *arithmetic*r110*
*h138-* *t185r144-* *t177c143-* *t373e135-* *k369r134-* *t088p133-*'''.split()
# Intentionally coarse. It sacrifices recall and cannot classify opaque aliases.
TOKENS='''corpus source primary history derivative search inventory fixture control extract render vendor build copy copied frozen role formal manuscript release parent private input upstream shortlist context fetched scratch preprint catalogue catalog receipt brief intake bundle recovery manifest authentication task work family-title literature venv site-packages packet payload archive cache download external third-party hits index navigation audit log provenance evidence ledger helper readme direct.tex pinned- scan snapshot submissions retention retrieve record_evidence validation invocation checkpoint-output journal status progress final report handoff disposition integrity checkpoint contribution proof-role ten-findings twenty-findings new-ten terminal-summary summary.json history-scout review check freeze summary rights dependencies node_modules verification canonical-bindings reading-limits hepp dybalski buchholz ruelle araki lee-rogers-seeger seeger1988 jsw lrs- bhs-'''.split()
def reason(p):
 s=p.as_posix().lower()
 if s==OWN.as_posix() or s.startswith(OWN.as_posix()+'/'): return 'own'
 if any(fnmatch.fnmatchcase(s,x) for x in ROUND_PATTERNS): return 'round'
 if '.git' in p.parts: return '.git'
 if re.search(r'screen(?:-|\d)|proof-r\d',s): return 'screen/proof-admin'
 if any(t in s for t in TOKENS): return 'coarse-category'
 return None

def eligible():
 skipped={}; files=[]
 for base,dirs,names in os.walk(ROOT,topdown=True,followlinks=False):
  rel=Path(base).relative_to(ROOT)
  keep=[]
  for n in dirs:
   p=rel/n; why=reason(p)
   if (ROOT/p).is_symlink(): why='symlink'
   if why: skipped[why]=skipped.get(why,0)+1
   else: keep.append(n)
  dirs[:]=keep
  for n in names:
   p=rel/n; why=reason(p)
   if (ROOT/p).is_symlink(): why='symlink'
   if why: skipped[why]=skipped.get(why,0)+1
   else: files.append(p)
 return files,skipped
if __name__=='__main__':
 files,skipped=eligible()
 (OWN/'private'/'eligible-paths.json').write_text(json.dumps([p.as_posix() for p in files],indent=2))
 (OWN/'notes'/'scan-coverage.json').write_text(json.dumps({'eligible_files':len(files),'pruned_entries':skipped,'limits':'coarse omissions; opaque aliases not certified; no body scan yet'},indent=2))
 print(json.dumps({'eligible_files':len(files),'pruned_entries':skipped}))
