from pathlib import Path
import fnmatch, os
PROJECT=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
ROOT=PROJECT/'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r153'
# These predicates apply to the entire relative path BEFORE descent or file reading.
PATTERNS=[
 '*structural*r158*','*arithmetic*r124*','*structural*r159*','*arithmetic*r125*','*t360s147*',
 '*analytic*r152*','*analytic*r151*','*analytic*r150*','*analytic*r149*','*analytic*r148*',
 '*analytic*r147*','*analytic*r146*','*analytic*r145*','*analytic*r144*','*analytic*r143*',
 '*analytic*r142*','*analytic*r141*','*analytic*r140*','*analytic*r139*','*analytic*r138*',
 '*structural*r157*','*structural*r156*','*structural*r155*','*structural*r154*',
 '*structural*r153*','*structural*r152*','*structural*r151*','*structural*r150*',
 '*structural*r149*','*structural*r148*','*structural*r147*','*structural*r146*',
 '*arithmetic*r123*','*arithmetic*r122*','*arithmetic*r121*','*arithmetic*r120*',
 '*arithmetic*r119*','*arithmetic*r118*','*arithmetic*r117*','*arithmetic*r116*',
 '*arithmetic*r115*','*arithmetic*r114*','*arithmetic*r113*','*arithmetic*r112*',
 '*arithmetic*r111*','*arithmetic*r110*','*h138-*','*t185r144-*','*t177c143-*',
 '*t373e135-*','*k369r134-*','*t088p133-*','*analytic*r153*',
 '*screen-*','*screen[0-9][0-9][0-9]*','*proof-r[0-9]*',
]
# Deliberately coarse: omissions are logged, never described as exhaustive clearance.
TOKENS='corpus source primary history search inventory fixture control extract render vendor build copy copied frozen role formal manuscript release parent private input upstream shortlist context fetched scratch preprint catalogue catalog receipt brief intake bundle recovery manifest authentication task work family-title literature venv site-packages packet payload archive cache download external third-party hits index navigation audit log provenance evidence ledger helper readme direct.tex pinned- scan snapshot submissions retention retrieve record_evidence validation invocation checkpoint-output journal status progress final report handoff disposition integrity checkpoint contribution proof-role review check freeze summary rights new-ten terminal-summary'.split()
def excluded(path):
 s=str(path.relative_to(PROJECT)).lower()
 if any(p in {'.git','node_modules','dependencies','__pycache__','.venv','venv'} for p in path.relative_to(PROJECT).parts): return True
 return any(fnmatch.fnmatchcase(s,p) for p in PATTERNS) or any(t in s for t in TOKENS)
def walk():
 for base,dirs,files in os.walk(PROJECT,topdown=True,followlinks=False):
  dirs[:]=[d for d in dirs if not excluded(Path(base)/d) and not (Path(base)/d).is_symlink()]
  for name in files:
   p=Path(base)/name
   if not excluded(p) and not p.is_symlink(): yield p
if __name__=='__main__':
 import json
 (ROOT/'notes/ISOLATION-PREDICATES.json').write_text(json.dumps({'patterns':PATTERNS,'coarse_substrings':TOKENS,'limits':'Full-relative-path filtering before descent/read. Symlinks omitted. Opaque aliases may evade classification; coarse predicates omit relevant authored material. No perfect/exhaustive clearance.'},indent=2)+'\n')
