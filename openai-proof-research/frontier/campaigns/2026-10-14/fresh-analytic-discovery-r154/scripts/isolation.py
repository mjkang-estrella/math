"""Prospective path filter. Coarse omissions and opaque aliases remain possible."""
import fnmatch, os, re
from pathlib import Path
ROOT=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
OWN=ROOT/'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r154'
ROUND_PATTERNS=[
 '*structural*r159*','*arithmetic*r125*','*structural*r160*','*arithmetic*r126*','*t360s147*',
 '*analytic*r153*','*analytic*r152*','*analytic*r151*','*analytic*r150*','*analytic*r149*','*analytic*r148*','*analytic*r147*','*analytic*r146*','*analytic*r145*','*analytic*r144*','*analytic*r143*','*analytic*r142*','*analytic*r141*','*analytic*r140*','*analytic*r139*','*analytic*r138*',
 '*structural*r158*','*structural*r157*','*structural*r156*','*structural*r155*','*structural*r154*','*structural*r153*','*structural*r152*','*structural*r151*','*structural*r150*','*structural*r149*','*structural*r148*','*structural*r147*','*structural*r146*',
 '*arithmetic*r124*','*arithmetic*r123*','*arithmetic*r122*','*arithmetic*r121*','*arithmetic*r120*','*arithmetic*r119*','*arithmetic*r118*','*arithmetic*r117*','*arithmetic*r116*','*arithmetic*r115*','*arithmetic*r114*','*arithmetic*r113*','*arithmetic*r112*','*arithmetic*r111*','*arithmetic*r110*',
 '*h138-*','*t185r144-*','*t177c143-*','*t373e135-*','*k369r134-*','*t088p133-*']
TOKENS='corpus source primary history search inventory fixture control extract render vendor build copy copied frozen role formal manuscript release parent private input upstream shortlist context fetched scratch preprint catalogue catalog receipt brief intake bundle recovery manifest authentication task work family-title literature venv site-packages packet payload archive cache download external third-party hits index navigation audit log provenance evidence ledger helper readme direct.tex pinned- scan snapshot submissions retention retrieve record_evidence validation invocation checkpoint-output journal status progress final report handoff disposition integrity checkpoint contribution proof-role history-focused compound-history review freeze summary rights verification seal anchor metadata retrieval novelty reproduction assemble'.split()
PATTERNS=ROUND_PATTERNS+['*'+x+'*' for x in TOKENS]+['*.git*','*dependencies*','*node_modules*','*new-ten*','*ten-findings*','*terminal-summary*','*summary.json*','*screen-*','*screen[0-9][0-9][0-9]*','*proof-r[0-9]*','*proof_r[0-9]*','*check*']
def excluded(p):
 s=p.relative_to(ROOT).as_posix().lower()
 return p==OWN or OWN in p.parents or any(fnmatch.fnmatchcase(s,k) for k in PATTERNS)
def walk():
 for base,dirs,files in os.walk(ROOT,topdown=True,followlinks=False):
  b=Path(base)
  dirs[:]=sorted(d for d in dirs if not (b/d).is_symlink() and not excluded(b/d))
  for n in sorted(files):
   p=b/n
   if not p.is_symlink() and not excluded(p): yield p
