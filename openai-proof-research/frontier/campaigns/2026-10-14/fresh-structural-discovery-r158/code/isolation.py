from pathlib import Path
import fnmatch
ROOT=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r158')
# Every round predicate is a distinct literal; lowercased full project-relative paths.
ROUND_PATTERNS=[
 '*arithmetic*r123*','*analytic*r152*','*arithmetic*r124*','*analytic*r153*','*t360s147*',
 '*structural*r157*','*structural*r156*','*structural*r155*','*structural*r154*','*structural*r153*','*structural*r152*','*structural*r151*','*structural*r150*','*structural*r149*','*structural*r148*','*structural*r147*','*structural*r146*','*structural*r145*',
 '*analytic*r151*','*analytic*r150*','*analytic*r149*','*analytic*r148*','*analytic*r147*','*analytic*r146*','*analytic*r145*','*analytic*r144*','*analytic*r143*','*analytic*r142*','*analytic*r141*','*analytic*r140*','*analytic*r139*','*analytic*r138*','*analytic*r137*',
 '*arithmetic*r122*','*arithmetic*r121*','*arithmetic*r120*','*arithmetic*r119*','*arithmetic*r118*','*arithmetic*r117*','*arithmetic*r116*','*arithmetic*r115*','*arithmetic*r114*','*arithmetic*r113*','*arithmetic*r112*','*arithmetic*r111*','*arithmetic*r110*','*arithmetic*r109*',
 '*h138-*','*t185r144-*','*t177c143-*','*t373e135-*','*k369r134-*','*t088p133-*']
COARSE='ten-findings twenty-findings paused-at history prepare screening-before-freeze corpus source primary history-derivative search inventory fixture control extract render vendor build copy copied frozen role formal manuscript release parent private input upstream shortlist context fetched scratch preprint catalogue catalog receipt brief intake bundle recovery manifest authentication task work family-title literature venv site-packages packet payload archive cache download external third-party hits index navigation audit log provenance evidence ledger helper readme direct.tex pinned- scan snapshot submissions retention retrieve record_evidence validation invocation checkpoint-output journal status progress final report handoff disposition integrity checkpoint contribution proof-role acquire retrieval history-screen second-history reading-rights dispatch write_notes seal verify review'.split()
DEPENDENCIES={'.git','node_modules','.venv','venv','__pycache__','site-packages','dist','target','.mypy_cache','.pytest_cache'}
def reason(path):
 s=Path(path).as_posix().lower()
 if s==ROOT.as_posix().lower() or s.startswith(ROOT.as_posix().lower()+'/'): return 'own-root'
 if s=='frontier/new-ten-2026-10-14.md': return 'shared-new-ten'
 if any(p in DEPENDENCIES for p in Path(s).parts): return 'dependency/git'
 for pat in ROUND_PATTERNS:
  if fnmatch.fnmatchcase(s,pat): return pat
 for word in COARSE:
  if word in s: return 'coarse:'+word
 return None
