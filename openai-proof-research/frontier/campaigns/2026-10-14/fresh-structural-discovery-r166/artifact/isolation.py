"""Prospective broad-history guards; direct authorized originals bypass this walker."""
from pathlib import Path
import fnmatch, os
ROOT=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
OWN='frontier/campaigns/2026-10-14/fresh-structural-discovery-r166'
PATTERNS=[
'*analytic*r160*','*arithmetic*r132*','*analytic*r161*','*arithmetic*r133*',
'*analytic*r162*','*arithmetic*r134*','*structural*r161*','*t126s161*','*t360s147*',
'*structural*r165*','*structural*r164*','*structural*r163*','*structural*r162*',
'*structural*r160*','*structural*r159*','*structural*r158*','*structural*r157*',
'*structural*r156*','*structural*r155*','*structural*r154*','*structural*r153*',
'*structural*r152*','*structural*r151*','*structural*r150*',
'*analytic*r159*','*analytic*r158*','*analytic*r157*','*analytic*r156*',
'*analytic*r155*','*analytic*r154*','*analytic*r153*','*analytic*r152*',
'*analytic*r151*','*analytic*r150*','*analytic*r149*','*analytic*r148*',
'*analytic*r147*','*analytic*r146*','*analytic*r145*','*analytic*r144*','*analytic*r143*',
'*arithmetic*r131*','*arithmetic*r130*','*arithmetic*r129*','*arithmetic*r128*',
'*arithmetic*r127*','*arithmetic*r126*','*arithmetic*r125*','*arithmetic*r124*',
'*arithmetic*r123*','*arithmetic*r122*','*arithmetic*r121*','*arithmetic*r120*',
'*arithmetic*r119*','*arithmetic*r118*','*arithmetic*r117*','*arithmetic*r116*',
'*arithmetic*r115*','*h138-*','*t185r144-*','*t177c143-*','*t373e135-*',
'*k369r134-*','*t088p133-*','*structural*r144*','*t185*',
'*history[0-9]*','*further-history-*','*proof-r[0-9]*','*screen-*','*screen[0-9][0-9][0-9]*']
# Deliberately coarse substring exclusions, applied to the CASEFOLDED FULL PATH.
GUARDS='''corpus source primary history-derivative search inventory fixture control extract render vendor build copy copied frozen role formal manuscript release parent private input upstream shortlist context fetched scratch preprint catalogue catalog receipt brief intake bundle recovery manifest authentication task work family-title literature venv site-packages packet payload archive cache download external third-party hits index navigation audit log provenance evidence ledger helper readme direct.tex pinned- scan snapshot submissions retention retrieve record_evidence validation invocation checkpoint-output journal status progress final report handoff disposition integrity checkpoint contribution proof-role ten-findings twenty-findings sawin-2018 tao-teravainen acquire checks verify seal_once exact_moments tools scripts verification prepare metadata contracts bind_passages replay stderr author-completion reading-limit history-scout verifier check- new-ten terminal-summary summary.json summary sharedtasks dispatch integration reproduce reproduction resume launch scout history diagnostics write_notes review freeze rights .git dependencies node_modules __pycache__'''.split()
def blocked(relative):
 s=relative.as_posix().casefold()
 if s==OWN or s.startswith(OWN+'/'): return True
 return any(fnmatch.fnmatchcase(s,p) for p in PATTERNS) or any(g in s for g in GUARDS)
def walk():
 for base,ds,fs in os.walk(ROOT,topdown=True,followlinks=False):
  rel=Path(base).relative_to(ROOT)
  ds[:]=[d for d in ds if not blocked(rel/d) and not (Path(base)/d).is_symlink()]
  for f in fs:
   r=rel/f
   if not blocked(r) and not (ROOT/r).is_symlink(): yield r
if __name__=='__main__':
 tests=['frontier/x/ANALYTIC-r160/a.md','frontier/ARITHMETIC-foo-r133.md','x/T126S161-role.md','x/t360S147.md','x/a/README.md','x/SOURCE/okay.md','x/T185R144-foo/n.md','x/STRUCTURAL-r161-anything.md','x/a/SCREEN-44.md','x/HISTORY32-a/a.md','x/ReProduction-FOO/a.md',OWN+'/notes/a.md','x/a/SUMMARY.md','x/a/Private/a.md','x/STRUCTURAL-r165/a.md']
 assert all(blocked(Path(p)) for p in tests)
 assert not blocked(Path('frontier/campaigns/old/notes/02-matroid.md'))
 print('Synthetic-only guard tests passed. Full-path/component casefold used; no protected body opened.')
