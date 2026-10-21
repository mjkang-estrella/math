"""Prospective coarse isolation, installed before any filename traversal."""
from pathlib import Path
import fnmatch,re
OWN='frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r133'
PATTERNS=[
 '*analytic*r161*','*analytic*r162*','*analytic*r163*',
 '*structural*r167*','*structural*r168*','*structural*r169*','*structural*r161*',
 '*t126s161*','*t360s147*',
 '*arithmetic*r132*','*arithmetic*r131*','*arithmetic*r130*','*arithmetic*r129*','*arithmetic*r128*','*arithmetic*r127*','*arithmetic*r126*','*arithmetic*r125*','*arithmetic*r124*','*arithmetic*r123*','*arithmetic*r122*','*arithmetic*r121*','*arithmetic*r120*','*arithmetic*r119*','*arithmetic*r118*',
 '*analytic*r160*','*analytic*r159*','*analytic*r158*','*analytic*r157*','*analytic*r156*','*analytic*r155*','*analytic*r154*','*analytic*r153*','*analytic*r152*','*analytic*r151*','*analytic*r150*','*analytic*r149*','*analytic*r148*','*analytic*r147*','*analytic*r146*',
 '*structural*r166*','*structural*r165*','*structural*r164*','*structural*r163*','*structural*r162*','*structural*r160*','*structural*r159*','*structural*r158*','*structural*r157*','*structural*r156*','*structural*r155*','*structural*r154*','*structural*r153*',
 '*h138-*','*t185r144-*','*t177c143-*','*t373e135-*','*k369r134-*','*t088p133-*']
# Deliberately broad substring guards: opaque aliases may escape; unrelated originals
# can be omitted. All operate on casefolded FULL RELATIVE path before descent/read.
GUARDS='''corpus source primary history-derivative search inventory fixture control extract render vendor build copy copied frozen role formal manuscript release parent private input upstream shortlist context fetched scratch preprint catalogue catalog receipt brief intake bundle recovery manifest authentication task work family-title literature venv site-packages packet payload archive cache download external third-party hits index navigation audit log provenance evidence ledger helper readme direct.tex pinned- scan snapshot submissions retention retrieve record_evidence validation invocation checkpoint-output journal status progress final report handoff disposition integrity checkpoint contribution proof-role ten-findings twenty-findings new-ten sharedtasks terminal-summary summary.json sawin-2018 tao-teravainen acquire checks verify seal_once exact_moments tools scripts verification prepare metadata contracts bind_passages replay stderr author-completion reading-limit further-history- reading-limits verifier check- fetch-family seal-family isolation reading-and-failures compound-history write_notes diagnostics result-helper reading failure outcome completion retrieval seal diagnostic history-scout history-focused history screen review proof-r freeze summary rights dispatch integration reproduce reproduction resume launch scout dependencies node_modules .git __pycache__'''.split()
def excluded(relative):
 s=Path(relative).as_posix().casefold()
 if s==OWN or s.startswith(OWN+'/'): return True
 if any(fnmatch.fnmatchcase(s,p) for p in PATTERNS): return True
 if any(g in s for g in GUARDS): return True
 if re.search(r'history[0-9]|screen-|screen[0-9]{3}',s): return True
 return False
if __name__=='__main__':
 protected=['x/Author-ANALYTIC-r161.md','x/parent-structural-X-r167-copy/a','x/AnaLYTic-r162/a','X/STRUCTURAL-r168/a','x/analytic-r163/a','x/structural-r169/a','x/STRUCTURAL-r161/a','x/T126S161/a','x/T360S147/a','x/compound-screen037-notes/a','x/ABCscreen-foo/a','X/README.md','x/NEW-TEN/a','x/TEN-FINDINGS/a','x/twenty-findings/a','x/SharedTasks/a','x/SUMMARY/a','x/DISPATCH/a','x/old-HISTORY23/a','x/hidden/.SOURCE/a',OWN+'/notes/a']
 assert all(excluded(p) for p in protected)
 assert not excluded('frontier/campaigns/old/notes/kahler.tex')
 print('Synthetic predicate tests passed; no protected bodies opened.')
