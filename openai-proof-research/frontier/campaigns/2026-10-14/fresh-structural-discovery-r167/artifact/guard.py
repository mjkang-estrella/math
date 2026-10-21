from pathlib import PurePosixPath
from fnmatch import fnmatchcase
OWN='frontier/campaigns/2026-10-14/fresh-structural-discovery-r167'
WILDCARDS=['*analytic*r161*','*arithmetic*r132*','*arithmetic*r133*','*analytic*r162*','*arithmetic*r134*','*analytic*r163*','*structural*r161*','*t126s161*','*t360s147*',
'*structural*r166*','*structural*r165*','*structural*r164*','*structural*r163*','*structural*r162*','*structural*r160*','*structural*r159*','*structural*r158*','*structural*r157*','*structural*r156*','*structural*r155*','*structural*r154*','*structural*r153*','*structural*r152*',
'*analytic*r160*','*analytic*r159*','*analytic*r158*','*analytic*r157*','*analytic*r156*','*analytic*r155*','*analytic*r154*','*analytic*r153*','*analytic*r152*','*analytic*r151*','*analytic*r150*','*analytic*r149*','*analytic*r148*','*analytic*r147*','*analytic*r146*','*analytic*r145*',
'*arithmetic*r131*','*arithmetic*r130*','*arithmetic*r129*','*arithmetic*r128*','*arithmetic*r127*','*arithmetic*r126*','*arithmetic*r125*','*arithmetic*r124*','*arithmetic*r123*','*arithmetic*r122*','*arithmetic*r121*','*arithmetic*r120*','*arithmetic*r119*','*arithmetic*r118*','*arithmetic*r117*',
'*h138-*','*t185r144-*','*t177c143-*','*t373e135-*','*k369r134-*','*t088p133-*','*screen-*','*screen[0-9]*','*proof-r[0-9]*','*check-*','*history[0-9]*','*further-history-*']
SUBSTRINGS='''corpus source primary history derivative search inventory fixture control extract render vendor build copy copied frozen role formal manuscript release parent private input upstream shortlist context fetched scratch preprint catalogue catalog receipt brief intake bundle recovery manifest authentication task work family-title literature venv site-packages packet payload archive cache download external third-party hits index navigation audit log provenance evidence ledger helper readme direct.tex pinned- scan snapshot submissions retention retrieve record_evidence validation invocation checkpoint-output journal status progress final report handoff disposition integrity checkpoint contribution proof-role ten-findings twenty-findings new-ten terminal-summary summary.json summary sharedtasks sawin-2018 tao-teravainen acquire checks verify seal_once exact_moments tools scripts verification prepare metadata contracts bind_passages replay stderr author-completion reading-limit verifier fetch-family seal-family isolation reading-and-failures compound-history write_notes diagnostics result-helper history-scout dispatch integration reproduce reproduction resume launch scout review freeze rights .git seal toolkit reading-and-limits dependencies node_modules __pycache__ .tox .mypy_cache .pytest_cache'''.split()
def blocked(relative):
 s=relative.as_posix().casefold() if hasattr(relative,'as_posix') else PurePosixPath(relative).as_posix().casefold()
 if s==OWN or s.startswith(OWN+'/'): return True
 return any(fnmatchcase(s,p) for p in WILDCARDS) or any(x.casefold() in s for x in SUBSTRINGS)
if __name__=='__main__':
 protected=['a/PARENT-ANALYTIC-r161.md','a/b/ARITHMETIC-r132/c','z/role-ARITHMETIC-r133.md','a/ANALYTIC-r162.md','a/ARITHMETIC-r134.md','a/ANALYTIC-r163.md','a/flat-STRUCTURAL-r161-copy.md','a/T126S161-data','x/t360S147.md','a/README.md','a/NEW-TEN.md','x/TEN-FINDINGS/x','x/twenty-findings','a/SHAREDTASKS/a','a/SCREEN001.md','a/history17.md','a/compound-history.md','a/REPRODUCTION/a','a/WRiTE_NOTES.py',OWN+'/notes/a.md']
 protected += ['x/'+p.strip('*')+'/y' for p in WILDCARDS if '[' not in p]
 assert all(blocked(p) for p in protected)
 assert not blocked('frontier/campaigns/2026-10-14/iteration-r40/notes/hamiltonian.tex')
 print('Synthetic-only guard tests passed:',len(protected),'protected examples; one eligible example.')
