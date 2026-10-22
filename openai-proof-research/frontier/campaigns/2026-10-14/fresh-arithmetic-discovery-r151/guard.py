from pathlib import Path
from fnmatch import fnmatchcase
import os
ROOT=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
OWN=ROOT/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r151'
# Each supplied literal is separately installed; matching is on the full project-relative POSIX path.casefold().
WILDCARDS='''*analytic*r162* *structural*r168* *arithmetic*r134* *analytic*r163* *structural*r169* *arithmetic*r135* *analytic*r164* *structural*r170* *arithmetic*r136* *analytic*r144* *analytic*r145* *analytic*r146* *analytic*r147* *analytic*r148* *analytic*r149* *analytic*r150* *analytic*r151* *analytic*r152* *analytic*r153* *analytic*r154* *analytic*r155* *analytic*r156* *analytic*r157* *analytic*r158* *analytic*r159* *analytic*r160* *analytic*r161* *structural*r151* *structural*r152* *structural*r153* *structural*r154* *structural*r155* *structural*r156* *structural*r157* *structural*r158* *structural*r159* *structural*r160* *structural*r161* *structural*r162* *structural*r163* *structural*r164* *structural*r165* *structural*r166* *structural*r167* *arithmetic*r116* *arithmetic*r117* *arithmetic*r118* *arithmetic*r119* *arithmetic*r120* *arithmetic*r121* *arithmetic*r122* *arithmetic*r123* *arithmetic*r124* *arithmetic*r125* *arithmetic*r126* *arithmetic*r127* *arithmetic*r128* *arithmetic*r129* *arithmetic*r130* *arithmetic*r131* *arithmetic*r132* *arithmetic*r133* *t126s161* *t360s147* *t337a161* *h138-* *t185r144-* *t177c143-* *t373e135-* *k369r134-* *t088p133-*
*arithmetic*r136* *arithmetic*r137* *arithmetic*r138* *arithmetic*r139* *arithmetic*r140* *arithmetic*r141* *arithmetic*r142* *arithmetic*r143* *arithmetic*r144* *analytic*r164* *analytic*r165* *analytic*r166* *analytic*r167* *analytic*r168* *analytic*r169* *analytic*r170* *analytic*r171* *structural*r171* *structural*r172* *structural*r173* *structural*r174* *structural*r175* *structural*r176* *structural*r177* *structural*r178* *structural*r179* *s176a*
*analytic*r172* *analytic*r173* *analytic*r174* *structural*r180* *structural*r181* *structural*r182* *arithmetic*r145* *arithmetic*r146* *arithmetic*r147*
*analytic*r175* *analytic*r176* *analytic*r177* *structural*r183* *structural*r184* *structural*r185* *arithmetic*r148* *arithmetic*r149* *arithmetic*r150*
*analytic*r178* *analytic*r179* *analytic*r180* *arithmetic*r151* *arithmetic*r152* *arithmetic*r153* *structural*r186* *structural*r187* *structural*r188*
*arithmetic*r154* *arithmetic*r155* *arithmetic*r156* *analytic*r181* *analytic*r182* *analytic*r183* *structural*r189* *structural*r190* *structural*r191*'''.split()
SUBSTRINGS='''corpus source primary history derivative search inventory fixture control extract render vendor build copy copied frozen role formal manuscript release parent private input upstream shortlist context fetched scratch preprint catalogue catalog receipt brief intake bundle recovery manifest authentication task work family-title literature venv site-packages packet payload archive cache download external third-party hits index navigation audit log provenance evidence ledger helper readme direct.tex pinned- scan snapshot submissions retention retrieve record_evidence validation invocation checkpoint-output journal status progress final report handoff disposition integrity checkpoint contribution proof-role ten-findings twenty-findings new-ten sharedtasks terminal-summary summary.json summary sawin-2018 tao-teravainen acquire checks verify seal_once exact_moments tools scripts verification prepare metadata contracts bind_passages replay stderr author-completion reading-limit reading-limits verifier fetch-family seal-family isolation reading-and-failures compound-history write_notes diagnostics result-helper reading failure outcome completion retrieval seal diagnostic history-scout history-focused screen review proof-r check- freeze rights dispatch integration reproduce reproduction resume launch scout dependencies node_modules .git __pycache__ toolkit canonical-bindings capture.py bind.py publication check'''.split()
EXPLICIT=['history[0-9]*','further-history-*','screen-*','screen[0-9][0-9][0-9]*','role*','proof-r[0-9]*','check*','freeze*','summary*','rights*']
def blocked(p):
    s=p.relative_to(ROOT).as_posix().casefold()
    return (any(fnmatchcase(s,w) for w in WILDCARDS) or any(t in s for t in SUBSTRINGS)
      or any(fnmatchcase(part,w) for part in s.split('/') for w in EXPLICIT))
def walk():
    for current, dirs, files in os.walk(ROOT,followlinks=False):
        d=Path(current)
        dirs[:]=sorted(x for x in dirs if not (d/x).is_symlink() and not blocked(d/x))
        for name in sorted(files):
            p=d/name
            if not p.is_symlink() and not blocked(p): yield p
if __name__=='__main__':
    eligible=list(walk())
    (OWN/'private/eligible-paths.txt').write_text('\n'.join(p.relative_to(ROOT).as_posix() for p in eligible)+'\n')
    print('Eligible paths:',len(eligible))
