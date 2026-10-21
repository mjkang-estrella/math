from pathlib import Path
import fnmatch,re,os
ROOT=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
OWN=ROOT/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r125'
# Full-path case-insensitive literal wildcard predicates, fixed before first traversal.
PATTERNS='''*structural*r159* *analytic*r153* *structural*r160* *analytic*r154* *t360s147*
*arithmetic*r124* *arithmetic*r123* *arithmetic*r122* *arithmetic*r121* *arithmetic*r120* *arithmetic*r119* *arithmetic*r118* *arithmetic*r117* *arithmetic*r116* *arithmetic*r115* *arithmetic*r114* *arithmetic*r113* *arithmetic*r112* *arithmetic*r111* *arithmetic*r110*
*analytic*r152* *analytic*r151* *analytic*r150* *analytic*r149* *analytic*r148* *analytic*r147* *analytic*r146* *analytic*r145* *analytic*r144* *analytic*r143* *analytic*r142* *analytic*r141* *analytic*r140* *analytic*r139* *analytic*r138*
*structural*r158* *structural*r157* *structural*r156* *structural*r155* *structural*r154* *structural*r153* *structural*r152* *structural*r151* *structural*r150* *structural*r149* *structural*r148* *structural*r147* *structural*r146*
*h138-* *t185r144-* *t177c143-* *t373e135-* *k369r134-* *t088p133-*
*new-ten* *terminal-summary* *summary.json* *tasks.json* *ten-findings* *twenty-findings* *second-history-screen* *history-screen* *history-broad-geometry* *prepare.py*'''.split()
CATEGORIES='''corpus source primary history search inventory fixture control extract render vendor build copy copied frozen role formal manuscript release parent private input upstream shortlist context fetched scratch preprint catalogue catalog receipt brief intake bundle recovery manifest authentication task work family-title literature venv site-packages packet payload archive cache download external third-party hits index navigation audit log provenance evidence ledger helper readme direct.tex pinned- scan snapshot submission retention retrieve record_evidence validation invocation checkpoint-output final report handoff disposition integrity checkpoint journal status progress outcome'''.split()
# Prefix matching: deliberately NO trailing boundary, so sources/inputs/snapshots/ledgers are excluded.
CATEGORY_RE=re.compile(r'(?:^|[/_. -])(?:'+ '|'.join(re.escape(x) for x in CATEGORIES)+')',re.I)
def reason(p):
 s=str(p.relative_to(ROOT)).lower()
 if p==OWN or OWN in p.parents:return 'own'
 if p.is_symlink():return 'symlink'
 if any(x.lower() in {'.git','dependencies','node_modules','__pycache__','.venv','venv'} for x in p.relative_to(ROOT).parts):return 'dependency'
 if any(fnmatch.fnmatchcase(s,x) for x in PATTERNS):return 'literal'
 if CATEGORY_RE.search(s):return 'coarse-category-prefix'
 return None
