# Prospective filter installed before any filename traversal. Broad history only.
import os,fnmatch,re
from pathlib import Path
ROOT=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
OWN='frontier/campaigns/2026-10-14/fresh-analytic-discovery-r155'
PATTERNS=['*arithmetic*r126*', '*arithmetic*r127*', '*structural*r161*', '*structural*r162*', '*t360s147*', '*analytic*r138*', '*analytic*r139*', '*analytic*r140*', '*analytic*r141*', '*analytic*r142*', '*analytic*r143*', '*analytic*r144*', '*analytic*r145*', '*analytic*r146*', '*analytic*r147*', '*analytic*r148*', '*analytic*r149*', '*analytic*r150*', '*analytic*r151*', '*analytic*r152*', '*analytic*r153*', '*analytic*r154*', '*structural*r146*', '*structural*r147*', '*structural*r148*', '*structural*r149*', '*structural*r150*', '*structural*r151*', '*structural*r152*', '*structural*r153*', '*structural*r154*', '*structural*r155*', '*structural*r156*', '*structural*r157*', '*structural*r158*', '*structural*r159*', '*structural*r160*', '*arithmetic*r110*', '*arithmetic*r111*', '*arithmetic*r112*', '*arithmetic*r113*', '*arithmetic*r114*', '*arithmetic*r115*', '*arithmetic*r116*', '*arithmetic*r117*', '*arithmetic*r118*', '*arithmetic*r119*', '*arithmetic*r120*', '*arithmetic*r121*', '*arithmetic*r122*', '*arithmetic*r123*', '*arithmetic*r124*', '*arithmetic*r125*', '*h138-*', '*t185r144-*', '*t177c143-*', '*t373e135-*', '*k369r134-*', '*t088p133-*']
ROLES=['corpus', 'source', 'primary', 'history-derivative', 'compound-history', 'history-focused', 'search', 'inventory', 'fixture', 'control', 'extract', 'render', 'vendor', 'build', 'copy', 'copied', 'frozen', 'role', 'formal', 'manuscript', 'release', 'parent', 'private', 'input', 'upstream', 'shortlist', 'context', 'fetched', 'scratch', 'preprint', 'catalogue', 'catalog', 'receipt', 'brief', 'intake', 'bundle', 'recovery', 'manifest', 'authentication', 'task', 'work', 'family-title', 'literature', 'venv', 'site-packages', 'packet', 'payload', 'archive', 'cache', 'download', 'external', 'third-party', 'hits', 'index', 'navigation', 'audit', 'log', 'provenance', 'evidence', 'ledger', 'helper', 'readme', 'direct.tex', 'pinned-', 'scan', 'snapshot', 'submissions', 'retention', 'retrieve', 'record_evidence', 'validation', 'invocation', 'checkpoint-output', 'journal', 'status', 'progress', 'final', 'report', 'handoff', 'disposition', 'integrity', 'checkpoint', 'contribution', 'proof-role', 'review', 'check', 'freeze', 'summary', 'rights', 'reading-limits', 'prepare.py']
def excluded(rel):
 s=rel.lower().replace('\\','/')
 if s==OWN or s.startswith(OWN+'/'): return True
 if any(fnmatch.fnmatchcase(s,p) for p in PATTERNS): return True
 if any(x in ('.git','node_modules','dependencies','__pycache__','.venv') for x in s.split('/')): return True
 if 'ten-findings' in s or 'new-ten' in s or 'terminal-summary' in s or re.search(r'screen(?:-|[0-9])',s): return True
 if re.search(r'proof-r[0-9]',s): return True
 # Coarse substring protection knowingly omits genuine authored files too.
 return any(x in s for x in ROLES)
def walk():
 for base,ds,fs in os.walk(ROOT,topdown=True,followlinks=False):
  rel=Path(base).relative_to(ROOT)
  ds[:]=sorted(d for d in ds if not (Path(base)/d).is_symlink() and not excluded((rel/d).as_posix()))
  for n in sorted(fs):
   p=Path(base)/n; q=p.relative_to(ROOT).as_posix()
   if p.is_symlink() or excluded(q): continue
   yield q,p
