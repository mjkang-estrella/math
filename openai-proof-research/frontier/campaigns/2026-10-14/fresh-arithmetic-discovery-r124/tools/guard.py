"""Prospective top-down history guard. Run only from actual project root."""
from pathlib import Path
import fnmatch, os, re, json, hashlib
ROOT=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
OWN=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r124')
PATTERNS=['*structural*r158*','*analytic*r152*','*structural*r159*','*analytic*r153*','*t360s147*',
 '*arithmetic*r123*','*arithmetic*r122*','*arithmetic*r121*','*arithmetic*r120*','*arithmetic*r119*','*arithmetic*r118*','*arithmetic*r117*','*arithmetic*r116*','*arithmetic*r115*','*arithmetic*r114*','*arithmetic*r113*','*arithmetic*r112*','*arithmetic*r111*','*arithmetic*r110*',
 '*analytic*r151*','*analytic*r150*','*analytic*r149*','*analytic*r148*','*analytic*r147*','*analytic*r146*','*analytic*r145*','*analytic*r144*','*analytic*r143*','*analytic*r142*','*analytic*r141*','*analytic*r140*','*analytic*r139*','*analytic*r138*',
 '*structural*r157*','*structural*r156*','*structural*r155*','*structural*r154*','*structural*r153*','*structural*r152*','*structural*r151*','*structural*r150*','*structural*r149*','*structural*r148*','*structural*r147*','*structural*r146*',
 '*h138-*','*t185r144-*','*t177c143-*','*t373e135-*','*k369r134-*','*t088p133-*',
 '*new-ten*','*terminal-summary*','*summary.json*','*tasks.json*','*ten-findings*','*twenty-findings*','*second-history-screen*','*history-screen*','*history-broad-geometry*','*prepare.py*']
WORDS='corpus source primary history-derivative search inventory fixture control extract render vendor build copy copied frozen role formal manuscript release parent private input upstream shortlist context fetched scratch preprint catalogue catalog receipt brief intake bundle recovery manifest authentication task work family-title literature venv site-packages packet payload archive cache download external third-party hits index navigation audit log provenance evidence ledger helper readme direct.tex pinned- scan snapshot submissions retention retrieve record_evidence validation invocation checkpoint-output final report handoff disposition integrity checkpoint journal status progress'.split()
# Token matching is deliberately coarse. Aliases may remain opaque; no clearance claim.
TOKEN=re.compile(r'(^|[/_.-])(?:'+ '|'.join(re.escape(w) for w in WORDS)+r')',re.I)
def excluded(path):
 s=str(path).lower()
 if s==str(OWN) or s.startswith(str(OWN)+'/'):return 'own-root'
 if any(x in s.split('/') for x in ['.git','dependencies','node_modules','__pycache__','.venv']):return 'dependency'
 for pat in PATTERNS:
  if fnmatch.fnmatchcase(s,pat):return pat
 if TOKEN.search(s):return 'coarse-body-category'
 return None

def scan(query):
 assert Path.cwd()==ROOT
 rx=re.compile(query,re.I); admitted=[]; omitted=[];errors=[];hits=[]
 for parent,dirs,files in os.walk('.',topdown=True,followlinks=False):
  if parent=='.':
   allowed={'frontier','campaigns','iterations','experiments','proposals','scouts','notes','findings'}
   for n in dirs:
    if n not in allowed:omitted.append([n,'root-area-coarse-omission'])
   dirs[:]=[n for n in dirs if n in allowed]
  dirs.sort();files.sort()
  keep=[]
  for name in dirs:
   p=Path(parent)/name;why=excluded(p)
   if p.is_symlink():why='symlink'
   if why:omitted.append([str(p),why])
   else:keep.append(name)
  dirs[:]=keep
  for name in files:
   p=Path(parent)/name;why=excluded(p)
   if p.is_symlink():why='symlink'
   if why:omitted.append([str(p),why]);continue
   try:
    data=p.read_bytes();body=data.decode('utf-8')
   except (OSError,UnicodeError) as e:errors.append([str(p),type(e).__name__]);continue
   admitted.append({'path':str(p),'size':len(data),'sha256':hashlib.sha256(data).hexdigest()})
   matches=[{'line':i,'text':s} for i,s in enumerate(body.splitlines(),1) if rx.search(s)]
   if matches:hits.append({'path':str(p),'matches':matches})
 result={'query':query,'admitted':admitted,'omitted':omitted,'errors':errors,'hits':hits}
 (OWN/'private/history-screen-result.json').write_text(json.dumps(result,indent=2))
 print(json.dumps({'admitted':len(admitted),'omitted':len(omitted),'errors':len(errors),'hit_files':len(hits),'largest':max((x['size'] for x in admitted),default=0)}))
 for h in hits:
  print(h['path'])
  for m in h['matches'][:2]:print(str(m['line'])+': '+m['text'][:350])
if __name__=='__main__':
 import sys,signal
 signal.alarm(180)
 (OWN/'private/isolation.json').write_text(json.dumps({'patterns':PATTERNS,'coarse_words':WORDS,'own':str(OWN),'symlinks':'pruned','no_size_cutoff':True},indent=2))
 scan(sys.argv[1])
