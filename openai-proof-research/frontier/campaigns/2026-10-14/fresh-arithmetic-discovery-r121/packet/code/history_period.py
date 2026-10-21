import os, fnmatch, json, re, hashlib
from pathlib import Path
ROOT=Path.cwd()
OWN=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r121')
ROUND_PATTERNS=[
 '*structural*r155*','*analytic*r149*','*structural*r156*','*analytic*r150*','*t360s147*',
 '*arithmetic*r120*','*arithmetic*r119*','*arithmetic*r118*','*arithmetic*r117*','*arithmetic*r116*','*arithmetic*r115*','*arithmetic*r114*','*arithmetic*r113*','*arithmetic*r112*','*arithmetic*r111*','*arithmetic*r110*','*arithmetic*r109*','*arithmetic*r108*',
 '*analytic*r148*','*analytic*r147*','*analytic*r146*','*analytic*r145*','*analytic*r144*','*analytic*r143*','*analytic*r142*','*analytic*r141*','*analytic*r140*','*analytic*r139*','*analytic*r138*','*analytic*r137*','*analytic*r136*',
 '*structural*r154*','*structural*r153*','*structural*r152*','*structural*r151*','*structural*r150*','*structural*r149*','*structural*r148*','*structural*r147*','*structural*r146*','*structural*r145*','*structural*r144*',
 '*h138-*','*t185r144-*','*t177c143-*','*t373e135-*','*k369r134-*','*t088p133-*',
 '*arithmetic*r121*']
CATEGORIES='corpus source primary history-derivative search inventory fixture control extract render vendor build copy copied frozen role formal manuscript release parent private input upstream shortlist context fetched scratch preprint catalogue catalog receipt brief intake bundle recovery manifest authentication task work family-title literature venv site-packages packet payload archive cache download external third-party hits index navigation audit log provenance evidence ledger helper readme direct.tex pinned- scan snapshot submissions retention retrieve record_evidence validation invocation checkpoint-output journal status progress final report disposition integrity checkpoint capture findings.md'.split()
PATTERNS=ROUND_PATTERNS+['*'+x+'*' for x in CATEGORIES]+['.git','*/.git/*','*new-ten-2026-10-14.md*','*twenty-findings*','*ten-findings*']
def excluded(path):
 s=path.as_posix().lower()
 return any(fnmatch.fnmatchcase(s,p) for p in PATTERNS)
def walk():
 omissions=[]; errors=[]; admitted=[]; hits=[]
 pattern=re.compile(r'Porowski|Kodaira.Parshin|Chabauty|Betts.Stix|Galois.{0,25}period',re.I)
 for base,dirs,files in os.walk(ROOT,topdown=True,followlinks=False):
  rel=Path(base).relative_to(ROOT)
  keep=[]
  for d in dirs:
   p=rel/d
   if excluded(p) or (ROOT/p).is_symlink(): omissions.append(str(p))
   else: keep.append(d)
  dirs[:]=keep
  for f in files:
   p=rel/f
   if excluded(p) or (ROOT/p).is_symlink(): omissions.append(str(p));continue
   try: data=(ROOT/p).read_bytes(); txt=data.decode('utf8')
   except (OSError,UnicodeError) as e: errors.append({'path':str(p),'error':type(e).__name__});continue
   admitted.append({'path':str(p),'size':len(data),'sha256':hashlib.sha256(data).hexdigest()})
   found=[{'line':i,'text':line} for i,line in enumerate(txt.splitlines(),1) if pattern.search(line)]
   if found: hits.append({'path':str(p),'matches':found})
 out={'pattern':pattern.pattern,'admitted':admitted,'omissions':omissions,'errors':errors,'hits':hits}
 (ROOT/OWN/'packet/private/history-screen-3.json').write_text(json.dumps(out,indent=2))
 print(json.dumps({'admitted':len(admitted),'omissions':len(omissions),'errors':len(errors),'hit_files':len(hits)}))
 for h in hits:
  print(h['path'])
  for m in h['matches'][:4]: print(str(m['line'])+': '+m['text'][:1200])
if __name__=='__main__':walk()
