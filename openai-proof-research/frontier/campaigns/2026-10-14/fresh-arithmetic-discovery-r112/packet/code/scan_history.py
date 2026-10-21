"""Bounded-scope authored-history search; exclusions precede descent/selection."""
from pathlib import Path
import os, re, fnmatch, json, hashlib
ROOT=Path(__file__).resolve().parents[1]
PROJECT=ROOT.parents[4]
FORBIDDEN=['*structural*r148*','*analytic*r142*','*analytic*r140*','*structural*r146*','*analytic*r141*','*structural*r147*','*h138-*','*t185r144-*','*arithmetic*r112*','*arithmetic*r111*','*arithmetic*r110*','*arithmetic*r109*','*arithmetic*r108*','*arithmetic*r107*','*analytic*r139*','*analytic*r138*','*structural*r145*','*structural*r144*','*structural*r143*','*t177c143-*','*analytic*r137*','*analytic*r136*','*analytic*r135*','*t373e135-*','*k369r134-*','*t088p133-*']
ROLE=re.compile(r'(?:fetch|download|retrieve|task|dispatch|runner|handoff|terminal|transcript|session|metadata|receipt|ledger|journal|index|summary|requirements|seal|verify|validation|checksum|hash|final\.json|contribution|manifest|family.titles|task\.json|read\.py|finalize|checks.receipt|corpus|source|primary|history|search|inventor|fixture|control|extract|render|vendor|build|cop(?:y|ies)|frozen|role|formal|manuscript|release|parent|brief|intake|input|private|context|preprint|upstream|catalog|canonical|acquisition|literature|audit|adversarial|prepare|provenance|payload|snapshot|mirror|evidence|review|proof-r|publication|package|\.venv|venv|site-packages|node_modules|\.git|__pycache__|\.cache)',re.I)
# Coarse extra omission: all numbered discovery rounds >=100, whether complete or active.
def blocked(name):
 n=name.lower()
 if any(fnmatch.fnmatchcase(n,x) for x in FORBIDDEN):return True
 if ROLE.search(n):return True
 return bool(re.search(r'(?:discovery|analytic|arithmetic|structural).*r(?:[1-9]\d{2,})(?:\D|$)',n))
PAT=re.compile(r'Ciliberto|Dumnicki|theta.{0,24}(?:diagram|interpolat)|homogeneous.{0,25}(?:postulation|linear system)|W136|U142|Nagata|Seshadri|fat.point|SHGH|Segre.Harbourne|Harbourne.Hirschowitz|Waldschmidt|Cremona|symbolic.{0,25}(?:regularity|resurgence)|(?:source|family)[ -]?0?39\b',re.I)
read=[];omitted=[];hits=[]
for name in ['campaigns','iterations','experiments','proposals','scouts','notes','findings']:
 base=PROJECT/'frontier'/name
 if not base.exists():continue
 for directory,dirs,files in os.walk(base,followlinks=False):
  kept=[]
  for d in sorted(dirs):
   f=Path(directory)/d
   if blocked(d) or f.is_symlink():omitted.append([str(f.relative_to(PROJECT)),'component']);continue
   kept.append(d)
  dirs[:]=kept
  for name in sorted(files):
   f=Path(directory)/name
   if blocked(name) or f.is_symlink():omitted.append([str(f.relative_to(PROJECT)),'file']);continue
   try:b=f.read_bytes();s=b.decode('utf-8')
   except (OSError,UnicodeError):omitted.append([str(f.relative_to(PROJECT)),'unreadable/nonUTF8']);continue
   if '\0' in s:omitted.append([str(f.relative_to(PROJECT)),'NUL']);continue
   rel=str(f.relative_to(PROJECT));read.append([rel,len(b),hashlib.sha256(b).hexdigest()])
   a=[{'line':i,'text':x} for i,x in enumerate(s.splitlines(),1) if PAT.search(x)]
   if a:hits.append({'path':rel,'matches':a})
receipt={'read':read,'omitted':omitted,'hits':hits,'limitations':'No size cutoff; hidden/ignored/JSON included. Coarse omissions; not exhaustive. Metadata snapshot only. Exclusion applies before directory descent and body selection.'}
(ROOT/'private/search/history039-mechanism.json').write_text(json.dumps(receipt,indent=2))
print('READ',len(read),'OMITTED',len(omitted),'HIT_FILES',len(hits))
for h in hits:print(h['path'],len(h['matches']))
