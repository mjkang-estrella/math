from pathlib import Path
import fnmatch, os, json, hashlib, re
ROOT=Path.cwd()
OWN=ROOT/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r114'
ACTIVE=['*structural*r149*','*analytic*r144*','*structural*r150*','*analytic*r145*']
OLDER=[f'*arithmetic*r{i}*' for i in range(107,114)]+[f'*analytic*r{i}*' for i in range(135,144)]+[f'*structural*r{i}*' for i in range(143,149)]+['*h138-*','*t185r144-*','*t177c143-*','*t373e135-*','*k369r134-*','*t088p133-*']
CATEGORIES=['corpus','source','primary','history-derivative','search','inventory','fixture','control','extract','render','vendor','build','copy','copied','frozen','role','formal','manuscript','release','parent','private','input','upstream','shortlist','context','fetched','scratch','preprint','catalogue','receipt','brief','intake','bundle','recovery']
# Conservative additional aliases for derivatives, with deliberate coarse omissions.
ALIASES=['literature','archive-copy','snapshot','verification','family-map','history.json','history-reads','history-hits','baseline','node_modules','.git','.venv','__pycache__']
PATTERNS=ACTIVE+OLDER+['*'+s+'*' for s in CATEGORIES+ALIASES]+['*fresh-arithmetic-discovery-r114*']
RX=re.compile(r'character.variet|integral.points.on.character|Litt.{0,50}(integral|density)|potential.{0,20}integral.{0,20}density|arithmetic.local.system|multiplicative.quiver',re.I)
def excluded(name):
    return next((p for p in PATTERNS if fnmatch.fnmatchcase(name.lower(),p)),None)
rows=[]; omissions=[]; errors=[]; scanned=0
# First project traversal: top-down, reject components before descent or body selection.
for base, dirs, files in os.walk(ROOT,topdown=True,followlinks=False):
    keep=[]
    for name in dirs:
        reason=excluded(name)
        p=Path(base)/name
        if reason or p.is_symlink(): omissions.append([str(p.relative_to(ROOT)),reason or 'symlink'])
        else: keep.append(name)
    dirs[:]=keep
    for name in files:
        reason=excluded(name); p=Path(base)/name
        if reason or p.is_symlink():
            omissions.append([str(p.relative_to(ROOT)),reason or 'symlink']); continue
        try: raw=p.read_bytes(); s=raw.decode('utf-8')
        except (OSError,UnicodeDecodeError) as e: errors.append([str(p.relative_to(ROOT)),type(e).__name__]); continue
        scanned+=1
        hits=[[i,line] for i,line in enumerate(s.splitlines(),1) if RX.search(line)]
        if hits: rows.append({'path':str(p.relative_to(ROOT)),'size':len(raw),'sha256':hashlib.sha256(raw).hexdigest(),'hits':hits})
for name,obj in [('hits.json',rows),('scan-receipt.json',dict(root=str(ROOT),patterns=PATTERNS,regex=RX.pattern,utf8_bodies=scanned,omissions=omissions,errors=errors,limits='Coarse omissions may hide original authored history. No size, hidden-file, ignored-file or JSON exclusion. Not exhaustive isolation or novelty clearance.'))]:
    (OWN/'packet/private/search'/name).write_text(json.dumps(obj,indent=2)+'\n')
print(json.dumps({'utf8_bodies':scanned,'omissions':len(omissions),'errors':len(errors),'hit_files':len(rows),'hits':[{k:r[k] for k in ('path','size')} for r in rows]},indent=2))
