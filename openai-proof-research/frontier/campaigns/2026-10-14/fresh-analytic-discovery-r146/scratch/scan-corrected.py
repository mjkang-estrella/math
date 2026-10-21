from pathlib import Path
import os,fnmatch,json,re,hashlib
ROOT=Path.cwd(); OUT=ROOT/'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r146'
patterns=['*structural*r151*','*arithmetic*r116*','*structural*r152*','*arithmetic*r117*']
patterns += [f'*analytic*r{x}*' for x in range(135,146)]
patterns += [f'*structural*r{x}*' for x in range(143,151)]
patterns += [f'*arithmetic*r{x}*' for x in range(107,116)]
patterns += ['*h138-*','*t185r144-*','*t177c143-*','*t373e135-*','*k369r134-*','*t088p133-*']
categories='corpus source primary history-derivative search inventory fixture control extract render vendor build copy frozen role formal manuscript release parent private input upstream shortlist context fetched scratch preprint catalogue catalog receipt brief intake bundle recovery manifest authentication task work family-title literature venv site-packages packet payload archive cache download external third-party hits index navigation audit log provenance evidence ledger helper README direct.tex pinned- scan snapshot submissions retention retrieve record_evidence'.lower().split()
patterns += ['*'+x+'*' for x in categories]
patterns += ['*history*','.git','node_modules','fresh-analytic-discovery-r146']
def blocked(name): return any(fnmatch.fnmatchcase(name.lower(),p) for p in patterns)
rx=re.compile(r'defocusing|(?:source|T|I)[ _-]?371\b|\bNLS\b|Madelung|quantum.pressure|multi[ -]bubble|Schr[oö]dinger',re.I)
counts=dict(pruned=0,symlinks=0,non_utf8=0,nul=0,eligible=0,errors=0)
hits=[]; skipped=[]
for base,dirs,files in os.walk(ROOT,topdown=True,followlinks=False):
    kept=[]
    for name in dirs:
        p=Path(base)/name
        if blocked(name): counts['pruned']+=1
        elif p.is_symlink(): counts['symlinks']+=1
        else: kept.append(name)
    dirs[:]=kept
    for name in files:
        p=Path(base)/name
        if blocked(name): counts['pruned']+=1; continue
        if p.is_symlink(): counts['symlinks']+=1;continue
        rel=str(p.relative_to(ROOT))
        try: b=p.read_bytes()
        except OSError as e: counts['errors']+=1;skipped.append([rel,str(e)]);continue
        if b'\0' in b: counts['nul']+=1;skipped.append([rel,'NUL']);continue
        try: s=b.decode('utf-8')
        except UnicodeDecodeError: counts['non_utf8']+=1;skipped.append([rel,'non-UTF8']);continue
        counts['eligible']+=1
        matches=[[i,l] for i,l in enumerate(s.splitlines(),1) if rx.search(l)]
        if matches: hits.append(dict(path=rel,size=len(b),sha256=hashlib.sha256(b).hexdigest(),matches=matches))
record=dict(patterns=patterns,regex=rx.pattern,counts=counts,skipped=skipped,hits=hits)
(OUT/'private/history-scan-corrected.json').write_text(json.dumps(record,indent=2,ensure_ascii=False)+'\n')
print(json.dumps(counts)); print('matching files',len(hits),'lines',sum(len(x['matches']) for x in hits))
for x in hits: print(x['path'],len(x['matches']))
