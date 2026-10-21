"""Prospective exclusions; synthetic tests only when invoked without --scan."""
from pathlib import Path
import fnmatch, re, os, json, hashlib, sys
ROOT=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r131')
# Each round is an individual full-path wildcard predicate, not a range string.
PATTERNS=['*structural*r164*','*analytic*r159*','*structural*r165*','*analytic*r160*','*structural*r166*','*analytic*r161*','*structural*r161*','*t126s161*','*t360s147*','*arithmetic*r131*',
'*arithmetic*r130*','*arithmetic*r129*','*arithmetic*r128*','*arithmetic*r127*','*arithmetic*r126*','*arithmetic*r125*','*arithmetic*r124*','*arithmetic*r123*','*arithmetic*r122*','*arithmetic*r121*','*arithmetic*r120*','*arithmetic*r119*','*arithmetic*r118*','*arithmetic*r117*','*arithmetic*r116*','*arithmetic*r115*','*arithmetic*r114*','*arithmetic*r113*',
'*analytic*r158*','*analytic*r157*','*analytic*r156*','*analytic*r155*','*analytic*r154*','*analytic*r153*','*analytic*r152*','*analytic*r151*','*analytic*r150*','*analytic*r149*','*analytic*r148*','*analytic*r147*','*analytic*r146*','*analytic*r145*','*analytic*r144*','*analytic*r143*','*analytic*r142*','*analytic*r141*',
'*structural*r163*','*structural*r162*','*structural*r160*','*structural*r159*','*structural*r158*','*structural*r157*','*structural*r156*','*structural*r155*','*structural*r154*','*structural*r153*','*structural*r152*','*structural*r151*','*structural*r150*','*structural*r149*',
'*h138-*','*t185r144-*','*t177c143-*','*t373e135-*','*k369r134-*','*t088p133-*']
# No trailing boundary: sources, inputs, snapshots, ledgers, etc. are pruned.
WORDS='tools scripts checks search acquire screen corpus source primary history inventory fixture control extract render vendor build copy copied frozen role formal manuscript release parent private input upstream shortlist context fetched scratch preprint catalogue catalog receipt brief intake bundle recovery manifest authentication task work family-title literature venv site-packages packet payload archive cache download external third-party hits index navigation audit log provenance evidence ledger helper readme direct.tex pinned- scan snapshot submission retention retrieve record_evidence validation invocation checkpoint-output journal status progress final report handoff disposition integrity checkpoint new-ten terminal-summary summary.json ten-findings twenty-findings second-history-screen history-screen history-broad-geometry prepare.py dispatch integration retrieval metadata capture reproduction resume launch scout'.split()
ADMIN=re.compile(r'(?:^|[/_.\s-])(?:'+ '|'.join(re.escape(w) for w in WORDS)+')')
def deny(p):
 p=str(p).casefold().replace('\\','/')
 if p.endswith(('.py','.sh','.js','.mjs')):return 'coarse-program'
 if any(x in {'.git','node_modules','dependencies','dependency','.venv','__pycache__'} for x in p.split('/')):return 'dependency'
 if any(fnmatch.fnmatchcase(p,g) for g in PATTERNS):return 'round'
 if ADMIN.search(p):return 'coarse'
 return None

def tests():
 bad=['a/README.md','NEW-TEN-2026.md','TEN-FINDINGS.json','x/inputs/x','x/sources/x','x/snapshots/x','x/ledgers/x','x/tasks.json','x/summary.json','x/prepare.py','x/second-history-screen/a','x/history-broad-geometry/a','x/DISPATCH-arithmetic-r131.md','x/INTEGRATION/arithmetic-foo-r131.md','.git/objects/a','dependencies/x','a/structural-parent-R164-note.md','a/ANALYTIC-brief-R159.md','a/structural-copy-r165-parent','a/analytic-r160','a/STRUCTURAL-r166','a/analytic-r161','a/t126s161-copy','a/t360s147-parent','a/structural-brief-R161.md','x/RETRIEVALS/a','x/captures/a','x/reproductions/a','x/resumes/a','x/launches/a','x/scouts/a']
 bad += [g.replace('*','x') for g in PATTERNS]
 assert all(deny(p) for p in bad),[p for p in bad if not deny(p)]
 good=['frontier/campaigns/2026-10-14/discovery-arithmetic-r100/notes/proof.md','frontier/experiments/alperin/calculation.json','.hidden/calculation.tex']
 assert all(not deny(p) for p in good)
 return {'synthetic_rejected':len(bad),'synthetic_admitted':len(good),'patterns':PATTERNS,'coarse_words':WORDS}
if __name__=='__main__':
 report=tests();print('Synthetic guard tests:',report['synthetic_rejected'],'rejected and',report['synthetic_admitted'],'admitted')
 if '--scan' in sys.argv:
  hits=[]; stats={'pruned_directories':0,'pruned_files':0,'utf8_files':0,'non_utf8_or_binary':0,'symlinks':0}; names=[]
  query=re.compile(r'alperin|\bbrauer\b|p.singular|Teichm.ll|puncture|tuple.divisi|cyclic.twist|marked.cover|mixed.moment',re.I)
  for base,ds,fs in os.walk('.',topdown=True,followlinks=False):
   kept=[]
   for d in ds:
    p=Path(base)/d
    if p.is_symlink():stats['symlinks']+=1
    elif deny(p.as_posix().removeprefix('./')):stats['pruned_directories']+=1
    else:kept.append(d)
   ds[:]=kept
   for f in fs:
    p=Path(base)/f; rel=p.as_posix().removeprefix('./')
    if p.is_symlink():stats['symlinks']+=1;continue
    if deny(rel):stats['pruned_files']+=1;continue
    data=p.read_bytes()
    try:
     if b'\0' in data:raise UnicodeError()
     s=data.decode('utf-8')
    except UnicodeError:stats['non_utf8_or_binary']+=1;continue
    stats['utf8_files']+=1
    lines=s.splitlines(); matches=[{'line':i+1,'text':l} for i,l in enumerate(lines) if query.search(l)]
    if matches:hits.append({'path':rel,'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest(),'matches':matches})
  (ROOT/'private/history/search-refined.json').write_text(json.dumps({'guards':report,'stats':stats,'hits':hits},indent=2)+'\n')
  print('SCAN STATS',stats,'matching files',len(hits))
  for h in hits:print(h['path'],len(h['matches']))
