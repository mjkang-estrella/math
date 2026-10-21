import os,re,json,fnmatch
from pathlib import Path
ROOT=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
OUT=ROOT/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r118/packet/private'
patterns=['*structural*r152*','*analytic*r147*','*structural*r153*','*analytic*r148*','*arithmetic*r118*']
patterns += ['*arithmetic*r%d*'%n for n in range(107,118)]
patterns += ['*structural*r%d*'%n for n in range(143,152)]
patterns += ['*analytic*r%d*'%n for n in range(135,145)]+['*analytic*r146*']
patterns += ['*h138-*','*t185r144-*','*t177c143-*','*t373e135-*','*k369r134-*','*t088p133-*']
categories='corpus/source/primary/history-derivative/search/inventory/fixture/control/extract/render/vendor/build/copy/frozen/role/formal/manuscript/release/parent/private/input/upstream/shortlist/context/fetched/scratch/preprint/catalogue/catalog/receipt/brief/intake/bundle/recovery/manifest/authentication/task/work/family-title/literature/venv/site-packages/packet/payload/archive/cache/download/external/third-party/hits/index/navigation/audit/log/provenance/evidence/ledger/helper/README/direct.tex/pinned-/scan/snapshot/history-screen/history-broad/check.out/prior_check/verify.py/check.py/summary/progress/reading-metadata/capture/seal'.lower().split('/')
# Extra prospective aliases from the required r117 disclosure.
categories += ['sawin-2018','tao-teravainen-2019','expanded-history','.git','node_modules','__pycache__']
def denied(rel):
 s=str(rel).lower()
 return any(fnmatch.fnmatchcase(s,p) for p in patterns) or any(t in part for part in rel.parts for t in categories)
rx=re.compile(r'Milne|Milnes|speciali[sz].{0,55}(Hodge|cycle)|Hodge.{0,55}(speciali|CM abelian)|rationality conjecture|absolute Hodge|numerical motives|Chow.{0,40}(idempotent|nilpoten)',re.I)
omit=[];errors=[];hits=[];read=0;stack=[ROOT]
while stack:
 d=stack.pop()
 for e in sorted(os.scandir(d),key=lambda e:e.name):
  p=Path(e.path);rel=p.relative_to(ROOT)
  if denied(rel):omit.append(str(rel));continue
  if e.is_symlink():errors.append([str(rel),'symlink omitted']);continue
  if e.is_dir(follow_symlinks=False):stack.append(p);continue
  if not e.is_file(follow_symlinks=False):errors.append([str(rel),'nonregular omitted']);continue
  try:s=p.read_text(encoding='utf8')
  except (UnicodeError,OSError) as ex:errors.append([str(rel),type(ex).__name__]);continue
  read+=1
  matches=[{'line':i,'text':l} for i,l in enumerate(s.splitlines(),1) if rx.search(l)]
  if matches:hits.append({'path':str(rel),'matches':matches})
(OUT/'history-hits.json').write_text(json.dumps(hits,ensure_ascii=False,indent=2))
(OUT/'history-omissions.json').write_text(json.dumps({'patterns':patterns,'categories':categories,'omissions':omit,'errors':errors,'files_scanned':read},indent=2))
print('scanned',read,'omissions',len(omit),'errors',len(errors),'hit files',len(hits))
for h in hits:
 print(h['path'])
 for m in h['matches'][:3]:print(str(m['line'])+': '+m['text'][:450])
