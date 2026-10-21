"""Bounded authored-history navigation. No source bodies; no file-size cutoff."""
from pathlib import Path
import os,re,json,hashlib
ROOT=Path(__file__).resolve().parent
PROJECT=ROOT.parents[3]
ACTIVE=re.compile(r'(structural.*r14[34]|arithmetic.*r10[789]|analytic.*r13[5-8]|t185r144|t177c143|t373e135|k369r134|t088p133)',re.I)
ROLES=re.compile(r'(^|[_. -])(review\w*|parent|intake\w*|copy|copies|copied|corpus|inventor\w*|fixture\w*|control\w*|source\w*|primary|literature|history\w*|search\w*|catalogue\w*|paths?|snapshots?|context|recovery[-_]context|manifest\w*|validation|diagnostic\w*|replay\w*|work|render\w*|vendor|frozen|outside|formal\w*|manuscript\w*|release\w*|publication\w*|payload|inputs?|originals?|extract\w*|downloads?|exports?|archives?|bundles?|evidence|support|private|scratch|tmp|temp|build|cache|brief\w*|prompt\w*|dispatch\w*|task\w*|receipt\w*|audit\w*|node_modules)([_. -]|$)',re.I)
QUERY=re.compile(r'harmonic.{0,45}(dimension|growth)|integer.degree.{0,35}harmonic|Yau.{0,25}(dimension|growth)|floquet|log.periodic|\bsource\s*361\b|\bT361',re.I)

def reject(name):
 if ACTIVE.search(name): return 'explicit-isolation'
 if ROLES.search(name): return 'role'
 if name in {'.git','.venv','__pycache__'}: return 'generated'
 nums=re.findall(r'(?:^|[-_])r(\d+)(?:[-_.]|$)',name,re.I)
 if any(int(n)>=125 for n in nums): return 'coarse-recent'
 return None

if __name__=='__main__':
 hits=[];admitted=[];omissions=[]
 # Do not descend unknown campaigns; only historical numbered discovery roots.
 starts=[PROJECT/x for x in ['proposals','findings','experiments','notes','frontier/iterations','frontier/experiments','frontier/proposals','frontier/scouts','frontier/notes','frontier/findings']]
 camp=PROJECT/'frontier/campaigns/2026-10-14'
 for q in camp.iterdir():
  if not q.is_dir() or q.is_symlink(): continue
  reason=reject(q.name)
  if reason: omissions.append([str(q.relative_to(PROJECT)),reason]);continue
  if re.search(r'(?:^|[-_])r\d+(?:[-_]|$)',q.name) and ('discovery' in q.name or 'analytic' in q.name): starts.append(q)
  else: omissions.append([str(q.relative_to(PROJECT)),'unknown-campaign-omitted'])
 for start in starts:
  if not start.exists(): continue
  for base,dirs,files in os.walk(start,topdown=True,followlinks=False):
   keep=[]
   for name in sorted(dirs):
    p=Path(base)/name; reason=reject(name)
    if p.is_symlink(): reason='symlink'
    if reason: omissions.append([str(p.relative_to(PROJECT)),reason])
    else: keep.append(name)
   dirs[:]=keep
   for name in sorted(files):
    p=Path(base)/name; rel=str(p.relative_to(PROJECT)); reason=reject(name)
    if reason or p.is_symlink(): continue
    b=p.read_bytes()
    if b'\x00' in b: continue
    try: s=b.decode('utf-8')
    except UnicodeDecodeError: continue
    admitted.append({'path':rel,'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
    m=[{'line':i,'text':l} for i,l in enumerate(s.splitlines(),1) if QUERY.search(l)]
    if m: hits.append({'path':rel,'hits':m})
 out={'query':QUERY.pattern,'active':ACTIVE.pattern,'roles':ROLES.pattern,'admitted':admitted,'omissions':omissions,'hits':hits}
 (ROOT/'private/history-search.json').write_text(json.dumps(out,indent=2))
 print('admitted',len(admitted),'hit_files',len(hits),'pruned',len(omissions))
 for h in hits:
  print(h['path'])
  for m in h['hits'][:3]: print(' ',m['line'],m['text'][:400])
