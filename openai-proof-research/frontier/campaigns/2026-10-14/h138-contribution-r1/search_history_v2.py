"""Bounded authored-history search. No writes outside this assigned review root."""
from pathlib import Path
import os,re,json,hashlib
R=Path(__file__).resolve().parent
P=R.parents[3]
assert P.name=='openai-proof-research'
peer=re.compile(r'h138[-_]|t185r144|structural.*r144|arithmetic.*r10[89]|arithmetic.*r110|analytic.*r13[5-8]|arithmetic.*r107|structural.*r143|t177c143|t373e135|k369r134|t088p133',re.I)
role=re.compile(r'(?:^|[-_. ])(?:review\w*|contribution\w*|peer\w*|parent\w*|intake\w*|brief\w*|tasks?|cop(?:y|ied|ies)\w*|frozen\w*|inputs?|sources?|primary|originals?|history\w*|replay\w*|release\w*|formal\w*|manuscript\w*|corpus\w*|controls?|private|roles?|snapshots?|archives?|validation\w*|manifests?|seal\w*|verif\w*|ledgers?|catalog\w*|inventor\w*|context\w*|recovery\w*|publication\w*|permissions?)(?:$|[-_. ])',re.I)
proofrole=re.compile(r'(?:^|[-_])proof(?:[-_]r\d+|$)',re.I)
extra=re.compile(r'source[0-9]|primary[0-9]|payload|packet|(?:^|[-_. ])(?:public|work|scratch|vendor|search\w*|paths?|pinned\w*|acceptance\w*|accepted\w*|retention\w*|audit\w*|diagnostic\w*|evidence\w*|receipts?|register\w*|preflight\w*|prepare\w*|reproduce\w*|support\w*|fixtures?|tamper\w*|build|output|downloads?|extract\w*|cache)(?:$|[-_. ])',re.I)
needle=re.compile(r'harmonic|Source\s*361|spectral[- ]flag|triangular[- ]lift|retained[- ]double|inward.{0,40}graph|full[- ]leg|integer[- ]degree|three[- ]circles|volume[- ]ratio|graph[- ]transform|fixed[- ]cutoff|nonuniform[- ]contraction',re.I)
roots=['proposals','findings','experiments','notes','frontier/campaigns','frontier/iterations','frontier/experiments','frontier/proposals','frontier/scouts','frontier/notes','frontier/findings']
def bad(name):return bool(peer.search(name) or role.search(name) or proofrole.search(name) or extra.search(name) or name in {'.git','node_modules','.venv','venv','__pycache__'})
seen=set();admitted=[];pruned=[];hits=[];fail=[];skipped=[]
for rel in roots:
 root=P/rel
 if not root.is_dir():continue
 for base,ds,ns in os.walk(root,topdown=True,followlinks=False):
  ds.sort();ns.sort()
  keep=[]
  for n in ds:
   q=Path(base)/n
   if bad(n) or q.is_symlink():pruned.append(str(q.relative_to(P)))
   else:keep.append(n)
  ds[:]=keep
  for n in ns:
   q=Path(base)/n;path=str(q.relative_to(P))
   if path in seen:continue
   seen.add(path)
   if any(bad(x) for x in q.relative_to(P).parts) or q.is_symlink():pruned.append(path);continue
   try:
    b=q.read_bytes()
    if b'\0' in b:skipped.append({'path':path,'reason':'NUL/binary'});continue
    s=b.decode('utf8')
   except (OSError,UnicodeError) as e:fail.append({'path':path,'error':str(e)});continue
   rec={'path':path,'size':len(b),'sha256':hashlib.sha256(b).hexdigest()};admitted.append(rec)
   matches=[{'line':i,'text':l} for i,l in enumerate(s.splitlines(),1) if needle.search(l)]
   if matches:hits.append(dict(rec,matches=matches))
out={'roots':roots,'peer_regex':peer.pattern,'role_regex':role.pattern,'proofrole_regex':proofrole.pattern,'extra_regex':extra.pattern,'needle':needle.pattern,'admitted':admitted,'pruned':pruned,'hits':hits,'failures':fail,'skipped':skipped,'limits':'Authored listed roots only; all matching role components/flat filenames omitted even if genuine original. UTF8 only, hidden/ignored/JSON/large files included without size limit. No unrelated root or derivative body clearance.'}
(R/'private/history-search-v2.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'admitted':len(admitted),'pruned':len(pruned),'hit_files':len(hits),'failures':len(fail),'binary':len(skipped)}))
for h in hits:
 if any(re.search(r'Source\s*361|retained[- ]double|integer[- ]degree|inward.{0,40}graph|spectral[- ]flag|triangular[- ]lift|fixed[- ]metric.{0,30}harmonic',x['text'],re.I) for x in h['matches']):print(h['path'],len(h['matches']))
