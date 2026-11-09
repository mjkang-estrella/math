from pathlib import Path
import json,os,fnmatch,re,time,hashlib
R=Path(__file__).resolve().parent
g=json.loads((R/'private/guards.json').read_text())
def blocked(p):
 s=p.as_posix().casefold()
 return any(t in s for t in g['substrings']) or any(fnmatch.fnmatchcase(s,t) for t in g['wildcards']+g['additional_derivative_wildcards']) or p==R or R in p.parents
qs={
'einstein-four-blocks':r'einstein[\s-]+(?:four|4)[\s-]*(?:dimensional|manifold)[^\n]{0,130}(?:weyl|coupl|sectional|compact)',
'weyl-coupling':r'(?:weyl[\s-]+(?:block|norm)s?[^\n]{0,90}(?:coupl|hessian|einstein))|(?:einstein[^\n]{0,90}weyl[^\n]{0,40}coupl)',
'zero-plane':r'zero[\s-]+plane[\s-]+rigidity',
'ricci-L2':r'(?:trace[\s-]+free[\s-]+ricci[^\n]{0,90}(?:L\s*\^?\s*\{?2|energy|gap))|(?:L\s*\^?\s*\{?2[^\n]{0,50}einstein[\s-]+gap)',
'sectional-boundary':r'sectional[\s-]+(?:curvature[\s-]+)?cone[^\n]{0,100}(?:boundary|equality)',
'spectral-hessian':r'einstein[^\n]{0,60}spectral[^\n]{0,60}hessian',
'nonnegative-topology':r'nonnegative[\s-]+curvature[^\n]{0,60}topological[\s-]+gap',
'moving-curvature-tail':r'(?:moving[\s-]+threshold|high[\s-]+curvature[\s-]+(?:part|tail))[^\n]{0,100}(?:ricci|curvature|sobolev)',
'weighted-weyl-hessian':r'weighted[\s-]+hessian[^\n]{0,80}weyl',
'Bianchi-highest-type':r'(?:bianchi[^\n]{0,60}(?:gradient|hessian)[^\n]{0,60}(?:spin|type))',
'Einstein-distance':r'(?:almost[\s-]+einstein|einstein[\s-]+defect)[^\n]{0,120}(?:distance|gromov|stability|ricci[\s-]+flow)'}
rx={k:re.compile(v,re.I) for k,v in qs.items()}
admin=re.compile(r'provenance|status|scope.and.evidence|contribution.screen|disposition|handoff|acceptance|campaign|reading|audit|inventory|shortlist|comparison.screen',re.I)
hd=re.compile(r'^(#{1,6})\s+(.+)$|^\\((?:sub)*section)\*?\{([^}]+)\}',re.M)
counts={'eligible_utf8':0,'binary_or_nonutf8':0,'pruned_dirs':0,'pruned_files':0,'noheading_hits':0,'administrative_hits':0};hits=[];t=time.monotonic()
# One prospective traversal only, prune before descent and before any bytes/decode.
for base,dirs,files in os.walk('frontier',topdown=True,followlinks=False):
 if time.monotonic()-t>90:raise RuntimeError('bounded navigation exceeded 90s')
 keep=[]
 for d in dirs:
  p=Path(base)/d
  if blocked(p) or p.is_symlink():counts['pruned_dirs']+=1
  else:keep.append(d)
 dirs[:]=keep
 for name in files:
  p=Path(base)/name
  if blocked(p) or p.is_symlink():counts['pruned_files']+=1;continue
  b=p.read_bytes()
  try:s=b.decode('utf-8')
  except UnicodeDecodeError:counts['binary_or_nonutf8']+=1;continue
  if '\x00' in s:counts['binary_or_nonutf8']+=1;continue
  counts['eligible_utf8']+=1
  matches=[(m.start(),m.end(),key) for key,rr in rx.items() for m in rr.finditer(s)]
  if not matches:continue
  hs=[]
  for h in hd.finditer(s):hs.append((h.start(),len(h[1]) if h[1] else 1+h[3].count('sub'),h[2] or h[4]))
  for x,y,key in matches:
   before=[h for h in hs if h[0]<=x]
   if not before:counts['noheading_hits']+=1;continue
   start,level,title=before[-1]
   end=next((q[0] for q in hs if q[0]>start and q[1]<=level),len(s))
   if admin.search(title):counts['administrative_hits']+=1;continue
   # Headings only: no original mathematical body is displayed at this stage.
   item={'path':p.as_posix(),'heading':title,'level':level,'query':key,'char_extent':[start,end],'bytes':[len(s[:start].encode()),len(s[:end].encode())],'file_sha256':hashlib.sha256(b).hexdigest()}
   if item not in hits:hits.append(item)
out={'counts':counts,'candidate_headings':hits,'queries':qs,'limits':'One pruned traversal; no inherited/peer bodies; no-heading and administrative matches not displayed. Coarse omissions and opaque false admissions possible, no exhaustive clearance.'}
(R/'private/original-navigation.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
