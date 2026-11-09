import os,re,json,hashlib,importlib.util
from pathlib import Path
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r210')
spec=importlib.util.spec_from_file_location('guards',R/'guards.py');G=importlib.util.module_from_spec(spec);spec.loader.exec_module(G)
roots=['frontier/campaigns','frontier/iterations','frontier/experiments','frontier/proposals','frontier/scouts','frontier/notes','frontier/findings']
queries=[r'smooth\s+local\s+isometric\s+non[- ]?immersion',r'flat[- ]jet\s+metric\s+obstruction',r'surface\s+Gauss[-– ]Codazzi\s+obstruction',r'three[- ]space\s+nonreali[sz]ability',r'accumulating\s+metric\s+pulses',r'Nadirashvili',r'Pogorelov',r'Darboux.{0,50}(?:height|equation|obstruction)',r'local\s+isometric\s+(?:immersion|embedding|reali[sz]ation)',r'cap\s+regularity',r'curvature\s+drift',r'boundary[- ]saddle',r'oscillatory\s+(?:metric\s+)?pulse']
Q=re.compile('|'.join('(?:'+q+')' for q in queries),re.I)
admin=re.compile(r'(?i)(status|provenance|scope.and.evidence|contribution.?screen|administrat|disposition|acceptance|handoff|summary|source.?map|source.?read|navigation|reading.?log|evidence|catalog|shortlist)')
heading=re.compile(r'(?m)^(#{1,6})\s+(.+)$|^\\(part|chapter|section|subsection|subsubsection)\*?\{([^\n]*)\}')
out=[];stats={'eligible_utf8_files':0,'invalid_utf8_files':0,'pruned_entries':0,'symlinks_skipped':0,'roots':{},'bytes_read':0}
seen=set()
for root in roots:
 if G.denied(root):stats['roots'][root]='pruned before descent';continue
 if not Path(root).is_dir():stats['roots'][root]='exact root absent';continue
 stats['roots'][root]='guarded traversal'
 for base,dirs,files in os.walk(root,topdown=True,followlinks=False):
  keep=[]
  for n in dirs:
   p=Path(base,n);rel=p.as_posix()
   if G.denied(rel):stats['pruned_entries']+=1
   elif p.is_symlink():stats['symlinks_skipped']+=1
   else:keep.append(n)
  dirs[:]=keep
  for n in files:
   p=Path(base,n);rel=p.as_posix()
   if G.denied(rel):stats['pruned_entries']+=1;continue
   if p.is_symlink():stats['symlinks_skipped']+=1;continue
   if rel in seen:continue
   seen.add(rel);b=p.read_bytes();stats['bytes_read']+=len(b)
   try:s=b.decode('utf8')
   except UnicodeDecodeError:stats['invalid_utf8_files']+=1;continue
   stats['eligible_utf8_files']+=1
   matches=list(Q.finditer(s))
   if not matches:continue
   hs=[]
   for m in heading.finditer(s):
    level=len(m[1]) if m[1] else {'part':1,'chapter':1,'section':2,'subsection':3,'subsubsection':4}[m[3]]
    hs.append((m.start(),level,m[2] or m[4]))
   for m in matches:
    prior=[h for h in hs if h[0]<=m.start()]
    if prior:
     h=prior[-1];start=h[0];end=next((x[0] for x in hs if x[0]>start and x[1]<=h[1]),len(s));title=h[2]
    else:start=0;end=hs[0][0] if hs else len(s);title='[unheaded; requires manual classification]'
    record={'path':rel,'heading':title,'bytes_start':len(s[:start].encode()),'bytes_end':len(s[:end].encode()),'classification':'reject administrative' if admin.search(title) else 'candidate only; no body displayed','file_sha256':hashlib.sha256(b).hexdigest()}
    if record not in out:out.append(record)
(R/'private/history-candidates.json').write_text(json.dumps({'queries':queries,'stats':stats,'candidates':out,'limits':'Full-relative path guards applied before descent and before bytes/decode. No size/extension/hidden cutoff. No claim of exhaustive clearance: coarse substrings exclude originals; opaque aliases can escape. Candidate headings only displayed; no original mathematical section yet selected.'},indent=2)+'\n')
print(json.dumps(stats,indent=2));print(json.dumps(out,indent=2))
