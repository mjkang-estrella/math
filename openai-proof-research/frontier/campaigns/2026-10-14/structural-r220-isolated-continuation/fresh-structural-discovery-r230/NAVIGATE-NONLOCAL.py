from pathlib import Path
import os,re,json,hashlib,runpy
R=Path("frontier/campaigns/2026-10-14/structural-r220-isolated-continuation/fresh-structural-discovery-r230")
g=runpy.run_path(str(R/'GUARDS.py'));g['assert_guards']()
query=re.compile('(?:cubic[\\s\\S]{0,60}(?:torus|tori)[\\s\\S]{0,180}(?:nonlocal|coulomb)|(?:nonlocal|coulomb)[\\s\\S]{0,180}cubic[\\s\\S]{0,60}(?:torus|tori)|periodic[\\s_-]+(?:Coulomb|Ohta.Kawasaki)|Cristoferi.{0,80}periodic|(?:ball.tube|tube.slab).{0,80}(?:nonlocal|coulomb))',re.I)
admin=re.compile(r'screen|report|prior interfaces|read boundary|dependencies|status|provenance|scope.and.evidence|contribution.screen|receipt|manifest|handoff|administrat|campaign count|disposition|search results|source inventory',re.I)
roots=[Path(a)/b for a in ['frontier',''] for b in ['campaigns','iterations','experiments','proposals','scouts','notes','findings']]
seen=set();hits=[];stats={'pruned_dirs':0,'pruned_files':0,'eligible_files':0,'utf8_files':0,'non_utf8':0,'symlinks':0}
for root in roots:
 if g['excluded'](root.as_posix()) or not root.is_dir():continue
 for dp,ds,fs in os.walk(root,topdown=True,followlinks=False):
  kept=[]
  for n in ds:
   p=Path(dp)/n
   if p.is_symlink():stats['symlinks']+=1
   elif g['excluded'](p.as_posix()):stats['pruned_dirs']+=1
   else:kept.append(n)
  ds[:]=kept
  for n in fs:
   p=Path(dp)/n;rel=p.as_posix()
   if rel in seen:continue
   seen.add(rel)
   if g['excluded'](rel):stats['pruned_files']+=1;continue
   if p.is_symlink():stats['symlinks']+=1;continue
   stats['eligible_files']+=1
   try:b=p.read_bytes();s=b.decode('utf-8')
   except UnicodeDecodeError:stats['non_utf8']+=1;continue
   except OSError:continue
   stats['utf8_files']+=1
   if not query.search(s):continue
   lines=b.splitlines(keepends=True);off=0;headings=[];matches=[]
   for i,l in enumerate(lines,1):
    t=l.decode('utf8').rstrip('\r\n')
    hm=re.match(r'^(#{1,6})\s+(.+)',t)
    tm=re.match(r'\\(section|subsection|subsubsection)\*?\{([^}]*)\}',t)
    if hm:headings.append((i,off,len(hm[1]),hm[2]))
    elif tm:headings.append((i,off,{'section':1,'subsection':2,'subsubsection':3}[tm[1]],tm[2]))
    if query.search(t):matches.append((i,off))
    off+=len(l)
   sections=[]
   for i,o in matches:
    before=[h for h in headings if h[0]<=i]
    if not before:sections.append({'match_line':i,'class':'unclassified-no-heading'});continue
    h=before[-1];after=[x for x in headings if x[0]>h[0] and x[2]<=h[2]]
    end=after[0][1] if after else len(b)
    bad=bool(admin.search(h[3]))
    sections.append({'start_line':h[0],'start_byte':h[1],'end_byte':end,'heading':'[ADMINISTRATIVE REJECTED]' if bad else h[3],'class':'administrative-rejected' if bad else 'candidate-mathematical-heading','match_line':i})
   hits.append({'path':rel,'sha256':hashlib.sha256(b).hexdigest(),'sections':sections})
out={'query':query.pattern,'stats':stats,'hits':hits,'limits':'No file size cutoff; full-path pruning before descent/read/decode; metadata navigation only; own root and wrapper excluded. Opaque aliases can escape; coarse guards may omit originals. No exhaustive clearance.'}
(R/'private/history-nonlocal-navigation.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
