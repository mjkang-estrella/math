import os,re,json,hashlib
from pathlib import Path
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research'); R=Path(__file__).resolve().parent
# Applied to each component and filename before descent/read. No path from a hit overrides this policy.
block=re.compile(r'h138-|t185r144|structural.*r144|arithmetic.*r1(?:07|08|09|10)|analytic.*r1(?:35|36|37|38)|structural.*r143|t177c143-|t373e135-|k369r134-|t088p133-|review|proof-r|contribution|release|formal|manuscript|corpus|control|source|private|snapshot|cop(?:y|ied|ies)|frozen|intake|role|brief|parent|task|recovery|history|catalog|ledger|manifest|seal|verif|validate|read.stream|packet|handoff|extract|cache|inputs?|primary|pinned|fetched|build|publication|submission|\.?venv|site.packages|context|followup|scratch|work|inventory|paths|titles|families|hits|scan|validation|diagnostic|evidence|read\.py|support|README',re.I)
pattern=re.compile(r'Source\s*361|family\s*361|harmonic.{0,70}(dimension|growth|degree)|spectral.{0,25}(flag|quotient)|retained.double|terminal.graph|whole.ball|full.leg|fixed.cutoff|nonuniform.contract',re.I)
roots=['frontier/campaigns/2026-10-14','frontier/iterations','frontier/experiments','frontier/proposals','frontier/scouts','frontier/notes','frontier/findings','experiments','proposals','scouts','notes','findings']
seen=set(); admitted=[];pruned=[];hits=[];skips=[]
for root in roots:
 p=P/root
 if not p.exists():continue
 for base,dirs,files in os.walk(p,topdown=True,followlinks=False):
  dirs[:]=sorted(dirs)
  for d in dirs[:]:
   q=Path(base)/d
   if block.search(d) or q.is_symlink():dirs.remove(d);pruned.append(str(q.relative_to(P)))
  for f in sorted(files):
   q=Path(base)/f;rel=q.relative_to(P).as_posix()
   if rel in seen:continue
   seen.add(rel)
   if block.search(f) or q.is_symlink():pruned.append(rel);continue
   b=q.read_bytes()
   try:
    if b'\0' in b:raise ValueError('NUL')
    s=b.decode('utf8')
   except (UnicodeError,ValueError):skips.append(rel);continue
   h=hashlib.sha256(b).hexdigest();admitted.append({'path':rel,'size':len(b),'sha256':h})
   matches=[{'line':i,'text':l} for i,l in enumerate(s.splitlines(),1) if pattern.search(l)]
   if matches:hits.append({'path':rel,'sha256':h,'matches':matches})
(R/'private/search-pass2.json').write_text(json.dumps({'roots':roots,'exclusion_regex':block.pattern,'pattern':pattern.pattern,'admitted':admitted,'pruned':pruned,'nonutf8_or_nul':skips,'hits':hits},indent=2)+'\n')
print('admitted',len(admitted),'pruned',len(pruned),'hit files',len(hits))
for x in hits:print(x['path'],len(x['matches']))
