import os,fnmatch,re,json,hashlib
from pathlib import Path
R=Path(__file__).parent;cfg=json.loads((R/'private/guards.json').read_text())
wc=[re.compile(fnmatch.translate(w)) for w in cfg['wildcards']]
extra=[re.compile(fnmatch.translate(w)) for w in cfg['extra_components']]
def blocked(p):
 q=p.as_posix().casefold()
 return q==cfg['own_root'].casefold() or q.startswith(cfg['own_root'].casefold()+'/') or any(x in q for x in cfg['substrings']) or any(w.fullmatch(q) for w in wc) or any(w.fullmatch(c) for c in q.split('/') for w in extra)
queries={
'hamiltonian_stable':r'hamiltonian[\s\S]{0,180}stable[ -]morse|stable[ -]morse[\s\S]{0,180}hamiltonian',
'cyclic_integral':r'cyclic(?:ally)?[ -](?:graded[ -])?integral[ -]floer',
'involution_torsion':r'(?:hamiltonian[ -])?involution[\s\S]{0,180}(?:torsion|blow.?up)|(?:torsion|blow.?up)[\s\S]{0,180}hamiltonian[ -]involution',
'morse_arnold':r'morse[ -]number[\s\S]{0,80}arnold|arnold[\s\S]{0,80}(?:morse[ -]number|cancellation)',
'contractible_nondegenerate':r'contractible[\s\S]{0,80}nondegenerate[\s\S]{0,40}fixed|nondegenerate[\s\S]{0,80}contractible[\s\S]{0,40}fixed',
'quadric_critical':r'quadric[\s\S]{0,80}(?:critical[ -]number|three[ -]fixed|critical points)',
'mixedprime_morse':r'mixed[ -]prime[\s\S]{0,120}(?:stable[ -]morse|involution|torsion profiles)',
'augmentation_hamiltonian':r'augmentation[ -]ideal[\s\S]{0,160}(?:hamiltonian|relative[ -]morse)|relative[ -]morse[\s\S]{0,160}augmentation',
'cap_model':r'(?:sixteen|sphere|product)[ -]caps[\s\S]{0,120}(?:morse|critical|hamiltonian)|quadratic[ -]collars[\s\S]{0,100}cancellation',
'source_titles':r'fixed[ -]points[ -]below[ -](?:the[ -])?stable[ -]morse|sharpness[ -]of[ -]the[ -]cyclic'
}
queries={k:re.compile(v,re.I) for k,v in queries.items()}
admin=re.compile(r'status|provenance|scope.*evidence|contribution|screen|intake|catalog|catalogue|metadata|receipt|audit|brief|summary|disposition|handoff|administrative|comparison.*gate',re.I)
hits=[];stats={'pruned':0,'eligible_files':0,'utf8_files':0,'read_errors':0,'symlinks_skipped':0}
def walk(d):
 with os.scandir(d) as it:
  for e in it:
   p=Path(e.path)
   if blocked(p):stats['pruned']+=1;continue
   if e.is_symlink():stats['symlinks_skipped']+=1;continue
   if e.is_dir(follow_symlinks=False):walk(p);continue
   if not e.is_file(follow_symlinks=False) or p.name.casefold()=='agents.md':continue
   stats['eligible_files']+=1
   try:b=p.read_bytes();t=b.decode('utf-8')
   except UnicodeDecodeError:continue
   except OSError:stats['read_errors']+=1;continue
   stats['utf8_files']+=1
   matches=[(m.start(),m.end(),k) for k,v in queries.items() for m in v.finditer(t)]
   if not matches:continue
   ls=b.splitlines(keepends=True);head=[];off=0
   for n,l in enumerate(ls,1):
    v=l.decode();m=re.match(r'^(#{1,6})\s+(.+)',v);tx=re.match(r'\\((?:sub)*section)\*?\{(.+)\}',v)
    if m:head.append((off,len(m[1]),m[2].strip(),n))
    elif tx:head.append((off,1+tx[1].count('sub'),tx[2],n))
    off+=len(l)
   for a,z,k in matches:
    aa=len(t[:a].encode());hz=[h for h in head if h[0]<=aa]
    h=hz[-1] if hz else (0,0,'UNHEADED — manual classification required',1)
    end=next((hh[0] for hh in head if hh[0]>h[0] and hh[1]<=h[1]),len(b))
    status='administrative_rejected' if admin.search(h[2]) else 'heading_candidate_only'
    row={'path':p.as_posix(),'heading':h[2],'first_line':h[3],'start':h[0],'end':end,'alias':k,'classification':status,'file_sha256':hashlib.sha256(b).hexdigest()}
    if row not in hits:hits.append(row)
walk(Path('.'))
(R/'private/history-candidates.json').write_text(json.dumps(hits,indent=2)+'\n')
(R/'private/history-navigation.json').write_text(json.dumps({'stats':stats,'queries':{k:v.pattern for k,v in queries.items()},'limits':'Full-path prospective pruning before descent/read/decode. Hidden ignored JSON TeX Bib and large UTF8 included without size cutoff. Names/headings only displayed. Coarse substring exclusions omit useful originals; opaque aliases may escape. No perfect clearance. No symlink traversal. Broad scan performed once.'},indent=2)+'\n')
print(stats)
for h in hits:print(json.dumps(h))
