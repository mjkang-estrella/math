import os,fnmatch,json,hashlib,re
from pathlib import Path
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r207')
g=json.loads((R/'guards.json').read_text())
print('guard keys',list(g))
assert len(g['wildcards'])==337 and len(g['substrings'])==162
assert '*structural*r207*' in g['wildcards'] and '*structural*207*' in g['wildcards']
for term in ['check','scope.json','publication','.diff','state_probe','consolidate','activity']:
 assert term in g['substrings']
for stem,lo,hi in [('analytic',144,195),('arithmetic',116,168),('structural',151,207)]:
 for n in range(lo,hi+1):
  assert f'*{stem}*r{n}*' in g['wildcards'] and f'*{stem}*{n}*' in g['wildcards']
for a,b in [('*k369r134-*','*k369134-*'),('*t185r144-*','*t185144-*')]:assert a in g['wildcards'] and b in g['wildcards']
def excluded(p):
 q=p.as_posix().casefold()
 return q==R.as_posix().casefold() or any(s in q for s in g['substrings']) or any(fnmatch.fnmatchcase(q,w) for w in g['wildcards']+g['derivative_wildcards'])
patterns=[
 r'asymptotic(?:ally)?[\s-]+midpoint[\s-]+uniform(?:ly)?[\s-]+convex',
 r'AMUC.{0,70}AUC',r'AUC.{0,70}AMUC',
 r'segment[\s-]+forest[\s-]+lens',r'countably[\s-]+branching[\s-]+diamond',
 r'joining[\s-]+root[\s-]+recursive[\s-]+potential',
 r'independent[\s-]+mean[\s-]+one[\s-]+tree[\s-]+multiplier',
 r'independent[\s-]+products.{0,70}(?:L1|L\^1|L_1|midpoint)',
 r'AUC[\s-]+renorming[\s-]+obstruction',
 r'bounded[\s-]+tree[\s-]+potential',r'quadratic[\s-]+path[\s-]+cost',
 r'segment[\s-]+start[\s-]+(?:tail|cost|norm)',r'two[\s-]+recursive[\s-]+potential',
 r'first[\s-]+exit.{0,60}(?:multiplier|conditional|product)',
 r'Kadets[\s–—-]+Werner',r'Daugavet.{0,80}(?:modul|measure)',
 r'weakly[\s-]+null.{0,60}(?:path[\s-]+product|multiplier)',
 r'(?:Gaussian[\s-]+square|exponential)[\s-]+multiplier',
 r'(?:uniform|unbounded).{0,60}(?:coefficient[\s-]+list|independent[\s-]+sum)']
queries=[re.compile(x,re.I) for x in patterns]
counts={'pruned_directories':0,'pruned_files':0,'symlinks':0,'eligible_files':0,'utf8_files':0,'binary_or_invalid':0,'read_errors':0,'read_bytes':0}
hits=[]
def walk(d):
 if excluded(d):return
 try:
  with os.scandir(d) as it:
   for e in it:
    p=d/e.name
    if e.is_symlink():counts['symlinks']+=1;continue
    if e.is_dir(follow_symlinks=False):
     if excluded(p):counts['pruned_directories']+=1
     else:walk(p)
    elif e.is_file(follow_symlinks=False):
     if excluded(p):counts['pruned_files']+=1;continue
     counts['eligible_files']+=1
     try:b=p.read_bytes()
     except OSError:counts['read_errors']+=1;continue
     counts['read_bytes']+=len(b)
     try:s=b.decode('utf-8')
     except UnicodeDecodeError:counts['binary_or_invalid']+=1;continue
     if '\x00' in s:counts['binary_or_invalid']+=1;continue
     counts['utf8_files']+=1
     matches=[]
     for k,q in enumerate(queries):
      for m in q.finditer(s):matches.append({'query':k,'start':len(s[:m.start()].encode()),'end':len(s[:m.end()].encode())})
     if matches:hits.append({'path':p.as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'matches':matches})
 except FileNotFoundError:pass
roots=[Path('frontier')/x for x in ['campaigns','iterations','experiments','proposals','scouts','notes','findings']]
for d in roots:walk(d)
record={'guard_sha256':hashlib.sha256((R/'guards.json').read_bytes()).hexdigest(),'roots':list(map(str,roots)),'queries':patterns,'counts':counts,'hits':hits,'limits':'Prospective full-relative-path pruning, no symlinks, no filesize cutoff, hidden/ignored/JSON/TeX/Bib eligible; coarse omissions and opaque aliases possible. No exhaustive clearance.'}
(R/'private/history-navigation.json').write_text(json.dumps(record,indent=2))
print(json.dumps({'counts':counts,'hits':[{'path':h['path'],'queries':sorted(set(x['query'] for x in h['matches'])),'match_count':len(h['matches'])} for h in hits]},indent=2))
