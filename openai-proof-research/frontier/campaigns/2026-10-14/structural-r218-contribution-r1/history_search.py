from pathlib import Path
import runpy,os,re,json,subprocess
n=runpy.run_path('frontier/campaigns/2026-10-14/structural-r218-contribution-r1/review_io.py');P=n['P'];R=n['R'];excluded=n['excluded']
# Prospective path gates are applied to full project-relative casefold POSIX paths.
roots=['frontier/campaigns','frontier/iterations','frontier/experiments','frontier/proposals','frontier/scouts','frontier/notes','frontier/findings','notes','findings']
files=[];stats={'directory_pruned':0,'file_pruned':0,'symlinks_skipped':0,'eligible_files':0};seen=set()
def walk(p):
 rel=p.relative_to(P).as_posix()
 if excluded(rel):stats['directory_pruned']+=1;return
 if p.is_symlink():stats['symlinks_skipped']+=1;return
 if not p.is_dir():return
 for e in os.scandir(p):
  q=Path(e.path);rel=q.relative_to(P).as_posix()
  if excluded(rel):stats['directory_pruned' if e.is_dir(follow_symlinks=False) else 'file_pruned']+=1;continue
  if e.is_symlink():stats['symlinks_skipped']+=1;continue
  if e.is_dir(follow_symlinks=False):walk(q)
  elif e.is_file(follow_symlinks=False) and rel not in seen:seen.add(rel);files.append(rel)
for root in roots:walk(P/root)
stats['eligible_files']=len(files)
patterns=[r'tamed[- ]to[- ]compatible',r'compatible symplectic (?:forms?|cone)',r'anti[- ]invariant (?:cohomology|forms?|kernel)',r'(?:self[- ]dual|Hodge).{0,70}(?:reconstruct|exact|harmonic|correct)',r'(?:prescribed|fixed)[- ](?:cohomology|class).{0,90}(?:compatib|moment|taming)',r'(?:period|moment).{0,70}(?:cancel|obstruction|self[- ]dual)',r'disjoint supports.{0,70}(?:symplectic|period)',r'hypersymplectic',r'Donaldson.{0,70}(?:tamed|compatib|unimodular)',r'flat.{0,30}torus.{0,80}(?:compatib|symplectic)']
# rg is invoked only on already path-admitted exact files. No untracked inventory, no size cutoff.
args=['rg','--text','--ignore-case','--count-matches','--no-heading','--color','never']
for pat in patterns:args+=['-e',pat]
matched={}
for start in range(0,len(files),150):
 z=subprocess.run(args+['--']+files[start:start+150],cwd=P,capture_output=True,text=True)
 if z.returncode not in [0,1]:raise RuntimeError(z.stderr)
 for line in z.stdout.splitlines():
  rel,count=line.rsplit(':',1);matched[rel]=int(count)
result={'roots':roots,'stats':stats,'eligible_files':len(files),'patterns':patterns,'matched_files':len(matched),'candidates':[],'rejected':[]}
rx=re.compile('|'.join(patterns),re.I);head=re.compile(rb'^\s*(#{1,6})\s+(.+)')
admin=re.compile(r'status|provenance|scope.and.evidence|contribution|screen|source|catalog|navigation|accept|disposition|bibliog|reading|audit|next|handoff|metadata|candidate|literature|frontier|prior|summary|related work|motivation|scope|instructions|index',re.I)
for rel in matched:
 assert not excluded(rel);p=P/rel
 try:b=p.read_bytes();b.decode('utf8')
 except UnicodeError:result['rejected'].append({'path':rel,'reason':'non-UTF8'});continue
 ls=b.splitlines(keepends=True);o=[0]
 for l in ls:o.append(o[-1]+len(l))
 hs=[(i,len(m.group(1)),m.group(2).decode()) for i,l in enumerate(ls) if (m:=head.match(l))]
 for i,l in enumerate(ls):
  if not rx.search(l.decode()):continue
  candidates=[h for h in hs if h[0]<=i]
  h=candidates[-1] if candidates else None
  if h is None:result['rejected'].append({'path':rel,'match_line':i+1,'reason':'no classifiable original mathematical heading'});continue
  begin,level,title=h;end=next((j for j,lev,t in hs if j>begin and lev<=level),len(ls));endtitle=next((t for j,lev,t in hs if j==end),'EOF')
  d={'path':rel,'match_line':i+1,'heading':title,'lines':[begin+1,end],'bytes':[o[begin],o[end]],'stop_heading':endtitle}
  if admin.search(title):d['reason']='administrative/non-original heading';result['rejected'].append(d)
  else:result['candidates'].append(d)
(R/'private/history-search.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['rejected','patterns']},indent=2));print('rejected section matches',len(result['rejected']))
