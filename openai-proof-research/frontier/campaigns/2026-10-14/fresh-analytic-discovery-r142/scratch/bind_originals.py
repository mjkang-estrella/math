from pathlib import Path
import hashlib,json
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research'); R=Path.cwd()
C='frontier/campaigns/2026-10-14/'
selections=[('AGENTS.md',None),('sources/upstream.json',None),('sources/CONTENTS.md',[2295,2310]),('frontier/NEW-TEN-2026-10-14.md',[1,63])]
selections += [(C+'discovery-analytic-r141-parent/assessment.md',None)]
selections += [(C+'fresh-analytic-discovery-r141/'+n,None) for n in ['DERIVATION.md','GAPS.md','READING-LIMITS.md','ISOLATION.md']]
selections += [(C+'fresh-analytic-discovery-r83/'+n,None) for n in ['checkpoint.md','working-transport.md','primary-comparison.md']]
selections += [(C+'fresh-analytic-discovery-r118/HANDOFF.md',None),(C+'fresh-analytic-discovery-r118/packet/public/conditioning.md',None),('frontier/iterations/i05-crossfield.md',[19,31]),('proposals/probability_dynamics.md',[244,257]),('frontier/iterations/i147-computational-lower-bound-discovery.md',[180,238])]
def ident(b):return {'size':len(b),'gitblob':hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest(),'sha256':hashlib.sha256(b).hexdigest()}
def excerpt(b,a,z):
 lines=b.split(b'\n'); return b'\n'.join(lines[a-1:z])+(b'\n' if z<len(lines) else b'')
orig=[]; copies=[]
for i,(rel,ran) in enumerate(selections,1):
 b=(P/rel).read_bytes(); iden=ident(b); orig.append({'id':i,'path':rel,**iden,'observation':'late-current-original; not first-read or whole-packet authentication'})
 bb=b if ran is None else excerpt(b,*ran)
 dest=R/'private/history'/f'{i:02d}-{Path(rel).name}';dest.parent.mkdir(parents=True,exist_ok=True); dest.write_bytes(bb)
 copies.append({'original_id':i,'local':str(dest.relative_to(R)),'selection':'whole' if ran is None else 'inclusive-LF-lines','lines':ran,**ident(bb)})
(R/'original-authentication.json').write_text(json.dumps(orig,indent=2)+'\n');(R/'selected-copy-membership.json').write_text(json.dumps(copies,indent=2)+'\n')
print('originals',len(orig),'copies',len(copies))
for f in ['private/source093/build/sections/01-introduction.tex','private/source093/build/sections/02-calculus.tex','private/source093/build/sections/07-observations.tex','private/primary/bizeul/extracted/main.tex']:
 b=(R/f).read_bytes();print(f,len(b.splitlines()),len(b))
