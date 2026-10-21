"""Bind actual semantic read extents; acquisition and lexical search are separate."""
from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parent
entries=[]
def add(p,ranges,purpose,limits='Unlisted lines are uncredited, not presumed read.'):
 p=R/p;b=p.read_bytes();ls=b.splitlines(); rr=[]
 for start,end in ranges:
  end=len(ls) if end is None else end
  assert 1<=start<=end<=len(ls),(p,start,end,len(ls))
  rr.append({'start':start,'end':end,'raw_line_join_sha256':hashlib.sha256(b'\n'.join(ls[start-1:end])).hexdigest()})
 entries.append({'copy':str(p.relative_to(R)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'lines':len(ls),'read_ranges':rr,'purpose':purpose,'limits':limits})
for n in ['H-SCOPE.md','AUTHOR-PROOF.md','DERIVATION.md','freeze-receipt.json','REPORT.md','FINAL.json','READING-LIMITS.md','NOTES.md','README.md','source-ledger.json','primary-ledger.json','original-ledger.json','verify.py']:
 add('private/incoming/'+n,[(1,None)],'Mandatory author original; source/primary/history metadata are navigation, not independent gate authority.')
for n in ['assessment.md','intake.json','replay.json']:add('private/parent/'+n,[(1,None)],'Exact parent intake/limits, no gate authority.')
for p in sorted((R/'private/source/preprints').glob('A-Three-Dimensional*/build/sections/*.tex')):add(p.relative_to(R),[(1,None)],'Actual complete stipulated September26 operative source section, including proof ending.')
for p in sorted((R/'private/source/preprints').glob('A-counterexample*/build/sections/*.tex')):
 if p.name=='geometry.tex':add(p.relative_to(R),[],'Acquired authenticated bytes only; no body read.')
 elif p.name=='algebra.tex':add(p.relative_to(R),[(1,90),(410,500)],'Actual finite representation/control statement and finite-word inverse proof; middle single-degree/direct-sum proof uncredited.')
 else:add(p.relative_to(R),[(1,None)],'Actual complete September25 operative comparison section, including positive full-leg normalization and exact transmission.')
add('private/primary/2109.07534v1/main.tex',[(275,355),(525,574),(575,1108)],'Actual unique-cone/counting and three-circles proofs, cone expansion/counting and quoted Weyl/convergence input statements; their external proofs not read.')
add('private/primary/1601.02066v1/main.tex',[(202,345),(418,685)],'Actual conic setup/degree union, weighted-sequence lemma, ball and Green-level three-circles proofs with their endings.')
add('private/primary/1108.3244v3/main.tex',[(1,181),(199,341),(352,389),(490,550)],'Actual slow-link lemma and complete global main realization proof, plus round-link application and incidental ending/bibliography excerpt. Not all examples/closability proofs.')
add('private/primary/2312.16939v4/text/main.tex',[(1,175),(200,255),(343,625),(1002,1038),(1173,1336)],'Actual sphere stability, finite-cluster structure/variation and needed implicit/transversality/resolvent proofs. Not whole paper; no semantic credit for overlarge label-search snippets.')
add('private/originals/AGENTS.md',[(1,None)],'Project instructions; direct ancestor candidates were checked separately and absent.')
add('private/originals/sources/upstream.json',[(1,None)],'Stipulated immutable pin.')
add('private/originals/frontier/iterations/i130-spectral-harmonic-discovery.md',[(98,201)],'Selected exact H and full H1/H2 operations, obstructions and decision; unrelated earlier screens uncredited.')
add('private/originals/frontier/iterations/i133-fixed-metric-harmonic-growth.md',[(1,None)],'Full original I133, including old conclusion, fixed-cutoff/prefix/geometry/exhaustion proofs.')
add('private/originals/frontier/iterations/i136-birational-positivity-discovery.md',[(1,136)],'Genuine history hit followed to original harmonic overlap; no new birational target reopened.')
add('private/originals/frontier/campaigns/2026-10-14/fresh-analytic-discovery-r33/report.md',[(1,None)],'Named completed original history lead; no unrelated body follow-up.')
for name,start,end in [('iteration133-fixed-metric-harmonic-growth-task.json',236,375),('iteration136-birational-positivity-discovery-task.json',381,481)]:
 p=R/'private/originals/frontier/iterations'/name;b=p.read_bytes();j=json.loads(b);ls=j['brief'].splitlines();text='\n'.join(ls[start-1:end]);q=R/'private/extracts'/('FINALPARENTI130.txt' if '133-fixed' in name else 'FINALPARENTI133.txt');q.parent.mkdir(exist_ok=True);q.write_text(text+'\n');entries.append({'copy':str(p.relative_to(R)),'sha256':hashlib.sha256(b).hexdigest(),'decoded_field':'brief','decoded_lines':[start,end],'decoded_passage_sha256':hashlib.sha256(text.encode()).hexdigest(),'extract':str(q.relative_to(R)),'purpose':'Actual original finalized parent response, not an alias or search hit. Whole JSON body not credited as read.'})
(R/'reading-ledger.json').write_text(json.dumps({'convention':'Raw splitlines LF-joined without appended newline; decoded JSON brief uses Unicode splitlines LF-joined without appended newline. Hashes bind extents, not cognition.','entries':entries,'direct_administrative_ranges':{'sources/CONTENTS.md':[[1,24],[8754,8754],[8763,8763]],'frontier/NEW-TEN-2026-10-14.md':[[1,155]]},'tree':'Complete13223-entry tree used for membership/hash authentication, not read as mathematical prose; truncated tree.json unused.'},indent=2)+'\n')
print('read-ledger entries',len(entries))
