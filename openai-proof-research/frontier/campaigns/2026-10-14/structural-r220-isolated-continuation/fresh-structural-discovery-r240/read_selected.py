from pathlib import Path
import json,sys,hashlib
R=Path('frontier/campaigns/2026-10-14/structural-r220-isolated-continuation/fresh-structural-discovery-r240')
PREFIX={'J':'Determination-of-a-metric-and-a-unitary-connection-from-one-boundary-patch-October-5-2026','S':'Smooth-Anisotropic-Uniqueness-in-the-Calderon-Problem-from-One-Boundary-Patch-September-24-2026','M':'Nonuniqueness-for-Bounded-Measurable-Scalar-Conductivities-in-Three-Dimensions-September-23-2026'}
for arg in sys.argv[1:]:
 alias,file,start,end=arg.split(':'); start=int(start); end=int(end)
 p=R/'private'/'preprints'/PREFIX[alias]/'build'/file
 b=p.read_bytes(); ls=b.splitlines(keepends=True)
 assert 1<=start<=end<=len(ls)
 lo=sum(map(len,ls[:start-1])); hi=sum(map(len,ls[:end]))
 masks={'J:paper.tex':{3,4,5,7},'S:paper.tex':{3,4,5,7},'M:paper.tex':{42,43,44,47,161}}
 omit=masks.get(alias+':'+file,set())
 print('\nREAD',alias,file,'lines',start,end,'bytes',lo,hi,'EOF' if end==len(ls) else 'contiguous installment; classified section endpoints in boundaries.json')
 for i in range(start-1,end):
  if i+1 in omit: print('[driver title/production wrapper masked]')
  else: print(ls[i].decode(),end='')
 with (R/'private'/'semantic-reads.jsonl').open('a') as h: h.write(json.dumps({'path':p.relative_to(R).as_posix(),'start_line':start,'end_line':end,'start_byte':lo,'end_byte':hi,'masked_lines':sorted(omit.intersection(range(start,end+1))),'sha256':hashlib.sha256(b).hexdigest()})+'\n')
