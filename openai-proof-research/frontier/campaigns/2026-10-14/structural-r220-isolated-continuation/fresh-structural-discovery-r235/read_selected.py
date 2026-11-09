from pathlib import Path
import json,sys,hashlib
R=Path('frontier/campaigns/2026-10-14/structural-r220-isolated-continuation/fresh-structural-discovery-r235')
A='preprints/A-negatively-pinched-Kahler-threefold-without-bounded-holomorphic-coordinates-September-25-2026/'
B='preprints/One-sided-negative-sectional-curvature-and-the-holomorphic-Liouville-property-September-25-2026/'
for arg in sys.argv[1:]:
 family,filename,first,last=arg.split(':'); p=(A if family=='A' else B)+filename
 b=(R/'private/canonical'/p).read_bytes(); lines=b.splitlines(keepends=True)
 lo=int(first)-1;hi=len(lines) if last=='end' else int(last)
 assert 0<=lo<hi<=len(lines)
 s=sum(map(len,lines[:lo]));e=sum(map(len,lines[:hi]));part=b[s:e]
 print(f'=== {family}/{filename} lines {lo+1}-{hi}; bytes[{s},{e}) ===')
 print(part.decode('utf8'))
 with (R/'private/read-extents.jsonl').open('a') as f: f.write(json.dumps({'path':p,'lines_inclusive':[lo+1,hi],'bytes_halfopen':[s,e],'sha256':hashlib.sha256(part).hexdigest(),'kind':'source semantic display','truncation':'none requested; tool output must be checked'})+'\n')
