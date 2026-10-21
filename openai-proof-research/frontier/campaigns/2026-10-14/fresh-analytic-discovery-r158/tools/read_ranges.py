from pathlib import Path
import sys,json
R=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r158');p=R/sys.argv[1];s=p.read_text().splitlines(keepends=True)
for spec in sys.argv[2:]:
 a,b=map(int,spec.split(':')); b=min(b,len(s));print('\nFILE',sys.argv[1],f'LINES {a}-{b}/{len(s)}\n'+''.join(s[a-1:b]))
 with (R/'private/read-ranges.jsonl').open('a') as f:f.write(json.dumps({'file':sys.argv[1],'start':a,'end':b,'total':len(s),'kind':'display-request; output truncations separately disclosed'})+'\n')
