from pathlib import Path
import re
R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/percolation-formal-r4');s=(R/'unreplayed-generated/src/NReplay024.lean').read_text();out=[]
for line in s.splitlines():
 if line=='import NReplay023':line='import NCheck024_4'
 if line.startswith('def cl_'):continue
 if 'CNF.rup_sound cl_' in line:
  i=re.search('CNF.rup_sound cl_(\\d+)',line)[1];assert '(by decide)' in line;line=line.replace('(by decide)',f'rc_{i}',1)
 out.append(line)
(R/'check-factoring/src/NReplay024.lean').write_text('\n'.join(out)+'\n')
