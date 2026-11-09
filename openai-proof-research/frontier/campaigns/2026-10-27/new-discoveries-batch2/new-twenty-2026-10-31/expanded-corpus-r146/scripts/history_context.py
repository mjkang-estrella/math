# Context of exact-ID matches in prior campaign files found by grep (list in logs/history-grep-files.txt).
import re,json,pathlib,collections
R=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
ids='337294|337352|337528|337577|332393|332603|332860|333133|333742|333826|334118|334119|334560|334570|334722|334795|334947|334964|330508|330518'
P=re.compile(r'(?<![0-9a-fA-F])('+ids+r')(?![0-9a-fA-F])')
out=collections.defaultdict(list)
for f in pathlib.Path('logs/history-grep-files.txt').read_text().split():
  with open(R/f,errors='replace') as fh:
   for line in fh:
    if len(line)>200000: line=line[:0] if not P.search(line) else line
    for m in P.finditer(line):
      out[m.group(1)].append((f.split('/campaigns/')[-1][:110], line[max(0,m.start()-70):m.end()+70].replace('\n',' ')))
      if len(out[m.group(1)])>400: break
for k in sorted(out):
  print('==',k,len(out[k]))
  seen=set()
  for f,c in out[k]:
    if f in seen: continue
    seen.add(f); print('  ',f,'::',c[:200])
