from research import *
import collections
pats=[('domino',re.compile(r'2501[.]17765|(?<!\d)366858(?!\d)|Domino\s+Tilings.{0,20}Domino\s+Shuffling|Cavey|Yi.Lin\s+Lee',re.I)),('partite',re.compile(r'2410[.]11194|(?<!\d)365312(?!\d)|Partite\s+saturation\s+number\s+of\s+cycles|Yiduo\s+Xu|Zhen\s+He.{0,60}Mei\s+Lu',re.I)),('spectral',re.compile(r'minimum\s+spectral\s+radius.{0,80}saturat|spectral\s+saturation|Kim.{0,25}Kim.{0,25}Kostochka|Suil\s+O|disc[.]2020[.]112068',re.I))]
seen={};stats=collections.Counter()
with (H/'focused-matches.jsonl').open('w') as out:
 for line in (H/'rg-target-paths.txt').open():
  p=Path(line.strip()).resolve();rel=str(p.relative_to(R))
  if p.stat().st_size>12000000:stats['oversized']+=1;continue
  b=p.read_bytes();h=hashlib.sha256(b).hexdigest()
  stats['matching_paths']+=1
  if h in seen:continue
  seen[h]=rel;stats['unique_bodies']+=1
  if len(b)>12000000:stats['oversized']+=1;continue
  if b'\0' in b:stats['binary']+=1;continue
  s=b.decode('utf8','replace')
  # Native rg already completed broad statement screening; focused pass records source identities.
  for k,pat in pats:
   for m in pat.finditer(s):
    out.write(json.dumps({'target':k,'path':rel,'sha256':h,'offset':m.start(),'excerpt':s[max(0,m.start()-180):m.end()+260]})+'\n');stats[k]+=1
save('focused-receipt.json',dict(stats));print(dict(stats))
