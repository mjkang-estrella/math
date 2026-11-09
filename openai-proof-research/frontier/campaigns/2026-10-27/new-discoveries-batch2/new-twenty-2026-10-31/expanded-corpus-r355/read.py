exec(compile((__import__('pathlib').Path(__file__).parent/'research.py').read_text(),'research.py','exec'))
if sys.argv[1]=='read':
 import re
 terms=sys.argv[2].split('|'); limit=int(sys.argv[3]); inv=[]
 for p in sorted((P/'sources').glob('*.txt')):
  text=p.read_text(); lines=text.splitlines(); ranges=[]
  for n,s in enumerate(lines):
   if any(t.lower() in s.lower() for t in terms): ranges.append((max(0,n-5),min(len(lines),n+limit)))
  used=set(); print('SOURCE',p.name,'LINES',len(lines))
  for a,b in ranges:
   for n in range(a,b):
    if n not in used: print(str(n+1)+': '+lines[n]); used.add(n)
  inv.append(dict(path=str(p.relative_to(P)),sha256=sha(p.read_bytes()),lines=len(lines),actually_displayed_lines=sorted(n+1 for n in used),depth='displayed passages, not whole source'))
 js('read-'+sha('|'.join(sys.argv[2:]).encode())[:10]+'.json',inv)
