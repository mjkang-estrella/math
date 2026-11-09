from pathlib import Path
import sys,json,hashlib,re
R=Path(__file__).resolve().parent
k=sys.argv[1];p=R/'private/primary'/(k+'.txt');b=p.read_bytes();ls=b.splitlines(keepends=True);st=[0]
for l in ls:st.append(st[-1]+len(l))
# These are already classified running furniture, never mathematical fragments.
def furniture(line):
 s=line.decode('utf-8').strip().strip('\f').strip()
 return bool(re.fullmatch(r"(?:\d+\s+)?(?:D\. CORRO AND J\.-B\. KORDASS|EXISTENCE SLICES SPACE OF RIEMANNIAN METRICS)(?:\s+\d+)?",s)) or s=="Author's personal copy" or bool(re.fullmatch(r'(?:\d+\s+)?MATTHEW J\. GURSKY AND JEFF A\. VIACLOVSKY(?:\s+\d+)?',s)) or bool(re.fullmatch(r'(?:\d+\s+)?RIGIDITY AND STABILITY(?:\s+\d+)?',s)) or bool(re.fullmatch(r'(?:\d+\s+)?(?:C\. (?:De|D\.) Lellis, P\. M\. Topping|Almost-Schur lemma)(?:\s+\d+)?',s))
for s in sys.argv[2:]:
 a,z=map(int,s.split(':'));assert 1<=a<z<=len(ls)+1
 print(f'PRIMARY {k} exact byte-parser lines[{a},{z}) bytes[{st[a-1]},{st[z-1]})')
 selections=[];start=None
 for i in range(a-1,z-1):
  if furniture(ls[i]):
   if start is not None:selections.append((start,st[i]));start=None
   print(f'[running furniture omitted at line {i+1}]')
  else:
   if start is None:start=st[i]
   print(ls[i].decode(),end='')
 if start is not None:selections.append((start,st[z-1]))
 with (R/'private/primary-read-extents.jsonl').open('a') as f:f.write(json.dumps({'file':str(p.relative_to(R)),'outer_lines':[a,z],'outer_bytes':[st[a-1],st[z-1]],'selected_byte_extents':selections,'outer_sha256':hashlib.sha256(b[st[a-1]:st[z-1]]).hexdigest(),'mode':'semantic extraction, classified exact running furniture omitted; formulas not auto-masked'})+'\n')
