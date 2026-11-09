import pathlib,re
D=pathlib.Path(__file__).resolve().parents[1]
for p in (D/'sources').glob('arxiv*.txt'):
 lines=p.read_text().splitlines();hits=[]
 for i,l in enumerate(lines):
  if re.search(r'Conjecture|Question|computational|verified|checked by|tested|enumerat',l) and len(l)<1600:hits.append((i+1,'\n'.join(lines[max(0,i-3):i+12])))
 (D/'outputs'/(p.stem+'-excerpts.txt')).write_text('\n\n'.join(str(i)+' '+x for i,x in hits))
 print(p.stem,[(i,x.replace('\n',' ')[:230]) for i,x in hits[:12]])
