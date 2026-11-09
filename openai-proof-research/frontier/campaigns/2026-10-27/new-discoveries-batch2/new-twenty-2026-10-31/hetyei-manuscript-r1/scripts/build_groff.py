from pathlib import Path
R=Path(__file__).resolve().parent.parent
s=(R/'scripts/paper_content.py').read_text()
s='\n'.join(x for x in s.splitlines() if not x.startswith('from reportlab'))
ns={'__file__':str(R/'scripts/paper_content.py')};exec(compile(s,'paper-content','exec'),ns)
pages=ns['pages'];D=ns['D'];out=['.nr PO 0.67i','.nr LL 7.16i','.nr HM 0.5i','.nr FM 0.45i','.nr PS 10.5','.nr VS 12.8','.ds LF DRAFT | AI-assisted | MathDB 347230 | not accepted','.ds RF \\n[PN]','.ds CF',''];md=[]
def esc(t):return t.replace('\\','\\e').replace('-','\\-')
for i,items in enumerate(pages):
 if i:out+=['.bp'];md+=['\n---\n']
 for kind,t in items:
  if kind=='h':
   out+=['.SH '+esc(t)];md+=['## '+t+'\n']
  elif kind=='p':out+=['.PP',esc(t)];md+=[t+'\n']
  elif kind=='eq':out+=['.DS L','.ft CR','.ps 8.8','.vs 11p',esc(t),'.ft R','.ps 10.5','.vs 12.8p','.DE'];md+=['```text\n'+t+'\n```\n']
  else:
   rows=[['n','dim V_n','rank I_2','dim ker I_2','dim A_n','dim(ker cap S_n)']]+[[r[k] for k in ['n','ambient','rank','kernel','anti','symmetric_kernel']] for r in D['table']]
   out+=['.TS','center;','c c c c c c.']+['\t'.join(map(str,r)) for r in rows]+['.TE'];md+=['\n'.join(' | '.join(map(str,r)) for r in rows)+'\n']
(R/'manuscript.ms').write_text('\n'.join(out)+'\n');(R/'manuscript.md').write_text('\n'.join(md)+'\n')
print('Wrote groff source and readable source')
