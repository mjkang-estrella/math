# Print source passages around conjecture/theorem markers in an unpacked arXiv source (read-only).
import sys,pathlib,re
d=pathlib.Path(sys.argv[1]); pat=re.compile(sys.argv[2] if len(sys.argv)>2 else r'conj',re.I); w=int(sys.argv[3]) if len(sys.argv)>3 else 12
for f in sorted(d.glob('*.tex'))+sorted(d.glob('main.tex')):
  L=f.read_text(errors='replace').splitlines(); shown=-1
  for i,l in enumerate(L):
    if pat.search(l) and i>shown and not l.lstrip().startswith('%') and 'newtheorem' not in l:
      a=max(0,i-3); b=min(len(L),i+w); print(f'--- {f.name}:{a+1}'); print('\n'.join(L[a:b])); shown=b
