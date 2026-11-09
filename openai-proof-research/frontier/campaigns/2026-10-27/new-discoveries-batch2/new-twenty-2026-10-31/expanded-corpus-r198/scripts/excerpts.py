import pathlib,re,json
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for i,o in json.loads((D/'outputs/source-versions.json').read_text()).items():
 v=max(o['versions']);p=D/'outputs'/f'{i}-v{v}.txt'
 if not p.exists():continue
 lines=p.read_text().splitlines();hits=[k for k,l in enumerate(lines) if re.search(r'Conjecture|counterexample|conjecture.*(false|solved)|Theorem [1-9]',l)]
 text='\n'.join(f'{k+1}: '+ '\n'.join(lines[max(0,k-1):k+7]) for k in hits[:18]);out.append('\n### '+i+' v'+str(v)+'\n'+text)
(D/'outputs/current-excerpts.txt').write_text('\n'.join(out))
