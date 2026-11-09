import importlib.util,pathlib,sys,json
# Import only the polynomial implementation without its experiment driver.
p=pathlib.Path(__file__).with_name('flow_search_leaf.py');s=p.read_text().split('for n in range(2,N+1):')[0];ns={'__name__':'flow'};old=sys.argv;sys.argv=['flow','1'];exec(compile(s,str(p),'exec'),ns);sys.argv=old
f=ns['f'];add=ns['add'];e={(0,-1):1};t=()
for n in range(2,21):
 t=(t,);out={(b,j-1):c for (b,j),c in e.items()}
 # E_n = E_{n-1}/q + b (E_{n-1}(q)-E_{n-1}(1))/(1-q).
 for (b,j),c in e.items():
  for k in (range(j,0) if j<0 else range(j)):
   key=(b+1,k);out[key]=out.get(key,0)+(c if j<0 else -c)
 e={k:v for k,v in out.items() if v};value=f(t);print(json.dumps({'linear_n':n,'equal':e==value,'terms':len(e)}),flush=True)
 if e!=value:break
