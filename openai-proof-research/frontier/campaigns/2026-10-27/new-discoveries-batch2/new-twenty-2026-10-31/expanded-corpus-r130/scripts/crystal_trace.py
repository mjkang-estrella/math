import pathlib,importlib.util,sys,json
D=pathlib.Path(__file__).resolve().parents[1]
sys.argv=['crystal','3','0'];s=importlib.util.spec_from_file_location('c',D/'scripts/crystal.py');c=importlib.util.module_from_spec(s);s.loader.exec_module(c)
a=(0,1,1,0,2,1)
def show(a):return [(list((x+1,y+1)),k) for k,(x,y) in zip(a,c.roots) if k]
def detail(a):
 out={'partition':show(a)}
 for i in [0,1]:
  e,broken=c.e(a,i);out[str(i+1)]={'normal':c.sig(a,i,False),'star':c.sig(a,i,True),'e':show(e) if e else None,'simple_blocked':broken}
 out['BD']=c.bd(a,0);return out
for seq in [[0],[1,1,1],[0]+[1]*4+[0]*3,[1]*3+[0]*4+[1]]:
 print('PATH',seq,flush=True);b=a;print(json.dumps(detail(b)),flush=True)
 for i in seq:
  b,blocked=c.e(b,i)
  print('apply',i+1,'blocked=',blocked,flush=True)
  if b is None:break
  print(json.dumps(detail(b)),flush=True)
