import pathlib,json,time,random
D=pathlib.Path(__file__).resolve().parents[1];ns={'__file__':str(D/'scripts/divisibility.py')};exec(compile((D/'scripts/divisibility.py').read_text().split("lines=(D/'sources/atlas.txt')")[0],str(D/'scripts/divisibility.py'),'exec'),ns);check=ns['stats'];rng=random.Random(221);results=[];hits=[]
for n in range(8,14):
 t=time.monotonic();samples=pfree=nonpd=0
 while samples<1000 and time.monotonic()-t<10:
  p=[.2,.4,.6,.8][samples%4];a=[0]*n
  for i in range(n):
   for j in range(i):
    if rng.random()<p:a[i]|=1<<j;a[j]|=1<<i
  pd,bad,cut,hasp5=check(a);samples+=1;pfree+=not hasp5;nonpd+=not pd
  if cut or (not pd and not hasp5):hits.append({'adjacency':a,'mn_pd_subsets':bad,'clique_cutsets':cut,'P5free':not hasp5})
 result={'n':n,'samples':samples,'P5free_samples':pfree,'not_perfectly_divisible_samples':nonpd,'seconds':time.monotonic()-t};results.append(result);print(result,flush=True)
(D/'outputs/divisibility-random.json').write_text(json.dumps({'seed':221,'Gnp_probabilities':[.2,.4,.6,.8],'results':results,'hits':hits},indent=2))
