import pathlib,itertools,json,time
D=pathlib.Path(__file__).resolve().parents[1];out={'scope':'All binary x with1<=|x|<=10; retain xxx^R if it has no proper www^R factor; diagnoses printed source inconsistency only','counts':{},'examples':{}};start=time.monotonic()
for n in range(1,11):
 words=[]
 for t in itertools.product('01',repeat=n):
  x=''.join(t);w=x+x+x[::-1];bad=False
  for k in range(1,n):
   if any(w[i:i+k]==w[i+k:i+2*k] and w[i:i+k]==w[i+2*k:i+3*k][::-1] for i in range(len(w)-3*k+1)):bad=True;break
  if not bad:words.append(w)
 out['counts'][str(3*n)]=len(words);out['examples'][str(3*n)]=words[:6]
out['wall_seconds']=time.monotonic()-start;(D/'outputs/words.json').write_text(json.dumps(out,indent=2));print(out)
