import pathlib,json,math
D=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r166');rows=json.loads((D/'outputs/polygon-sweep.json').read_text());out=[]
for r in rows:
 k,n=r['k'],r['n'];a=2*math.pi/n;b=2*math.pi/(k*n)-a;s=pow(n,-1,k);d=2*math.pi*s/k;R=1/(2*math.sin(math.pi/n));h=R*math.cos(math.pi/n)
 A0=k*n*h*h*(math.tan(a/2)+math.tan(b/2));C=R*R*k*n/2*(math.cos(b-d)-math.cos(b))/math.sin(b);A=A0+C*r['relative_radius_shift']**2
 out.append({'k':k,'n':n,'inverse':s,'ell':(n*s-1)//k,'predicted_area_quadratic_coefficient':C,'area_prediction_error':r['area']-A,'perimeter_prediction_error':r['perimeter']-2*A0/h})
(D/'outputs/polygon-formula.json').write_text(json.dumps(out,indent=2));print('cases',len(out),'max_area_error',max(abs(r['area_prediction_error']) for r in out),'max_perimeter_error',max(abs(r['perimeter_prediction_error']) for r in out))
