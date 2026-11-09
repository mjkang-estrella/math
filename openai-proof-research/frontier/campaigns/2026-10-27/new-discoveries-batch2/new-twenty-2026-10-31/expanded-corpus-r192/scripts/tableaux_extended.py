import pathlib,json,math
D=pathlib.Path(__file__).resolve().parents[1];s=(D/'scripts/tableaux.py').read_text();ns={'__file__':str(D/'scripts/tableaux.py')};exec(s[:s.index('rows=[]')],ns);count=ns['count'];rows=[]
for m,n in [(3,5),(3,6),(6,2)]:
 a=count([n]*m);b=count([n+1]+[n]*(m-2)+[n-1]);fail=[i for i in range(n*(m-2)*(m-1)//2+1,len(a)) if a[i]!=(b[i-m+1] if 0<=i-m+1<len(b) else 0)];z={'m':m,'n':n,'A':a,'B':b,'row_standard_count':sum(a),'failures':fail};rows.append(z);print(json.dumps(z),flush=True);(D/'outputs/tableaux-extended.json').write_text(json.dumps(rows,indent=2))
