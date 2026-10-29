exec(open(__file__.replace('routes.py','probe.py')).read().split('results=[]')[0])
out=[]
for n,a,b in [(3,3,4),(4,4,4),(4,4,5),(5,5,6),(6,6,6)]:
 p=R(n,a,b).as_expr()
 G=s.groebner([p,s.diff(p,x),s.diff(p,y)],x,y)
 out.append({'n':n,'a':a,'b':b,'affine_gradient_ideal':str(G),'ym1':str(s.factor(p.subs(y,-1)))})
print(json.dumps(out,indent=2));pathlib.Path(__file__).with_name('routes-results.json').write_text(json.dumps(out,indent=2))
