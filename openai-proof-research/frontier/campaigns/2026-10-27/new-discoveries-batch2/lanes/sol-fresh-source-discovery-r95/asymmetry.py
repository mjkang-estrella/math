exec(open(__file__.replace('asymmetry.py','drum.py')).read().split('expr=')[0])
# On beta=pi/4: z=(2c²-1)/(1-c²). Exact evaluation, no quadrature.
rows=[]
for cc in [s.Rational(3,4),s.Rational(7,9),s.Rational(4,5),s.Rational(5,6),s.Rational(6,7),s.Rational(9,10)]:
 zz=(2*cc*cc-1)/(1-cc*cc)
 hh=s.simplify((gcc-gz*fcc/fz).subs({z:zz,c:cc}));jj=s.simplify((gc*fz-gz*fc).subs({z:zz,c:cc}))
 rows.append({'c':str(cc),'z':str(zz),'H':str(hh),'H_approx':str(hh.evalf(15)),'J':str(jj),'J_approx':str(jj.evalf(15))})
(P/'asymmetry.json').write_text(json.dumps(rows,indent=2)); print(json.dumps(rows,indent=2))
