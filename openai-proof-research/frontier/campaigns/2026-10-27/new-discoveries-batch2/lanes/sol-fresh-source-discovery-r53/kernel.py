import mpmath as m,json,pathlib
m.mp.dps=40
rows=[]
for q in map(m.mpf,['.1','.25','.4']):
 V=lambda x:q*m.log(q/x)+(1-q)*m.log((1-q)/(1-x))
 for v in map(m.mpf,['.001','.05','.5','2']):
  lo=m.mpf(0);hi=q
  for _ in range(145):
   mid=(lo+hi)/2
   if V(mid)>v:lo=mid
   else:hi=mid
  xm=(lo+hi)/2
  lo=q;hi=m.mpf(1)
  for _ in range(145):
   mid=(lo+hi)/2
   if V(mid)>v:hi=mid
   else:lo=mid
  xp=(lo+hi)/2
  K=(xp*(1-xp))**(m.mpf(1)/3)/(xp-q)-(xm*(1-xm))**(m.mpf(1)/3)/(q-xm)
  rows.append(dict(q=str(q),v=str(v),K=str(K),level_residual=str(max(abs(V(xm)-v),abs(V(xp)-v)))))
pathlib.Path(__file__).with_name('kernel-checks.json').write_text(json.dumps({'diagnostic_only':True,'rows':rows},indent=2)+'\n')
print(json.dumps(rows,indent=2))
