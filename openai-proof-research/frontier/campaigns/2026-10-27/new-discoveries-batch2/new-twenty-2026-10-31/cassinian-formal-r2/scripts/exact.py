from fractions import Fraction as Q
import json
# On either ray, s=Re(p)>=1 and |Im(p)|=(s-1)/20.
# Lower bound |p|^2 |y-p|^2 by s^2*((s-4)^2+(1-(s-1)/20)^2)
# for s<=5. For s>=5, use s^2*(s-4)^2>=25.
rows=[('1..5/4',Q(1)*(Q(11,4)**2)),('5/4..2',Q(5,4)**2*(4+Q(19,20)**2)),('2..3',4*(1+Q(9,10)**2)),('3..4',9*Q(17,20)**2),('4..5',16*Q(4,5)**2),('5..infinity',Q(25))]
assert all(v>Q(153,25) for _,v in rows)
# z exclusion uses finite boundary p=2+i/20.
d=Q(1601,400)*Q(81,400); lower=Q(17,4)/d
assert lower>Q(49,16)
# Membership y,z: imaginary coordinate lies strictly above upper wedge edge.
assert Q(1)>Q(3,20) and Q(1,2)>Q(1,20)
print(json.dumps({'denominator_squared_lower_bounds':[(a,str(b)) for a,b in rows],'threshold_for_ratio_5/3':str(Q(153,25)),'z_ratio_squared_at_2+i/20':str(lower),'radius_squared':str(Q(49,16)),'exact_assertions_pass':True},indent=2))
