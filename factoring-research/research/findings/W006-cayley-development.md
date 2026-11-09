# W006 cubic map in rational coordinates

2026-10-08. Parent symbolic continuation, not part of the frozen screen or its
current review brief. No execution, changed parameters or empirical assertion.

For F_a(h)=h(h^2+a)/(a h^2+1), put q=(h-1)/(h+1), whenever that chart is legal.
Direct substitution gives

    q' = q*((3-a)+(1+a)*q^2)/((1+a)+(3-a)*q^2).

For h of norm one, q=i*t in the conjugation-fixed rational coordinate chart.
If 1+a is a unit, set lambda=(3-a)/(1+a). Then

    t' = t*(lambda-t^2)/(1-lambda*t^2).

This gives a concrete scalar implementation on the chart; its denominator gcds
and points outside the chart must be paid. For a=3, lambda=0 and t'=-t^3;
for a=0, lambda=3 and the map is the tangent tripling formula. Neither is a
new nonmonomial mechanism just because its other coordinate formula is rational.

Choosing lambda=b^2 rationally gives the three visible preimages t=0,+/-b of 0,
where denominators are legal. Equivalently a=(3-b^2)/(1+b^2), also with a paid
denominator. This guarantees only one layer of preimages. The equation for a
preimage of b is a cubic; the known first layer does not make every successive
inverse layer rational. Building a full split inverse tree is a distinct
acquisition problem and can incur exponential degree or height.

A tempting analytic shortcut is to make the multiplier at the fixed point
zero modulo one unknown prime: F'_a(1)=(3-a)/(1+a). But the numerator 3-a then
already has a nontrivial gcd with N unless it vanishes at all factors. The
globally critical choice a=3 returns the conjugate power map. Real contraction
also does not imply attraction in a finite field.

No new parameter search is selected by this note. The frozen menu stays
0,1,3,2,5; its full transition tables can distinguish actual fixed-point basin
growth and collision energy from degree counts. The unresolved computation is
a cheaply realizable iterated map or shared batch evaluator with a paid useful
distribution law beyond known power maps.

