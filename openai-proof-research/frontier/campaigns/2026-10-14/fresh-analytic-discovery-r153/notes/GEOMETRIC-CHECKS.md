# Exact geometric checks of the exploratory reduction

These are pencil-and-paper diagnostic identities, not tests or an author theorem.

## Euler condition cannot simply disappear

Take S3(a) times a flat circle of circumference ell. Its Ricci eigenvalues are (2/a²,2/a²,2/a²,0), scalar curvature is 6/a², trace-free Ricci squared norm is 3/a^4, and volume is 2pi² a³ ell. Hence

  integral |E|² = 6pi² ell/a,    F=0,    chi=0.

Fixing a²=1/2 normalizes average scalar to 12, but ell->0 makes the defect vanish and collapses the circle. These are not finite quotients of the three positive-Einstein models: their fundamental group is infinite. The example refutes only omission of the nonzero-Euler condition from that particular noncollapsed conclusion. No claim about all chi=0 metrics or a universal collapse classification follows.

## The elementary small-neck counterexample is dimension-sensitive

For a rotational metric g=e^(2u(s))(ds²+g_S3), put v=u'. Its radial and tangential sectional curvatures are -e^(-2u)v' and e^(-2u)(1-v²), respectively. Therefore

  integral |E|² = 6pi² integral (v'+1-v²)² ds,
  integral F² = 2pi² integral max(0,v',v²-1)² ds.

For any smooth neck segment with v(left)=-1 and v(right)=1,

  integral (v'+1-v²)² ds
  = integral (v'-(1-v²))² ds + 4[v-v³/3]_(left)^(right)
  >=16/3.

Thus that neck costs at least 32pi² of trace-free Ricci energy, independent of scale or monotonicity of v. End slopes tending to -1 and 1 yield the corresponding limiting lower bound. This checks why the shrinking-neck argument read in De Lellis–Topping for n>=5 is not a counterexample to the four-dimensional critical calculation. It does not exclude nonrotational degeneration or prove a general neck theorem.

## Scale bookkeeping

Under g->c g in dimension four, scalar/sectional curvature and the norm of E scale by c^-1, volume by c², and integral E² and integral F² are invariant. Integral F scales by c. This is why the positive-time limit inequality is (1-6t) integral F(h)<=Ct. Neither the unweighted integral of F nor volume is falsely called scale invariant.

For the Schouten convention A=(Ric-Rg/6)/2, sigma2(A)=R²/96-|E|²/8. Ge–Wang's Y1 is Y/6. Their factor 8/3 consequently becomes 96 in the standard-Y inequality. The positive sphere Yamabe constant has square 384pi²; it yields the normalized volume upper bound 8pi²/3+eta²/12.

## Remaining distinction

Obtaining a compact smooth limit at a fixed positive time identifies the smooth manifold, and here is enough for the quotient conclusion. It does not provide a gauge or a rate comparing original distance functions. I30's original full-scope proof already concerns that separate operation. No time-zero metric-stability claim is inserted into this round's reduction.
