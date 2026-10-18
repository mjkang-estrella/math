# Exact prescribed-map obstruction in L4

This is an obstruction to one proposed black-box transfer, not a nominee and not a counterexample to the full terminal target.

In l4^3 take x1=(1,1,1), x2=(1,-1,-1), x3=(-1,1,-1), x4=(-1,-1,1). Every distinct pair has distance fourth power32, and ||xi||4^4=3. The map f(xi)=2e_i in l4^4 is an exact isometry of these four terminals.

For any z in l4^{4+k}, extra coordinates add a common nonnegative term to every ||z-2e_i||4^4, so discard them for a lower bound. Average the four distance fourth powers. The resulting convex symmetric function of the first four coordinates is minimized by a common value a; alternatively minimize each coordinate's independent expression (|a-2|^4+3|a|^4)/4. Thus

 max_i ||z-2e_i||4^4 >= min_a[(2-a)^4+3a^4]
                         =48/(1+cuberoot(3))^3 >3.

The minimum occurs at a=2/(1+cuberoot(3)). Convexity and differentiation prove this is the global minimum. Since cuberoot(3)<3/2, its value is greater than384/125>3. Consequently no outer extension of this prescribed f can send the extra point0 to a point at distance3^(1/4) from every image terminal, regardless of added coordinate dimension. More generally any bi-Lipschitz extension with one common scale and distortionD must have D^4>=16/(1+cuberoot(3))^3>128/125: terminal ratios are exactly1, so its lower scale is at most1, and its upper permitted query ratio is at mostD.

This rules out an all-Lp analogue of 'every exact finite isometry has arbitrarily near-isometric one-point outer extensions.' It does not rule out choosing a different terminal embedding after enriching the input. The completed proposed construction deliberately chooses one finite embedding after adding profile representatives. No novelty claim is made for this elementary four-point geometry.
