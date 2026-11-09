# Dismal Conjecture26: root-proposed routine exclusion

Provenance: the proof mechanism was supplied by root in the assignment, initially unreviewed. This lane checks and completes it; it is not a separate credited family or nomination.

Source: Applegate–LeBrun–Sloane, *Dismal Arithmetic*, JIS14 (2011), VOL14/Sloane/carry2.pdf, definitions (5)–(7) pp4–5, divisor definition p6, number/sum of divisors Section6 p15, Conjecture26 p30. The original definitions identify dismal numbers with nonnegative ordinary integers. For nonzero n a divisor cannot be zero, since multiplying zero gives zero. Addition is digitwise maximum and multiplication is max of digitwise min convolutions. For positive factors the leading product coefficient is the minimum of their two positive leading digits, hence positive. Therefore lengths add minus1, equivalently degrees add. This verifies the exact conventions needed.

Let D be the finite set of decimal dismal divisors of n>0, d=|D|, and sigma their digitwise maximum interpreted as an ordinary integer. Each element of D is positive and at most sigma in ordinary order. Therefore d<=sigma. Equality would force D={1,...,sigma}.

If equality holds,1 divides n. A dismal product with the one-digit factor1 has every digit0 or1. Thus n has only those digits. For n>1 its length L is at least2. Replace every1 of n by9, leaving zeros unchanged, to obtain an L-digit divisor r: r dismally multiplied by1 equals n. Thus sigma>=r>=9*10^(L-1). Both a=10^(L-1) and b=10^(L-1)+1 are positive integers at most sigma (L>=2), so under equality both divide n.

Because a and b each have length L, any positive quotient producing n must have length1 by degree addition. Multiplication of a by a positive one-digit quotient yields a monomial with only its leading digit nonzero (indeed that digit is1). Multiplication of b by a positive one-digit quotient yields nonzero digits at both degree L-1 and degree0 (both1). As L>=2 those positions differ. A single n cannot have both forms. Thus equality is impossible for n>1, and d_10(n)<sigma_10(n), exactly C26. For n=1 the source Table5 gives d=sigma=9, consistent with the excluded endpoint.

The source Theorems24–25 discuss the digitwise sum and binary classification. They do not state this strict decimal count inequality, but the bridge above uses only its definitions and elementary finite-set cardinality. Recommend routine exclusion with root provenance; no novelty clearance or discovery credit.
