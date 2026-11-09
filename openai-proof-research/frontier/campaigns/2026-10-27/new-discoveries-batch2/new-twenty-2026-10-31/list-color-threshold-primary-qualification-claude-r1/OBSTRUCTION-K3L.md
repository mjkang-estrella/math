# Note: K_{3,l} does not follow the sqrt(l) law (reviewer-authored, NOT independently reviewed, credit 0)

Purpose: adversarial question 3. All arithmetic by hand; no program.

Claim. Let m >= 3, t = m-1, d = m-2, u >= 1, l = 3u, s = (t-1)/t. If s^u <= 1/(6 sqrt d) then
P_l(K_{3,l}, m) < P(K_{3,l}, m). Since s^u <= e^{-u/t}, this holds whenever u >= t ln(6 sqrt d).
Hence tau(K_{3,l}) = Omega(l / log l) along l = 3u.

Assignment. D a set of d colours, and 1,2,3 outside D. Lists on the part of size 3:
A1 = D+{1,2}, A2 = D+{2,3}, A3 = D+{3,1}. On the part of size l, u lists each of D+{1,2}, D+{2,3}, D+{3,1}.

Count tuples (a1,a2,a3) in A1xA2xA3 by colour pattern, with the number of extensions:
  (a) one D colour only:             d tuples,            t^{3u}
  (b) two colours of {1,2,3}, no D:  6,                   (t-1)^u t^{2u}
  (c) all of 1,2,3:                  2,                   (t-1)^{3u}
  (d) one D colour, one of {1,2,3}:  9d,                  (t-1)^{2u} t^u
  (e) one D colour, two of {1,2,3}:  9d,                  (t-2)^u (t-1)^{2u}
  (f) two D colours only:            3d(d-1),             (t-1)^{3u}
  (g) two D colours, one of {1,2,3}: 6d(d-1),             (t-2)^{2u} (t-1)^u
  (h) three D colours:               d(d-1)(d-2),         (t-2)^{3u}
The counts sum to (d+2)^3 = m^3. With P(K_{3,l},m) = m t^{3u} + 3 m t (t-1)^{3u} + m t (t-1)(t-2)^{3u}:
  P(G,m) - P(G,L) = 2 t^{3u} - 6 (t-1)^u t^{2u} - 9d (t-1)^{2u} t^u - 9d (t-2)^u (t-1)^{2u}
                    - 6d(d-1) (t-2)^{2u} (t-1)^u + (12d+4)(t-1)^{3u} + 6 d^2 (t-2)^{3u}.
Put e = s^u. As (t-2)/t <= s^2, dividing by t^{3u} gives at least 2 - 6e - 9d e^2 - 9d e^4 - 6 d^2 e^5.
For e <= 1/(6 sqrt d) this is at least 2 - 1 - 1/4 - 1/144 - 1/1296 > 0. []

Why the K_{2,l} proof cannot extend. It needs a family of non-monochromatic tuples whose colours are hit on average
once per list. For two lists A'xB' is such a family. Here every tuple has at least two distinct colours once D is
avoided, and pair sums of the hit probabilities on {1,2,3} cannot all be at most 1. Tuples of type (b) are hit 4/3
times per list on average, a FIRST-order loss, versus the second-order loss in K_{2,l}.

Consequences recorded only as observations. (1) sqrt(l) is not a uniform law for K_{s,l}. (2) No bound in terms of
|E| alone can give sqrt(|E|), so no general theorem of that form yields the target. (3) Source Question 7 asks whether
tau_max(t) = omega(sqrt t); the above says yes, up to verification. I did not search this separately beyond the
K_{n,l} words in search 2 and make no novelty claim. It is outside the literal of 353552 and earns nothing here.
