# Proof of the literal negation

All declarations are in namespace Hetyei347230. The endpoint has no assumptions:
`kernel_conjecture_false : ¬ KernelConjecture`.

The polynomial algebra is the free rational vector space on Boolean lists, false representing a and true representing b. Its reversal map is linear and involutive. Degree n consists of finitely supported coefficients supported on lists of length n. The antisymmetric submodule is the intersection of this degree with the kernel of star + id.

The coproduct enumerates every deletion position once, retaining its prefix and suffix. The mixing recursion has the Ehrenborg–Readdy v·b·u base case. MrsAux is an explicit Nat recursor; its successor equations implement the alternating coproduct recursion. The parity condition is n + r + s + 1 even, equivalent to the source congruence. Mrs_eq_nil_of_large proves that all terms vanish for n > |u| + |v| + 2: a recursive step consumes a letter from one input. Thus Mw's finite cutoff loses no source summands. M is its bilinear extension. I2 is the linear extension of w + reverse w + the coproduct mixing sum of Theorem 32.

uList contains the exact 20 terms from the certificate JSON. uCert_deg proves homogeneity of degree 5, star_uCert proves symmetry, and uCert_ne_zero extracts the coefficient 1 of aaaba. check_I2u uses decide +kernel to check both that every output word has length 5 and that all 32 degree-5 coefficients are zero. I2_toPoly and toPoly_coeff bridge integer list computations to rational finitely supported functions; allWords_complete ensures coverage of every possible support word. This proves I2_uCert without a computational trust extension.

If the conjectured equality held at n = 5, uCert would lie in the antisymmetric submodule. Its symmetry would then give 2 • uCert = 0, contradicting nonvanishing over Q.

For non-vacuity, kernel_equality_degree_two proves the entire equality at n = 2, the explicitly permitted alternative to proving Corollary 33 in all degrees. Every degree-2 polynomial is expanded in aa, ab, ba, bb. The image equations force the diagonal coefficients to vanish and the two off-diagonal coefficients to be negatives. Conversely those conditions imply both antisymmetry and zero image. No general-degree Corollary 33 theorem is claimed.

The optional printed-base-case variant and the companion MathDB 347231 are not formalized. No rank or minimality claim is needed by the endpoint. Root retains acceptance authority.
