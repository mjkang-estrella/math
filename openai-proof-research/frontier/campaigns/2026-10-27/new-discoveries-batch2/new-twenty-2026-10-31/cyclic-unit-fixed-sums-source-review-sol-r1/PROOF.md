# Independent ordinary proof for MathDB316244

This is a proof of falsity of the frozen literal and the printed arXiv0704.0541v1 Conjecture1.2. It is not a claim about an unread journal version, an odd-modulus replacement, novelty, or campaign acceptance. No mathematical program or enumeration was used.

Write [x] for the residue class of the integer x in the additive group Z/16Z. Take n=16 and A={[2j+1]:j is an integer,0<=j<8}. If [2j+1]=[2l+1], then 16 divides 2(j-l), so 8 divides j-l. Since -7<=j-l<=7, j=l. Consequently A has eight elements. Every representative 2j+1 is odd and hence coprime to16: every prime divisor of16 is2. Coprimality is invariant under changing the representative modulo16. A is a proper subset of Z/16Z as well as a subset in the inclusive convention.

The real size bound is satisfied since 4n-4=60, both 8 and sqrt60 are nonnegative, and 8^2=64>60. Further 3^2=9<15<16=4^2, hence 3<sqrt15<4 and ceil(sqrt(n-1))=4. Thus n and k are positive, k<=|A|, and all the hypotheses are satisfied with room to spare. The family of allowed four-subsets is nonempty: {[1],[3],[5],[7]} is one. Each four-subset is proper in A, so a strict reading of the subset glyph in the defining display would not remove any allowed witness or change this conclusion.

Reduction modulo2 gives a well-defined homomorphism pi:Z/16Z -> Z/2Z because 2 divides16. Each a in A has pi(a)=1. For any four-element subset B of A, pi(sum_{b in B}b)=1+1+1+1=0. Therefore 4 wedge A is contained in E={[2j]:0<=j<8}. These eight classes are distinct by the same divisibility and range argument as above; E is exactly the kernel of pi. So |4 wedge A|<=|E|=8<16=n. Equivalently [1], whose image is1, is missing. This contradicts the asserted equality and negates the full universal conjecture, without any exhaustive list of sums or assertion that the sumset has exactly eight elements.

The argument concerns exactly four distinct summands. A union over different lengths can meet both parity fibers, so this does not refute variable-length completeness S_A=union_{k>=1}(k wedge A), or its version with zero adjoined. In fact A satisfies the paper's main-theorem size hypothesis too: 8>1+2sqrt12 since 49>48 after subtracting1 and squaring positive sides. There is no conflict between completeness and failure at one length.

## Author's powers-of-two extension

The extension is valid but belongs to this same single family. For m>=4 let n=2^m and take all n/2 odd residues, the units. Distinctness follows by division of n|(2j-2l) by2. Their cardinality satisfies (n/2)^2>=4n>4n-4 because n>=16. Thus |A|>=sqrt(4n-4). The integer k=ceil(sqrt(n-1)) is positive and at most n/2: sqrt(n-1)<n/2 follows from (n-2)^2>0. Hence allowed k-subsets exist. Every such sum maps to k modulo2, so lies in a single fiber of size n/2<n. This refutes the all-n statement for every such n irrespective of the parity of k. It proves nothing about odd n, and gives no additional credited outcomes.
