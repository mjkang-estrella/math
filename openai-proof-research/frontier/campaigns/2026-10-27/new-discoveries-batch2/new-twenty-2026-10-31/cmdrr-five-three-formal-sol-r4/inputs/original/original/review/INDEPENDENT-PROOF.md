# Independent ordinary proof: CMDRR(5,3) is impossible

This is a personal deductive review, not a program-generated check or a formal certificate. The author's proposed argument was not treated as an established theorem. All schedules satisfying Berman-Wakeling Definition 1.2 are covered; no rounds, resolution, extra Latin property, or ordering of the games is assumed.

## Exact object and normalization

A game is an unordered pair of mixed teams { (M_i,F_j), (M_k,F_l) }, with i different from k and j different from l. A schedule can initially be regarded as a finite collection of game occurrences. Opposing and partnering multiplicities count occurrences, not ordered displays of teams. There are five distinct players of each sex and three disjoint spouse pairs. Enumerate the three pairs arbitrarily and label the male and female in each pair by the same element of H={1,2,3}. Label the two remaining players on each side arbitrarily by 4,5. These are bijective relabelings of each player set. Transport every game occurrence along them; partnership, opposition, and co-occurrence counts are preserved because relabeling induces bijections on occurrences of every relation. Thus a contradiction for the canonical spouse relation proves impossibility for any spouse matching of size three.

The source conditions become: spouses M_i,F_i for i in H never share a game; every other mixed pair partners once and opposes once; every same-sex pair opposes once except the pair of singles {4,5}, which opposes twice. The last assertion follows directly from the definition: a single must repeat opposition with another single, and only one other single exists. There are 25-3=22 allowed partnership cells X. Each occurs in exactly one game, and each game contains exactly two such cells, distinct because its two men and two women are distinct. Consequently there are eleven games. No partnership cell can belong to two distinct occurrences; in particular repeated copies of the same game would violate uniqueness. Switching team order does not create another occurrence.

## Genuine row and column bijections

For a man i let S_i be all women except his wife, if any. Given j in S_i take the unique game where M_i partners F_j and let p_i(j)=l be its opposing woman. This lies in S_i by spouse avoidance, and differs from j by distinctness of women in a game. For every l in S_i the unique game where M_i opposes F_l has a unique female partner F_j; that j gives an inverse to p_i. Thus p_i is a permutation, not merely a map with an assumed surjectivity. Its domain has size four for i in H and five for i=4,5. Each game involving M_i contributes one directed edge j -> p_i(j) and exactly one cell in row i; there is no division by two here.

Similarly, for a woman l define q_l(k)=i in the unique game where F_l partners M_k and opposes M_i. The unique mixed-opposition occurrence supplies its inverse. It is a fixed-point-free permutation of her allowed men, with the same domain sizes. This convention is partner-to-opponent in both sexes.

## Spouse rows and the structural identity

If p_i has a two-cycle (a b), its edges a -> b and b -> a come from two distinct games: M_i has different partners in them and has just one partner within any game. Both games contain the female pair {a,b}. The global female opposition count permits a repeated pair only when {a,b}={4,5}. This establishes the restriction for every row.

Every finite permutation partitions its domain into disjoint cycles: successive iterates of an element first return to it by bijectivity, and intersecting orbits coincide. No fixed point means every cycle length is at least two. On four elements the only possibilities are a four-cycle or two disjoint two-cycles. Two disjoint two-cycles would repeat two different female pairs, whereas only one female pair may repeat. Hence each spouse row is a four-cycle on {j,k,4,5}, where H minus {i}={j,k}.

The four directed edges of a four-cycle yield four distinct undirected edges: an undirected edge could repeat only if both directions occur, which would be a two-cycle. Each vertex has undirected degree two. Let e be the indicator for the edge {4,5}, f the indicator for {j,k}, and c the number of edges between these two pairs. The degree sum on {4,5} is 4=2e+c and on {j,k} is 4=2f+c. Thus e=f. This supplies the opposite-edge bridge without enumerating cycles or schedules.

Let A be the number of games having both men in H and women {4,5}; B the number having men {4,5} and both women in H; z the number having both the male and female pairs {4,5}. These are nonnegative integer counts of game occurrences. Sum e=f over the three spouse rows. Exactly two games contain the female pair {4,5}. Among them A contain two spouse men, z contain none, and 2-A-z contain one. The e-sum therefore counts spouse-man incidences in those games and equals 2A+(2-A-z)=2+A-z.

For the f-sum fix an unordered pair {j,k} in H and let i be the third member. There is exactly one game containing F_j,F_k, since they oppose once. Neither M_j nor M_k can participate because each would share a game with his wife. The two men must therefore form one of {i,4}, {i,5}, {4,5}. In the first two cases that game contributes exactly once to f, in row i; in the last case it contributes zero. Each pair in H has exactly one complementary index i, and there are three such female pairs. Exactly B of their games use men {4,5}. Thus the f-sum is 3-B. Equating the sums gives

                 A+B = 1+z.                     (*)

This identity uses only the already proved spouse-row four-cycles; it does not presuppose the type of any single row.

## Elimination of every single-row two-cycle

Suppose p_m for a single man m has a two-cycle. Its support must be {4,5}. The remaining three elements of the permutation cannot have fixed points; hence form one three-cycle, on H. The two games of its two-cycle are distinct and contain F4,F5; the global count of that female pair is two, so they exhaust those games. Both contain M_m and consequently none can have two spouse men. Therefore A=0. All other games of M_m correspond to the three edges of the three-cycle on H and have both women in H.

Let t be the other single man. The pair M_m,M_t opposes in exactly two games. Exactly z of them have women {4,5}, by the definition of z. Every other such game, because it contains M_m, belongs to his remaining three games and has women in H. Conversely every B-game has men {m,t}, so contains M_m and is one of these two games. Hence B=2-z. Equation (*) now gives 2-z=1+z, or 2z=1, impossible for an integer. Explicitly, z=0 gives 0=1, and z>=1 gives 2z>=2. Thus neither single row has a two-cycle.

A fixed-point-free permutation on five elements has cycle lengths at least two. If it has more than one cycle the only partition of five into such lengths is 2+3, which includes a two-cycle. Consequently each single row is one five-cycle. This is cycle-length reasoning, not enumeration of schedules.

Definition 1.2 and all arguments above are invariant under interchanging men and women. Apply the entire argument with the sexes exchanged, including its own identity (*) and its single-column contradiction. Thus the three spouse columns q_l are four-cycles and the two single columns are five-cycles. Merely asserting that a column must have the row type without this symmetry of hypotheses would not suffice.

## Permutation sign contradiction, with direction and domains

Define U on X by U(i,j)=(i,p_i(j)), and C on X by C(k,l)=(q_l(k),l). Their inverses are assembled from the already constructed row and column inverses, so both are genuine permutations of X. A cycle of length r is a product of r-1 transpositions (fix one vertex and successively swap it with the other cycle vertices); its sign is (-1)^(r-1). Sign is multiplicative and is unchanged by extending a permutation to act identically off its support. The row supports partition X. Hence U has three four-cycles of sign -1 and two five-cycles of sign +1, giving sign(U)=-1. The same reasoning on column supports gives sign(C)=-1.

For x=(i,j), let the unique game of that partnership have opposing team (M_k,F_l), and set T(x)=(k,l). This lies in X. The unique game of (k,l) is the same game, since that partnership already occurs there; therefore T(T(x))=x. It cannot fix x because the teams have different men and different women. Its two-element orbits are exactly the two partnership cells of individual games. There are eleven such orbits, so T is eleven disjoint transpositions and sign(T)=-1.

In the same game F_l partners M_k and opposes M_i; thus q_l(k)=i. Consequently C(T(i,j))=(i,l)=U(i,j) pointwise. Taking signs of C composed with T=U gives (-1)sign(T)=-1 and hence sign(T)=+1. This contradicts sign(T)=-1. No admissible schedule exists.

The conclusion is the asserted nonexistence, not a refutation of nonexistence. It applies to all games satisfying the source multiplicities with three arbitrary disjoint spouse pairs. No extra assumptions have entered the proof. No ordinary proof gap remains in this review; all formal counterparts remain unpaid.
