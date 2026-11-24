# Locating chromatic numbers of complete graph products with cycles and paths

**Abstract.** We prove Conjecture 3 of Behtoei and Omoomi with explicit thresholds. For $m\ge 7$ and $n\ge 4$, the locating chromatic numbers of $K_m\square C_n$ and $K_m\square P_n$ both equal $m+1$ for $n\le m+1$ and $m+2$ for $n\ge m+2$. A single lower-bound argument applies to both graphs, as does a cyclic construction using Hall’s marriage theorem. Two singleton colour classes distinguish vertices in the remaining range, with a separate choice of shifts at the antipode of an odd cycle.

**Provenance.** Claude Opus 5.5 produced the proof and the first review. GPT-6.2 Sol performed the cross-model review and Lean formalization. A separate GPT-6.2 Sol lane performed the final check, using the same model family as the Lean and manuscript packager.

## Conjecture and definitions

Behtoei and Omoomi state the following in §4 of arXiv v3 and on p. 234 of the journal version. [Source, arXiv:1106.3453v3](https://arxiv.org/abs/1106.3453v3)

> **Conjecture 3.** If $m$ and $n$ are sufficiently large, then $\chi_L(K_m\square C_n)=\chi_L(K_m\square P_n)$.

In §1, a proper $k$-colouring of a connected graph assigns all $k$ colours and gives adjacent vertices different colours. Write $V_i$ for the class of vertices of colour $i$. The distance $d(u,v)$ is the length of a shortest path, and the distance from $v$ to a class $V_i$ is $d(v,V_i)=\min_{w\in V_i}d(v,w)$. A proper colouring is locating when the ordered codes $(d(v,V_1),\ldots,d(v,V_k))$ distinguish all vertices. The locating chromatic number $\chi_L(G)$ is the least $k$ for which such a colouring exists.

The Lean definitions use `Fin k` in place of $[k]$, preserving the $k$ ordered coordinates with labels from zero through $k-1$. Mathlib’s `SimpleGraph.dist` gives the length of a shortest walk, and a shortest walk in a connected simple graph is a path. The Lean lemmas prove that each colour distance is attained when its class is nonempty and that the minimum number of colours is attained on each of the connected finite graphs considered here. A distinct colour for each vertex provides the initial witness.

```lean
noncomputable def colorDist (G : SimpleGraph V) (c : V → Fin k)
    (v : V) (x : Fin k) : ℕ :=
  sInf {d | ∃ w : V, c w = x ∧ G.dist v w = d}

def IsLocating (G : SimpleGraph V) (c : V → Fin k) : Prop :=
  (∀ u v, G.Adj u v → c u ≠ c v) ∧ Function.Surjective c ∧
  Function.Injective (fun v => fun x => colorDist G c v x)

noncomputable def locChrom (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ c : V → Fin k, IsLocating G c}
```

The Cartesian product has vertex set $V(G)\times V(H)$. Two vertices are adjacent when they agree in one coordinate and their other coordinates form an edge of the corresponding factor.

```lean
def KC (m n : ℕ) : SimpleGraph (Fin m × Fin n) :=
  (⊤ : SimpleGraph (Fin m)).boxProd (SimpleGraph.cycleGraph n)

def KP (m n : ℕ) : SimpleGraph (Fin m × Fin n) :=
  (⊤ : SimpleGraph (Fin m)).boxProd (SimpleGraph.pathGraph n)
```

Here `⊤` is the complete graph, `cycleGraph n` joins columns consecutive modulo $n$, and `pathGraph n` joins columns whose linear indices differ by one. For $n\ge3$, the cyclic adjacency gives the ordinary simple cycle. Mathlib uses the empty graph at $n=0$, a single vertex at $n=1$, and one edge at $n=2$ for the cycle factor. In Lean the conjecture is the proposition
```lean
∃ M N : ℕ, ∀ m n : ℕ, M ≤ m → N ≤ n →
  locChrom (KC m n) = locChrom (KP m n)
```

## Distances and lower bounds

Write the vertices as $(i,j)$, with rows $0\le i<m$ and columns $0\le j<n$. In either graph, a change of row and a step in the column graph require separate edges. A shortest route in the column graph, together with one row change when needed, attains the resulting lower bound. Thus the distance between $(i,j)$ and $(r,k)$ is $[i\ne r]+\delta(j,k)$. For the path, $\delta(j,k)=|j-k|$, since each step changes the index by one and a monotone walk attains the difference. For the cycle, $\delta(j,k)=\min\{|j-k|,n-|j-k|\}$, the smaller of the lengths of the two arcs.

Every column is an $m$-clique. An $m$-colouring uses each colour once in every column. The vertices of any one colour in two columns would have the same code, with a zero at that colour and a one everywhere else. Hence at least $m+1$ colours are necessary.

In a proper $(m+1)$-colouring, let $M_j$ be the unique colour missing from column $j$. Call a vertex *colourful* if all colours appear in its closed neighbourhood. Its code has one zero at its own colour and ones in all other coordinates. Therefore a locating $(m+1)$-colouring can have at most $m+1$ colourful vertices.

Suppose a run of $L\ge 2$ consecutive columns all miss a colour $z$. Take the maximal such run containing them. On a cycle, $z$ occurs somewhere by surjectivity, and the maximal run has a boundary column containing $z$ at each end. The same column can serve as both boundaries. For a path, first suppose there is also a boundary column containing $z$ at each end. Number the run columns $t=1,\ldots,L$. Every vertex in column $t$ has distance to $z$ at most $\min(t,L+1-t)+1\le\lfloor (L+1)/2\rfloor+1$, by going along the columns to a boundary and changing row if necessary. The distance is at least one. A vertex has distance one to $z$ only if it lies in a column neighbouring one of the boundaries and in the row of that boundary’s unique $z$-vertex. There are at most two such vertices in the run.

Fix any colour $x\ne z$. Its $L$ occurrences in the run have 0 at $x$ and 1 at every colour other than $x,z$. Their distances to $z$ must be distinct. For $L\ge 4$, there are fewer than $L$ possible distances. For $L=2,3$, there are at most $L$ and at least one of the occurrences must have distance one. Applying this to all $m\ge 3$ choices of $x$ contradicts the two-vertex bound.

For a path run at an end, number columns from that end starting at 1. Let the first occurrence of $z$ be at column $L+1$ in row $r$. The vertex in row $r$ of column 1 has distance $L$ to $z$. Its colour occurs in column 2 at a different row by properness. That vertex has distance $L-1+1=L$ to $z$. Any later column containing $z$ is at least one step farther away and cannot improve either distance. All other coordinates agree as before. This rules out an end run of length at least two.

It follows that adjacent columns have different missing colours. Each column therefore has a colourful vertex in the row at which a neighbouring column contains its missing colour. If a locating $(m+1)$-colouring exists, then $n\le m+1$. Consequently at least $m+2$ colours are required when $n\ge m+2$.

## A locating colouring for $4\le n\le m+1$

Use colours $0,\ldots,m$, with the first $n$ indexed modulo $n$. Choose rows $\rho_a=a$ when $a<m$, and put $\rho_m=2$ if $n=m+1$. Any two labels at cyclic distance 1 or 2 have distinct rows. The only different labels with equal rows are 2 and $m$ in the latter case, and their two arc lengths are $m-2$ and $3$.

In each column $j$, reserve three entries.

| Row | Colour |
|---|---|
| $\rho_{j-1}$ | $j-1$ |
| $\rho_j$ | $j+2$ |
| $\rho_{j+1}$ | $j+1$ |

These rows are distinct, and the three entries use distinct colours other than $j$. To check properness between the reserved entries in columns $j$ and $j+1$, the possible row labels in the two columns are $j-1,j,j+1$ and $j,j+1,j+2$. Equal rows either come from the same label $j$ or $j+1$, or from the label pair $(j-1,j+2)$. The two colours in those cases are $j+2,j$, $j+1,j+3$, and $j-1,j+2$, respectively. Each pair consists of distinct colours even for $n=4$.

Fill the remaining $d=m-3\ge 4$ rows of each column using the $d$ colours other than $j-1,j,j+1,j+2$. Process columns in numerical order, retaining the reserved entries everywhere. A row forbids any colours already assigned in its two neighbouring columns at that row. Each row forbids at most two colours, and each colour is forbidden in at most two rows because each neighbour is injectively coloured where assigned. For a nonempty set of at most $d-2$ free rows, the union of its allowed colours has size at least $d-2$ from any one of its rows. For a set of at least $d-1\ge 3$ rows, every colour is allowed somewhere in the set. The empty set satisfies Hall’s condition too. Hall’s theorem fills the column injectively. This also preserves every previously checked row edge, including the wrap edge when the last column is filled.

Each completed column $j$ misses exactly $j$, so any colour appears in some column. Both neighbours contain $j$ in row $\rho_j$. The unique colourful vertex in column $j$ is thus $(\rho_j,j)$, of colour $j+2$, and these vertices have pairwise distinct colours. Take two distinct vertices of the same colour. They are in different columns and at least one, say in column $j$, is noncolourful. Its distance to $j$ is at least two, while the other vertex has distance one to $j$ inside its column. Vertices of different colours have different zero coordinates. The cycle colouring is locating.

For the path, use the same array. Deleting the wrap edge preserves properness, preserves the set of missing colours and cannot create a colourful vertex. The same argument for two distinct vertices of the same colour proves the path colouring is locating.

## Singleton colour classes for $n\ge m+2$

Use $m$ regular colours indexed modulo $m$ and two singleton colours $A,B$. With shift $\sigma(j)$, the regular colour at $(i,j)$ is $i+\sigma(j)\pmod m$, except at the designated singleton vertices. Each column is proper, and row edges are proper whenever adjacent column shifts differ modulo $m$. A wholly regular column contains all $m$ regular colours, so every colour is used.

**Path.** Take $\sigma(j)=j\bmod 2$ and put $A,B$ at $(2,0),(0,0)$. At a regular vertex $(i,j)$, the two distances to $A,B$ are $j+[i\ne2]$ and $j+[i\ne0]$. Their maximum is $j+1$ because the two row increments cannot both be zero. Thus equal codes of regular vertices determine their common column, and the colour then determines the row. The singleton vertices have unique colours, and vertices of different colours have different codes.

**Cycle.** Put $A,B$ at $(2,0),(0,1)$. For even $n$, use $\sigma(j)=j\bmod 2$. For odd $n=2s+1$, put $J=s+1$, and choose the shifts
$$
\sigma(0)=6,\quad \sigma(1)=5,\quad
\sigma(J-1)=0,\quad \sigma(J)=2,\quad \sigma(J+1)=4,\quad
\sigma(J\pm u)=2+((u+1)\bmod2)\quad(2\le u\le s-1).
$$
Adjacent shifts are distinct. In the odd case, the shifts alternate between 2 and 3 on each ordinary arc segment. The three consecutive shifts at the centre are $0,2,4$ and connect to the alternating segments with unequal shifts. The shifts 6 and 5 differ from each other and from either alternating shift at their other neighbours. All shifts lie between 0 and 6, so these adjacencies also have distinct shifts modulo $m\ge 7$.

For a regular vertex let $a=\delta(j,0)$, $b=\delta(j,1)$, $e=[i\ne 2]$, $f=[i\ne0]$. Its two singleton distances are $(a+e,b+f)$ and $e+f\ge1$. In columns 0 and 1 the sum of the two distances is at most 3. In every other column $a+b\ge3$, so the sum is at least 4. A collision between columns 0 and 1 requires the pair $(1,1)$. The corresponding rows are 0 in column 0 and 2 in column 1. Their regular colours are 0 and 3 in the even case, and 6 and 7 modulo $m$ in the odd case, which are distinct.

For the other columns the base pair $(a,b)$ is $(t+1,t)$ on the arc $2\le j\le n/2$, with $t=j-1$, and $(t,t+1)$ on the opposite arc $\lfloor n/2\rfloor+1\le j\le n-1$, with $t=n-j$, except at $J$ in an odd cycle. At $J$ the base pair is $(s,s)$. On a single arc, equal distance pairs with different values of $t$ require both increments to vanish at the larger $t$, which is impossible. Across the two arcs the difference of coordinates of a common pair can only be zero. This forces row 2 on the first arc and row 0 on the second, and equal values of $t$. The columns are therefore $j$ and $n+1-j$. In the even case the difference $\sigma(n+1-j)-\sigma(j)$ is $\pm1$, and in the odd case it is 4 at $j=J-1$ or 0 elsewhere. None equals 2 modulo $m\ge7$, so the regular colours at these two rows differ.

In the odd cycle, compare $J$ with a first-arc column. The second coordinate is at most $s$ on the first arc and at least $s$ at $J$. Equality forces $j=J-1$ and row 0 at $J$. The first coordinate then forces a nonzero increment $e$ at $J-1$. But row 0 at $J$ has regular colour 2, which occurs at $J-1$ in row 2, where $e=0$. For the other arc, the first coordinate similarly forces $j=J+1$ and row 2 at $J$. The second coordinate forces $f=1$ at $J+1$. The required regular colour 4 occurs there at row 0, where $f=0$. These cases exhaust distinct columns. As for the path, the regular colouring is injective in each column and both singleton vertices are located by their own colours.

Together with the lower bounds, both constructions prove the claimed formula for each graph. The witnesses to Conjecture 3 are $M=7$ and $N=4$.

## Prior work and scope

Behtoei and Omoomi already proved the path formula in Theorem 2 (for $m\ge3,n\ge2$), as well as the colourful-vertex observation and the lower-bound strategy for paths. The argument here rederives the path formula in the range needed for the Lean equality. The journal version prints the same conjecture on p. 234 and the path formula on p. 225. Ghanbari and Mojdeh study the same graph family in *Neighbor Locating Coloring on Graphs: Three Products* (2024), §3.3. Its same-family bounds use the stricter neighbour-locating invariant and its $m+1$ construction for large $m$ treats $C_3$. That construction yields an ordinary upper bound for triangles. For fixed $m,k$, a given colour has at most $2^k$ distinct neighbourhood colour sets, so a uniform neighbour-locating bound of $m+2$ cannot give the large-$n$ branch here. [Behtoei–Omoomi](https://combinatorialpress.com/article/ars/Volume%20126/volume-126-paper-19.pdf) · [Ghanbari–Mojdeh](https://combinatorialpress.com/article/jcmcc/Volume%20122/neighbor-locating-coloring-on-graphs-three-products.pdf)

The result adds the cycle formula in an explicit eventual range. The shared lower bound extends the source’s missing-colour argument. The two cycle upper bounds require coordinating both neighbours in the Hall construction and handling the odd midpoint in the singleton construction. The proof makes no optimality claim for the thresholds.
