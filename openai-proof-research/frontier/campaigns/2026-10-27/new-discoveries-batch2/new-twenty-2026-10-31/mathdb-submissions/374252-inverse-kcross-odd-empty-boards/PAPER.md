# The empty-board Grundy values of odd Inverse $k$-cross

For every odd $k=2m+1$, the Sprague–Grundy value of the empty board of length $n$ is
$$
g_k(n)=\bigl(n+\mathbf{1}_{n\bmod(3m+2)\ge k}\bigr)\bmod2.
$$
The formula follows from a strategy that either player can use to force the same number of unmarked cells at the end of the game. It implies Liang and Li's conjecture: the bound $g_k\le1$ and both identities. For $k=3$ it gives a short new proof of their main theorem.

## The conjecture and game

Liang and Li, *A Weak Solution of Inverse Treblecross*, state the conjecture as Conjecture 5.5 in the v1 PDF and as Conjecture 5.4 in the v2 PDF. The mathematical text is the same in both versions. The v2 wording reads as follows. [v1, §5.3](https://arxiv.org/pdf/2604.16759v1#page=15) [v2, §5.3](https://arxiv.org/pdf/2604.16759v2#page=13)

> For Inverse $k$-cross with $k=2m+1$ ($m\geq 1$), the SG value of the empty board $[a]$ satisfies $\mathcal{G}([a])\leq 1$. Furthermore,
>
> $$
> \mathcal{G}([2+3m+a])=\mathcal{G}([a])\oplus(m\bmod 2),\qquad
> \mathcal{G}([2+5m-a])=\mathcal{G}([a])\oplus(m\bmod 2).
> $$

No range of $a$ is printed. The board $[a]$ is defined only for integers $a\ge0$, so we read the translation for every $a\ge0$. We read the reflection for $0\le a\le5m+2$, the range where both boards have nonnegative length. The proof below also covers $m=0$. That case is outside the conjecture: Inverse $1$-cross has no legal move, so every value is $0$.

The game is the source's. Players alternate placing a single X in an empty cell of a $1\times n$ strip. Placement "is strictly prohibited if it completes a contiguous sequence of $k$ pieces" (v1, §5.3), and in v2 a move "is prohibited if it completes a run of $k$ pieces". Play is normal: "a player loses when they face a position with no legal move" (v2, §1). The Sprague–Grundy value of a position is the mex ("minimum excluded value") of the values of its options, and $\oplus$ is "the bitwise XOR" (v2, §2). [v1](https://arxiv.org/pdf/2604.16759v1) [v2, §2](https://arxiv.org/html/2604.16759v2#S2)

In Lean, a position is the finset $S$ of its unmarked cells, and the empty board $[n]$ is $\mathrm{Icc}(1,n)$. Legality and the available placements are defined as
$$
\begin{aligned}
\operatorname{Legal}(k,n,S)&\iff
\forall a\in\mathbb N,\; 1\le a\text{ and }a+k\le n+1
\implies \exists x\in S,\; a\le x<a+k,\\
\operatorname{options}(k,n,S)&=\{x\in S:\operatorname{Legal}(k,n,S\setminus\{x\})\}.
\end{aligned}
$$
Every option has one fewer unmarked cell. Lean defines `grundy k n S` as the mex of $\{\operatorname{grundy}(k,n,S\setminus\{x\}):x\in\operatorname{options}(k,n,S)\}$ by well-founded recursion. Here `mex` is the least natural number not in the set, and `^^^` is XOR on natural numbers. A position with no option has value $0$, so the player to move there loses, as in normal play.

The Lean lemmas `boardCuts_empty`, `boardCuts_legal_iff`, `boardCuts_place` and `boardCuts_source_move_iff` match the cut-set model with a Boolean board. On a Boolean board the cells have indices $0,\ldots,n-1$, and `true` marks an X. The lemmas identify the empty board, legality, the board after a placement, and the legal placements. In particular, on a legal board a placement on an empty cell is allowed exactly when no window of $k$ cells containing that cell becomes entirely marked. This is a move-for-move correspondence. Lean defines no separate Grundy function on Boolean boards; equality of the two Grundy functions follows from these lemmas by induction on the number of empty cells. For example, `odd_inverse_kcross_nonvacuous` certifies that at $k=3$ the empty board $[4]$ has a legal move on its second cell and has Grundy value $1$.

Set $P=3m+2$ and write $n=qP+r$ with $0\le r<P$. We will show that either player, moving first or second, can enforce that exactly
$$
2q+\mathbf{1}_{r\ge k}
\tag{1}
$$
cells are unmarked at the end of the game. The same holds when the board is played in a disjunctive sum with $*1$, an independent game with a single move. In either game, the player who benefits from the resulting parity of the number of moves can use this strategy.

## 1. Gaps and the block layout

Number the board cells $1,\ldots,n$ and add virtual endpoints $0$ and $n+1$. Call the unmarked cells *cuts*. A board is legal exactly when every gap between consecutive cuts or endpoints is at most $k$. A move deletes a cut and must leave a legal board. Any superset of a legal set of cuts is legal.

Put $s=m+1$, so $P=k+s$ and $k=2s-1$. If $n<k$, every cell can be marked and (1) is immediate. Otherwise lay out $q$ full blocks of $P$ cells each. Each block has an anchor interval of $k$ cells followed by a middle interval of $s$ cells. Within each anchor, the first $s$ cells are low and the remaining $m$ cells are high. The $r$ remaining cells are placed as follows.

- If $r<k$, split them between a prefix and a suffix of at most $m$ cells each. This is possible because $r\le2m$.
- If $r\ge k$, append a final anchor of $k$ cells with no middle interval. Put the remaining $r-k\le m$ cells in a prefix, with no suffix. The final anchor has low and high cells like the others.

## 2. Local supports

Let $i\in[1,s]$ be the index of a low cut and $z\in[1,s]$ the index of a middle cut in the same full block. They form a supporting pair if $i\ge z$, because their gap is then $k+z-i\le k$. Any low cut in the final anchor is a supporting singleton. Initially, each full block contains the $s$ disjoint supporting pairs with $i=z$, and the final anchor contains $s$ disjoint supporting singletons.

Call a block finished when all its high cells are marked. Every legal board has a cut in every anchor, because an anchor is an interval of $k$ cells. In a finished full block, the last anchor cut therefore has index at most $s$. Suppose the middle interval contained no cut. Then the next cut or virtual endpoint would come no earlier than the first position after the block, so the gap would be at least $P+1-s=k+1$. Hence the middle interval contains a cut, and the last anchor cut and the first middle cut form a supporting pair. A finished final anchor contains a supporting singleton. Thus in every legal state, every finished block has a support.

Conversely, choosing one support per block gives a legal board with exactly the number of cuts in (1). We check every gap.

- Inside a block, the gap within a support is at most $k$.
- From a middle cut $z$ to a low cut $i$ of the next anchor, the gap is $s-z+i\le2s-1=k$.
- From $0$ to the first low cut, the gap is at most $m+s=k$.
- If the last cut lies in a middle interval, its gap to the end is at most $s+m=k$, by the bound on the suffix.
- If the last cut lies in the final anchor, its gap to the end is at most $k$, because the anchor ends just before the virtual endpoint.

Any set containing one support per block is therefore legal.

## 3. Strategy forcing the terminal count

Designate either player as the defender. Until all blocks are finished, the defender plays as follows. If the opponent has just played in a block that is still unfinished, the defender marks a high cell of that block. Otherwise the defender marks a high cell of any unfinished block. The defender may also be the first to move. A move in the prefix or suffix, or the single move of $*1$, counts as a move outside the blocks.

In an unfinished block, let $d$ count the marked high cells and $b$ the marked cells that are not high. We claim that $b\le d$ in each unfinished block just before every opponent turn. This holds at the start. An opponent move marks one cell, so it can violate the inequality in at most one unfinished block, and there by at most one. The defender restores it by marking a high cell of that block. An opponent move that finishes a block leaves the inequalities of the other blocks unchanged.

The defender's high-cell move is legal. Before a defender move, each unfinished block has $b\le d+1\le m$, so at least one of its $s=m+1$ disjoint initial supports is intact. Marking a high cell does not touch that support, even when the move finishes the block. Each other unfinished block keeps an intact initial support, and each finished block keeps the support given by legality. By the gluing argument of §2, the new state is legal.

A board is not terminal while some block is unfinished. Before either player's turn, every unfinished block has an intact initial support, so a high cell can legally be marked. Once all blocks are finished, the defender may make any legal move. From then on every legal state contains a support in each block, since the high cells stay marked. Choose one support per block. Every cut outside the chosen set can be deleted legally, since the result contains the chosen set and is therefore legal. So a terminal board consists of exactly the chosen cuts. Hence, from either starting order, every play in which the defender follows this strategy ends with exactly (1) unmarked cells. In the sum with $*1$, its single move has also been made by the end.

## 4. Sprague–Grundy value and both identities

Let $e=\mathbf{1}_{r\ge k}$. In the board game, every play in which the defender follows the strategy lasts exactly $n-2q-e$ moves. The player who benefits from that parity can be the defender, so the board is a first-player win exactly when $n-2q-e$ is odd. In the sum with $*1$ the count is one larger. The two games therefore have opposite outcomes.

The board is a loss for the player to move exactly when its Sprague–Grundy value $G$ is zero. By the Sprague–Grundy sum theorem, the sum with $*1$ has value $G\oplus1$, so it is a loss for the player to move exactly when $G=1$. If $n-2q-e$ is even, the board is a loss for the player to move, so $G=0$. If it is odd, the sum is a loss for the player to move, so $G=1$. Since $n-2q-e$ and $n+e$ have the same parity, this proves the formula.

Translation by $P$ preserves the exceptional residue set $[k,P-1]$, and it changes the parity of the length by $m\bmod2$, since $P\equiv m\pmod 2$. For $0\le a\le5m+2$, the reflection $a\mapsto5m+2-a$ sends a residue $u$ to $(2m-u)\bmod P$. For $u\le2m$ this is $2m-u$. For $2m+1\le u\le P-1$ it is $P+2m-u$, which again lies in $[2m+1,P-1]$. Thus reflection preserves $e$, and the two reflected lengths sum to $5m+2\equiv m\pmod 2$. Since the formula takes only the values $0$ and $1$, adding $m\bmod2$ modulo two is XOR with $m\bmod2$. This proves the translation for all $a\ge0$ and the reflection for $0\le a\le5m+2$.

*Remark.* The formula says slightly more than the conjecture. Reflection maps the lengths $2m+1,\ldots,3m+1$ among themselves, and translation only moves them upward. So the two identities, together with the base values $\mathcal G([a])=a\bmod 2$ for $a<k$, do not fix the $m$ values on $[k,P-1]$. The formula gives them as $(n+1)\bmod 2$. This qualifies the source's remark that the recurrence determines all empty-board values from the base cases $a<k$.

## Significance and prior work

Liang and Li proved the conjecture only for $k=3$ (their Theorem 1.1, the case $m=1$). Their proof is an induction over regular positions, about eight pages in v2 (about ten in v1), using two characteristic functions on $\mathbb Z/10\mathbb Z$ and reduction moves. For general odd $k$ they gave a table of values for $k\le13$ and boards of length up to $25$. They wrote that their reduction-move strategy "is insufficient" for these patterns, which likely require "more sophisticated tools". The argument here is short and elementary. Its block layout lets either player control the number of cuts left at the end, and it yields a single closed formula for every odd $k$. The case $m=1$ gives a much shorter proof of their main theorem. The result is modest. It is a parity formula for one family of empty boards, proved with a fixed-length strategy of a kind familiar in combinatorial game theory. It says nothing about the boards with pieces that the source leaves open, or about even $k$.

MathDB 374250, resolved separately in this campaign, is a different conjecture from the same paper (§5.1): coverage of regular one-piece positions at $k=3$. Its proof is a finite residue-periodic certificate over boards with two pieces, and it takes the known $k=3$ empty-board values as input. It neither implies nor is implied by the present result. [Liang–Li, v2](https://arxiv.org/abs/2604.16759v2)

Prior-art searches on 2026-11-23 found no journal version, no arXiv version after v2 (16 October 2026), and no public resolution of the conjecture. The searches covered arXiv, OpenAlex, web search, GitHub code search, the issues of the Omega registry, the `mxym/math` repository, and local copies of the Principia, Omega, `mio-qwq/math` and `openai/math` archives. OpenAlex lists one citing work, Liang's *A Finite Automaton Approach to Combinatorial Games*. Its §5.3 discusses the $k=3$ weak solution, and its Problem 5.5 asks about finding weak solutions automatically. It gives no result for general odd $k$. The Semantic Scholar citation list could not be queried (rate-limited). [Liang](https://arxiv.org/abs/2608.13273v2)

## Provenance and formal verification

GPT-6.2 Sol lanes found the proof, wrote the Lean formalization and wrote the paper. Claude Opus 5.5 lanes reviewed it: an adversarial review before the formalization, and a final check of the definitions, the paper and the prior art afterwards. All of this is AI work; no human has checked the result. The Lean module proves the formula, the conjecture's bound and both identities, and the correspondence of legal moves between the two board models. Lean 4.34.1 compiled the module, and the standalone kernel checker accepted its object file. It was rebuilt independently from the source appendix and accepted by the kernel; the only axioms used are `propext`, `Classical.choice` and `Quot.sound`.
