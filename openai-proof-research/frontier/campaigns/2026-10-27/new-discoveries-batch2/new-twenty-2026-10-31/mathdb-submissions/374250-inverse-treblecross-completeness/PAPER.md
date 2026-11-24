# Completeness of the regular set in Inverse Treblecross

We prove Conjecture 5.1 of Liang and Li's *A Weak Solution of Inverse Treblecross*, version 1. Every position with at most one piece and Sprague–Grundy value at most 1 lies in the authors' regular set or is one of four specified positions. Each of those four positions lies outside the regular set and has value exactly 1. The proof uses a finite certificate on abstract gap lists. Its soundness, coverage and evaluation are formalized in Lean 4.

Claude Opus 5.5 wrote the original proof, conducted the first review, and completed Lean stage 1. GPT-6.2 Sol conducted the cross-model review and completed Lean stage 2 and the manuscript. GPT-6.1 Terra checked the definitions. A separate GPT-6.2 Sol lane completed the final audit, using the same model family as the manuscript and Lean stage 2 author.

## 1. Statement and definitions

Liang and Li state Conjecture 5.1 in arXiv:2604.16759v1.

> The regular set R contains all board states that possess at most one piece and satisfy G ≤ 1, with exactly four isolated exceptions:
>
> [1X1], [1X4], [4X1], and [4X4].

MathDB 374250 follows version 1. Version 2 quantifies over single-piece boards with both gaps at least 2 and lists three exceptions up to reflection. Of the listed boards, only `[4X4]` satisfies that quantifier. On the version 2 domain, our theorem gives exactly `[4X4]` as the exception and establishes separately that all three listed representatives and the reflection `[4X1]` have value 1 and lie outside the regular set. Version 2's Remark 5.2 also calls `[1X0]` and `[0X1]` outside the regular set, although Definition 4.2 includes them in the exceptional boundary class of value 1. [Liang and Li, version 2](https://arxiv.org/abs/2604.16759v2)

**Board and rules.** The source describes Inverse Treblecross as follows.

> In Inverse Treblecross, the objective is reversed: completing a line of three is strictly prohibited. Consequently, the game is played under the normal play convention, where a player loses when they are faced with a board configuration and possess no legal moves that do not create a three-in-a-row.

The source defines its board notation in §2.

> • Boundaries: The symbols “[” and “]” denote the left and right ends of the board, respectively.  
> • Pieces: The symbol X represents an occupied cell.  
> • Gaps: A natural number n represents a sequence of n consecutive empty cells.  
> • Residue Classes: The symbol n̄ denotes a sequence of empty cells with length k ≡ n (mod 10). Consequently, a notation string containing n̄ represents the set of all positions satisfying this congruence condition.

In Lean, bit `true` holds an X. The game on cell lists is defined by

```lean
def ThreeInRow (s : List Bool) : Prop :=
  ∃ i, s[i]? = some true ∧ s[i + 1]? = some true ∧ s[i + 2]? = some true

def IsMove (s t : List Bool) : Prop :=
  ∃ i, s[i]? = some false ∧ t = s.set i true ∧ ¬ ThreeInRow t

noncomputable def sg (s : List Bool) : ℕ :=
  sInf {n : ℕ | ∀ t, IsMove s t → sg t ≠ n}
termination_by s.count false
decreasing_by exact count_false_lt_of_isMove (by assumption)

def emptyBoard (a : ℕ) : List Bool := List.replicate a false

def board (a b : ℕ) : List Bool := List.replicate a false ++ [true] ++ List.replicate b false
```

Here `sInf` takes the least natural number in the displayed set. The set is nonempty because the board has finitely many options. A legal move decreases the number of false cells by one. These facts justify the mex recursion, including the value 0 on terminal boards.

**Characteristic functions.** The source states that “the map x ↦ x/3 (equivalently x ↦ 7x) acts as a permutation on the residue classes.” The functions in §2 are

\[
\chi_1(a)=\begin{cases}
1 & a/3\in\{0,1,2,3,4\},\\
-1 & \text{Otherwise},
\end{cases}
\qquad
\chi_2(a)=\begin{cases}
1 & a/3\in\{-1,0,1\},\\
-1 & a/3\in\{4,5,6\},\\
0 & \text{Otherwise}.
\end{cases}
\]

Lean uses the ring `ZMod 10` and proves that multiplying by 7 is division by 3 in this ring.

```lean
def div3 (a : ZMod 10) : ZMod 10 := 7 * a

def chi1 (a : ZMod 10) : ℤ := if div3 a ∈ ([0, 1, 2, 3, 4] : List (ZMod 10)) then 1 else -1

def chi2 (a : ZMod 10) : ℤ :=
  if div3 a ∈ ([-1, 0, 1] : List (ZMod 10)) then 1
  else if div3 a ∈ ([4, 5, 6] : List (ZMod 10)) then -1 else 0
```

**The regular set.** Definition 4.4 of version 1 reads, with typography normalized:

> The set of regular positions R = R₁ ∪ R₋₁ is classified as follows:
>
> (1) Class R₁: This class comprises three sub-families of states. Our subsequent analysis will demonstrate that all states in this class have an SG value of 0 (i.e., they are P-positions).
>
> • R₁⁽⁰⁾ (Empty boards): States of the form [a], where χ₁(a) = 1.  
> • R₁⁽¹⁾ (General single-piece boards): States of the form [aXb], where χ₂(a)χ₂(b) = 1.  
> • R₁* (Exceptional boundary states): States belonging to the three specific residue classes [X6̄], [6̄X], and [X4̄X].
>
> (2) Class R₋₁: This class comprises three counterpart sub-families. We will show that all states in this class have an SG value of 1 (a specific subset of N-positions).
>
> • R₋₁⁽⁰⁾ (Empty boards): States of the form [a], where χ₁(a) = −1.  
> • R₋₁⁽¹⁾ (General single-piece boards): States of the form [aXb], where χ₂(a)χ₂(b) = −1.  
> • R₋₁* (Exceptional boundary states): States belonging to the three specific residue classes [X1̄], [1̄X], and [X9̄X].

The complete predicate, including the two-piece states, is

```lean
def R1 (s : List Bool) : Prop :=
  (∃ a : ℕ, s = emptyBoard a ∧ chi1 a = 1) ∨
  (∃ a b : ℕ, s = board a b ∧ chi2 a * chi2 b = 1) ∨
  (∃ k : ℕ, (k : ZMod 10) = 6 ∧ (s = board 0 k ∨ s = board k 0)) ∨
  (∃ k : ℕ, (k : ZMod 10) = 4 ∧ s = [true] ++ List.replicate k false ++ [true])

def Rm1 (s : List Bool) : Prop :=
  (∃ a : ℕ, s = emptyBoard a ∧ chi1 a = -1) ∨
  (∃ a b : ℕ, s = board a b ∧ chi2 a * chi2 b = -1) ∨
  (∃ k : ℕ, (k : ZMod 10) = 1 ∧ (s = board 0 k ∨ s = board k 0)) ∨
  (∃ k : ℕ, (k : ZMod 10) = 9 ∧ s = [true] ++ List.replicate k false ++ [true])

def InR (s : List Bool) : Prop := R1 s ∨ Rm1 s

def exceptions : List (List Bool) := [board 1 1, board 1 4, board 4 1, board 4 4]

def Conjecture51 : Prop :=
  (∀ s : List Bool, s.count true ≤ 1 → sg s ≤ 1 → InR s ∨ s ∈ exceptions) ∧
  (∀ s ∈ exceptions, s.count true ≤ 1 ∧ sg s ≤ 1 ∧ ¬ InR s)
```

## 2. Gap lists and reductions

A nonempty gap list `[g₀,…,gₖ]` represents a board with `g₀` empty cells, an X, `g₁` empty cells, and so on, ending with `gₖ` empty cells. It has exactly the sum of the gaps as its number of empty cells. Filling a cell splits one gap `g` into `j,k` with `g=j+1+k`, and every such split fills a cell. The result contains three consecutive X's exactly when two consecutive internal gaps are both zero. Thus the abstract moves below agree with the literal cell game in both directions.

An independent split gives a disjunctive sum. To see the nim-sum rule, suppose the components have values \(x,y\). In an option, precisely one value changes, so its xor differs from \(x\mathbin{\oplus}y\). For any \(u<x\mathbin{\oplus}y\), take the highest bit where \(u\) and \(x\mathbin{\oplus}y\) differ. This bit is set in exactly one of \(x,y\), say \(x\). The number \(u\mathbin{\oplus}y\) agrees with \(x\) above that bit and clears it, so it is less than \(x\). By mex the first component has a move to that value. This realizes \(u\) in the sum. Induction on the number of empty cells and the mex characterization give the rule, also when a component is terminal.

The checker scans internal gaps for the following splits. They hold on legal boards and continue to hold after legal play.

1. An internal gap of zero is a pair of adjacent X's. A neighboring empty cell on either side is permanently unplayable. Cut at each such cell, delete the pair of X's, and shorten the neighboring gaps by one, using truncated subtraction at the two ends. Each remaining side is independent. Legality excludes a third adjacent X.
2. An internal gap of one has form X·X. The middle cell is permanently unplayable, so cut there. Each triple crossing this cut contains that cell.
3. In an internal gap of four, write the cells \(c_1,c_2,c_3,c_4\). Within either side, occupying both cells of its pair would create a triple with its bounding X. Thus the pair \((c_1,c_2)\) is forbidden on the left and \((c_3,c_4)\) is forbidden on the right. Cut between \(c_2\) and \(c_3\). Each triple crossing the cut contains one of those two pairs, so it cannot be completed under independent legal play.
4. With no such internal split, delete an outside X in an edge pattern X··X, or its reflection. The only constraint from the outside X forbids simultaneous occupation of the two empty cells. The inside X already forbids it. The move trees before and after deletion therefore agree.

Every reduction preserves the Sprague–Grundy value as a nim-sum and the total number of empty cells of the resulting components is at most that of the input. Deleting an unplayable empty cell can decrease this total. Lean proves the move correspondence, the sum rule, and these identities in `TBGame` and `TBGaps`.

## 3. The family and its proposed values

Put \(Z=\{1,4,6,9\}\subseteq\mathbb Z/10\mathbb Z\), the zero set of \(\chi_2\). Define \(\sigma=-1\) on residues 1 and 4 and \(\sigma=1\) on 6 and 9. The family \(F\) and the proposed value \(V\) are as follows.

| Positions | Proposed value |
|---|---|
| Empty boards \([a]\) | \((1-\chi_1(a))/2\) |
| \([aXb]\) with \(\chi_2(a)\chi_2(b)\ne0\) | \((1-\chi_2(a)\chi_2(b))/2\) |
| \([X\bar 6],[\bar 6X],[X\bar 4X]\) | 0 |
| \([X\bar 1],[\bar 1X],[X\bar 9X]\) | 1 |
| \([aXb]\) with exactly one gap \(z\) of residue in \(Z\), outside the regular boundary classes above, and other gap \(o\) | \(2+(1-\sigma(z)\chi_2(o))/2\) |
| \([cXdX]\) and its reflection, with \(c\ge2\), \(\chi_2(c)\ne0\), \(d\ge3\), and \(d\equiv3,8\pmod{10}\) | \((2\text{ if }d\equiv3\text{, else }3)\oplus(1-\chi_2(c))/2\) |
| \([X3X]\) | 2 |
| \([1X1],[1X4],[4X1],[4X4]\) | 1 |

The two-piece family with \(d\equiv3,8\) supplies replies in the induction. For example, for \([aX]\) with \(a\ge9\) and \(a\equiv4,9\), the far-end option \([X(a-1)X]\) can be answered by \([X4X(a-6)X]\). The four-gap split yields \([X2]\oplus[2X(a-6)X]\), whose predicted nim-sum is the predicted value of \([aX]\). The small far-end option \([X3X]\) is included directly.

## 4. The finite certificate and its soundness

The certificate proves two assertions.

1. For every \(P\in F\), every \(u<V(P)\) occurs as the predicted nim-sum of a legal option reduced to members of \(F\). For every legal option \(Q\) of \(P\), either the reduction of \(Q\) has known predicted nim-sum unequal to \(V(P)\), or one reduced component has a legal reply such that its new reduction and the unchanged components have known predicted nim-sum \(V(P)\).
2. Every one-piece position outside \(F\) has legal options whose reductions have predicted nim-sums 0 and 1.

Here is the finite computation and the argument that it covers unbounded lengths. Gap knowledge is either \(e(n)\), meaning exactly \(n\), or \(g(m,r)\), meaning at least \(m\) and congruent to \(r\) modulo 10. For input gaps use the alphabet

\[
 e(0),\ldots,e(12),\quad g(13,0),\ldots,g(13,9).
\]

Assign every concrete gap its exact symbol if less than 13 and otherwise its residue symbol. This assignment always describes the gap. The checker uses the following operations.

- To decide membership in \(F\) and its predicted value, obtain for each gap either its exact value below 5 or its residue with a guaranteed size at least 5. For \(g(m,r)\), the least possible length is \(m+(r-m)\bmod10\), with the residue taken in \(0,\ldots,9\). When this lower bound is at least 5 the checker uses the residue. Canonical inputs always give enough information. Each condition in the table depends only on this information.
- To check legality or perform a reduction, test for exact sizes as required by the rules in §2. Equality with a number \(c\) is refuted for a lower-bound symbol if \(c<m\) or \(c\not\equiv r\pmod{10}\). If a test cannot be decided and the stated branch needs it, that branch gives no certificate. Decrementing a positive gap adjusts both its lower bound and residue. Each returned reduction describes actual components, with correct nim-sum and nonincreasing total empty-cell count. Reduction uses initial fuel equal to the gap-list length. An exhausted or undecidable reduction fails to give a certificate.
- To cover **all** moves of an exact gap, enumerate all splits. For \(g(m,r)\), enumerate the splits with an exact part \(j<7\) on either side and residual part described by \(g(m-1-j,(r-1-j)\bmod10)\). Lower bounds use truncated subtraction. Also enumerate the ten pairs whose two lower bounds are 7, with residues \(s\) and \((r-1-s)\bmod10\), for \(0\le s<10\). If both parts of a concrete split are at least 7, its residues select a pair in this last list. Otherwise its small part selects one of the end splits. Thus every concrete move is covered. The check tolerates extra abstract options by requiring the option test for the entire list.
- To **witness** a move, restrict to exact end offsets. For \(e(n)\), enumerate splits with either part less than the search limit. For \(g(m,r)\), choose \(j<\min(m,L)\) as the end offset and describe the remaining part as above. Every listed split has a realization for every concrete gap satisfying the input symbol. The search limit \(L\) is 100 for moves to required lower values and 5 for replies. The validity of a witness follows from the existence of its concrete split and from the legality and reduction tests on its output.

For an abstract input, `chkP` accepts immediately when it has no family value. Otherwise it checks all lower values through the witness search and checks all covering options. An option is accepted if legality is refuted. Otherwise the checker requires certified legality and a successful reduction. When all reduced components have family values, their nim-sum must differ from the input value. When a component has no certified value, the checker requires the reply in assertion 1. In the reply search, if the unchanged components have known nim-sum \(w\), the selected component must have a move whose reduced nim-sum is \(V(P)\oplus w\). The test for assertion 2 accepts an input with known family value or checks both witness searches for 0 and 1.

Enumerate the following input vectors, letting \(a,b\) range independently over the 23 canonical symbols.

| Inputs | Test |
|---|---|
| \([a]\) | `chkP` |
| \([a,b]\) | `chkP` and the family-or-two-options test |
| \([a,b,e(0)]\), \([e(0),b,a]\) | `chkP` |

Every row returns true. The full enumeration consists of 23 single-gap cases, 529 two-gap cases, and 1,058 three-gap cases counting the two orientations separately. The same 529 two-gap cases are used for the second test. Of the candidate entries, 589 have a family value, counting 23 single-gap entries, 452 two-gap entries, and 114 three-gap entries. This count includes five duplicate entries from the overlapping orientations. The other 77 two-gap entries require the two-option check. The counts can be reproduced by running `python3 -I -B scripts/abs_check.py 7 13 5` from the formalization packet. Each row result is proved by kernel reduction in `TBCert00` through `TBCert22`, with `TBCheck` supplying the functions above. The concrete move is covered before wall normalization. Every abstract reduction then carries the updated lower bounds and residues into the next test, including the reply search after a wall split. This establishes coverage directly at the level of abstract gap knowledge. The family-value function returns no value for the empty list or for lists of more than three gaps, and its three-gap case requires a zero end gap. In `TBAssembly`, `canon_mem` places every canonical symbol in the enumerated alphabet, and the row-dispatch theorems give the checks on each input shape. In `TBEndpoint`, `canonOK_checked` combines these facts for every member of \(F\), while `low_single` applies the two-gap test to every single-piece board. The finite step therefore comes from universal coverage of lengths by residue classes and sound split abstractions. In `TBSound`, `hasVal_sound` extracts moves and `optAll_sound` excludes the proposed value from all options under the induction hypothesis.

The earlier written proof used a separate concrete enumeration with each input gap bounded by 52. To reproduce that diagnostic check, use the following command from the original proof lane.

```sh
XCX='{}' SMALLX='{3:2}' EFAM='{3:2,8:3}' LOC=6 EDGE2=1 python3 -I -B scripts/tb_verify.py 52
```

The original Python verifier selects a different family with its default settings. The formal proof uses the abstract enumeration above, with its own checked coverage and reply bounds.

## 5. Induction and conclusion

We show \(G(P)=V(P)\) for all \(P\in F\) by strong induction on the number of empty cells. A move followed by reductions has fewer empty cells in total than the starting board. The same bound holds for each component of that reduction and for each component after a reply. Hence every family value cited by the certificate in assertion 1 is correct by the induction hypothesis. Each required lower value is therefore attained by an option. An option with a known unequal value cannot have value \(V(P)\). In the reply case, the reduced option has a component whose move gives value \(V(P)\oplus w\), where \(w\) is the value of the unchanged components. The component's current value differs from \(V(P)\oplus w\) by mex. Its xor with \(w\) consequently differs from \(V(P)\). This proves the mex conditions and completes the induction.

Every empty board lies in the regular set. A one-piece board in \(F\) either lies in the regular set, has a predicted value at least 2, or is one of the four displayed exceptions with predicted value 1. A one-piece board outside \(F\) has options of values 0 and 1 by assertion 2 and the proven family values. Its mex is at least 2. Each exception has both gaps in \(Z\) and both gaps positive, so it fails the general and boundary criteria for regular one-piece boards. A one-piece board cannot belong to the empty-board or two-piece parts of the regular set. Every list with at most one true cell is either an empty board or has the form \([aXb]\). The theorem follows.

Lean proves this last classification on cell lists and proves that the one-piece restriction of `InR` is exactly the stated characteristic-function and boundary predicate. The endpoint `ITB.conjecture_5_1` has type `Conjecture51`. A second endpoint, `ITB.conj_5_1`, states the same conclusion using the empty and one-piece board forms.

## 6. Scope and prior work

The result settles which positions with at most one piece have value at most 1. The induction also gives exact values for a mixed-residue family of single-piece boards and the auxiliary family of two-piece boards used in their replies. In the mixed-residue case, the cross-model review found that the lower bound alone follows from two explicit placements and the published empty-board sequence. The both-zero-residue case uses new values from the extended family. For single-piece boards outside the certified family the theorem gives a lower bound. A proof of Conjecture 5.3 on periodicity for all single-piece values and a strong solution for arbitrary partially occupied boards are outside the scope of this result.

Liang and Li's weak solution evaluates the regular set and gives the empty-board sequence. Their reduction-move arguments certify values 0 and 1 on those families. They leave completeness conjectural. Kai Liang's later automaton paper reports that its algorithm fails to produce an outcome DFA for all Inverse Treblecross positions and poses the problem of finding weak solutions automatically. The automaton paper uses the published empty-board result and the regular family, and leaves the completeness conjecture unaddressed. The final audit found no prior proof in the searched citation index, Principia archive, registry snapshots, or live Omega issue and pull-request searches. The new ingredients here are the larger certified family and the finite split analysis giving coverage at arbitrary lengths. [Liang and Li, version 1](https://arxiv.org/abs/2604.16759v1) · [Liang, arXiv:2608.13273v2](https://arxiv.org/abs/2608.13273v2)
