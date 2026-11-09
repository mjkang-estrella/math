#!/usr/bin/env python3
"""Editable manuscript source. Builds paper/tabminors-draft.pdf with ReportLab (no TeX).
ReportLab is loaded from ../tmp/pdf-deps (a copy of the bundle used by sibling lanes)."""
from pathlib import Path
import sys, re
W = Path(__file__).resolve().parent
sys.path.insert(0, str(W.parent / 'tmp/pdf-deps'))
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle, KeepTogether
from reportlab.lib.styles import ParagraphStyle
from reportlab.lib import colors
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont

F = '/usr/share/fonts/'
fonts = {'Body': 'liberation-serif-fonts/LiberationSerif-Regular.ttf', 'BodyB': 'liberation-serif-fonts/LiberationSerif-Bold.ttf',
         'BodyI': 'liberation-serif-fonts/LiberationSerif-Italic.ttf', 'BodyBI': 'liberation-serif-fonts/LiberationSerif-BoldItalic.ttf',
         'Mono': 'liberation-mono-fonts/LiberationMono-Regular.ttf', 'Sym': 'gdouros-symbola/Symbola.ttf'}
for n, f in fonts.items(): pdfmetrics.registerFont(TTFont(n, F + f))
pdfmetrics.registerFontFamily('Body', normal='Body', bold='BodyB', italic='BodyI', boldItalic='BodyBI')
CMAP = {f: set(pdfmetrics.getFont(f).face.charToGlyph) for f in ['Body', 'Mono']}

def fb(s, base='Body'):
    """Escape nothing; wrap characters missing from the base font in the Symbola font."""
    out = []
    for part in re.split(r'(<[^>]+>|&[a-z]+;)', s):
        if part.startswith('<') or part.startswith('&'): out.append(part); continue
        for ch in part:
            out.append(ch if ord(ch) < 128 or ord(ch) in CMAP[base] else f'<font name="Sym">{ch}</font>')
    return ''.join(out)

body = ParagraphStyle('body', fontName='Body', fontSize=10.2, leading=13.4, spaceAfter=6.5, alignment=4)
small = ParagraphStyle('small', parent=body, fontSize=8.8, leading=11.2, spaceAfter=4, alignment=0)
mono = ParagraphStyle('mono', parent=small, fontName='Mono', fontSize=8.2, leading=10.4)
head = ParagraphStyle('head', parent=body, fontName='BodyB', fontSize=12.2, leading=15.5, spaceBefore=6, spaceAfter=6, alignment=0)
title = ParagraphStyle('title', parent=head, fontSize=16.5, leading=20.5, spaceBefore=0, spaceAfter=8)
disp = ParagraphStyle('disp', parent=body, leftIndent=22, alignment=0)
story = []
P = lambda s, st=body: story.append(Paragraph(fb(s), st))
H = lambda s: story.append(Paragraph(fb(s), head))
D = lambda s: story.append(Paragraph(fb(s), disp))

def table(rows, widths, st=small):
    t = Table([[Paragraph(fb(str(x), 'Mono' if st is mono else 'Body'), st) for x in r] for r in rows], colWidths=widths, hAlign='LEFT', repeatRows=1)
    t.setStyle(TableStyle([('VALIGN', (0, 0), (-1, -1), 'TOP'), ('BACKGROUND', (0, 0), (-1, 0), colors.HexColor('#e9eef3')),
                           ('LINEBELOW', (0, 0), (-1, 0), .5, colors.grey), ('LINEBELOW', (0, -1), (-1, -1), .5, colors.grey),
                           ('LEFTPADDING', (0, 0), (-1, -1), 4), ('RIGHTPADDING', (0, 0), (-1, -1), 4),
                           ('TOPPADDING', (0, 0), (-1, -1), 2), ('BOTTOMPADDING', (0, 0), (-1, -1), 3)]))
    return t

# ---------------------------------------------------------------- front matter
story.append(Paragraph(fb('Two hook tableaux of size 12 with equal multisets of 8-minors: the k + 4 conjecture for tableau reconstruction fails'), title))
P('<b>DRAFT</b>, 2 November 2026. MathDB problem 359279. Prepared with AI assistance (Claude Opus 5.5 research lanes in an automated campaign). '
  'No human authorship or affiliation is asserted. The counterexample was found by computer search. It has been reviewed independently, but this draft has not been peer reviewed and carries zero accepted campaign credit until root acceptance.', small)
P('<b>Abstract.</b> Erickson, Herden, Meddaugh, Sepanski, Hammon, Mohn and Ruiz-Bolanos conjectured that for k ≥ 1 and n ≥ k + 4, the multiset mM<sub>k</sub>(T) of k-minors determines a standard Young tableau T of size n. They report a computer verification for k ≤ 5. '
  'We exhibit two distinct hook tableaux of size 12 whose multisets of 8-minors coincide. This refutes the conjecture at the smallest admissible size n = k + 4 for k = 8. The refutation is checked in the Lean 4 kernel against literal definitions of jeu de taquin deletion and of the multiset over all deletion sequences. '
  'An elementary weight formula for minors of hooks then shows, by pigeonhole, that no bound of the form n ≥ k + c works for any constant c. This second argument is ordinary mathematics and is not Lean-verified.')

# ---------------------------------------------------------------- 1
H('1. Source definitions and the conjecture')
P('We follow Section 2 of the source [1]; quotations are from arXiv:2307.13161 v1, whose e-print we read. The journal version [2] appeared in J. Combin. Theory Ser. A 209 (2025), article 105950. Its body was not read (Section 7), so we cannot confirm that its numbering or wording is identical.')
P('<b>Tableaux.</b> YT(n) is the set of standard Young tableaux of size n over [1, n], in English convention. Rows are left-justified and weakly decrease in length from the top, and the entries 1, …, n each occur once and strictly increase along every row and down every column.')
P('<b>Deletion T − m</b> (jeu de taquin). Delete the cell with entry m, leaving an empty space. Iterate the following: if a cell lies directly to the right of or directly below the empty space, slide the one with the smaller entry into the empty space. '
  'This terminates when neither cell exists, that is, at an outer corner, and that cell is removed. Finally, subtract 1 from each entry larger than m. The result is an element of YT(n − 1), denoted T − m. The source illustrates this on a tableau of shape (5, 5, 4, 2, 1, 1); our Lean controls reproduce that figure.')
P('<b>Minors.</b> A k-minor of T is a tableau obtained by iteratively deleting k cells via jeu de taquin. M<sub>k</sub>(T) is the set and mM<sub>k</sub>(T) the multiset of all k-minors. '
  'The multiset is counted over deletion <i>sequences</i>: the proof of the source theorem labelled thm: exp lower bound states “there are n(n−1)⋯(n−k+1) minors in total”. Equivalently,')
D('mM<sub>0</sub>(T) = {T},    mM<sub>k+1</sub>(T) = Σ<sub>m=1</sub><super>n</super> mM<sub>k</sub>(T − m)    (T ∈ YT(n)).')
P('A reading over subsets of cells is not even well defined, because relabelling makes later entries depend on the order of the deletions.')
P('<b>Conjecture</b> (source label conj:k+4). <i>Let k ≥ 1. Let T ∈ YT(n), where n ≥ k + 4. Then mM<sub>k</sub>(T) determines T.</i> That is, T ↦ mM<sub>k</sub>(T) is injective on YT(n). '
  'The source states: “We have been able to verify the following conjecture by computer for k ≤ 5.” It also proves the sharp bound n ≥ 8 for sets of 2-minors, a cubic sufficient bound for multisets, and conjectures n ≥ k<super>2</super> + 2k for sets. MathDB 359279 restates conj:k+4 literally; its record and hash are in the dossier.')

# ---------------------------------------------------------------- 2
H('2. The counterexample')
P('<b>Theorem 1.</b> Let T<sub>1</sub> be the hook of shape (5, 1<super>7</super>) with first row 1 5 7 8 12 and first column 1 2 3 4 6 9 10 11. Let T<sub>2</sub> be the hook of shape (6, 1<super>6</super>) with first row 1 2 3 7 10 11 and first column 1 4 5 6 8 9 12. '
  'Then T<sub>1</sub> and T<sub>2</sub> are distinct elements of YT(12), and mM<sub>8</sub>(T<sub>1</sub>) = mM<sub>8</sub>(T<sub>2</sub>). Consequently, Conjecture conj:k+4 is false: it fails for k = 8 and n = 12 = k + 4.')
P('Each multiset has 12!/4! = 19,958,400 elements. Every minor is a hook of size 4; the two tableaux of the non-hook shape (2, 2) do not occur. The common multiplicities are listed below, with rows separated by “/”.')
story.append(table([['size-4 minor', 'multiplicity', 'size-4 minor', 'multiplicity'],
                    ['1 / 2 / 3 / 4', '3,064,320', '1 2 3 / 4', '1,693,440'],
                    ['1 2 / 3 / 4', '2,540,160', '1 2 4 / 3', '2,540,160'],
                    ['1 3 / 2 / 4', '3,628,800', '1 3 4 / 2', '2,056,320'],
                    ['1 4 / 2 / 3', '3,709,440', '1 2 3 4', '725,760']], [105, 80, 105, 80]))
story.append(Spacer(1, 7))
P('<b>Proof.</b> Both fillings are standard, and the shapes differ. A <i>weighted list</i> is a finite list L = [(U<sub>1</sub>, c<sub>1</sub>), …, (U<sub>r</sub>, c<sub>r</sub>)] of tableaux with natural weights. Its denotation is')
D('den<sub>k</sub>(L) = Σ<sub>i</sub> c<sub>i</sub> · mM<sub>k</sub>(U<sub>i</sub>).')
P('Let step(L) replace each pair (U, c) by the pairs (U − m, c) for m = 1, …, |U|, and then merge equal tableaux by adding their weights. Two facts give soundness:')
P('(i) by the recursion for mM<sub>k+1</sub>, den<sub>k+1</sub>(L) equals den<sub>k</sub> of the unmerged list;')
P('(ii) merging two entries (U, a) and (U, b) into (U, a + b) preserves a weighted sum of the form Σ c<sub>i</sub> · f(U<sub>i</sub>), for any f.')
P('Hence den<sub>k+1</sub>(L) = den<sub>k</sub>(step L) for every k and L, and mM<sub>k</sub>(T) = den<sub>k</sub>([(T, 1)]). Write A<sub>0</sub> = [(T<sub>1</sub>, 1)] and A<sub>i+1</sub> = step A<sub>i</sub>; define B<sub>i</sub> from T<sub>2</sub> in the same way. Then')
D('mM<sub>8</sub>(T<sub>1</sub>) = den<sub>8</sub>(A<sub>0</sub>) = den<sub>7</sub>(A<sub>1</sub>) = ⋯ = den<sub>0</sub>(A<sub>8</sub>),')
P('and similarly mM<sub>8</sub>(T<sub>2</sub>) = den<sub>0</sub>(B<sub>8</sub>). Here den<sub>0</sub> is the literal weighted multiset, and it is invariant under permuting the list. '
  'The lists A<sub>8</sub> and B<sub>8</sub> are permutations of one another; both equal the table above. The sixteen lists A<sub>1</sub>, …, A<sub>8</sub> and B<sub>1</sub>, …, B<sub>8</sub> are written out explicitly in the Lean file. Their lengths are 6, 16, 28, 36, 34, 26, 16, 8 and 6, 18, 34, 44, 42, 29, 16, 8. '
  'Each identity step A<sub>i</sub> = A<sub>i+1</sub> is a finite computation with jeu de taquin on at most 44 tableaux. The equality mM<sub>8</sub>(T<sub>1</sub>) = mM<sub>8</sub>(T<sub>2</sub>) follows. □')
P('<b>Certificate chain.</b> Every one of the 16 step identities, and the final permutation, is checked by the Lean kernel (Section 5). Three further checks were made independently of Lean’s deletion function. '
  'An independent reviewer reimplemented deletion from the source text in Python and found that all sixteen Lean literals equal the true level-by-level multisets. '
  'A second small Python check for this manuscript recomputes mM<sub>8</sub>(T<sub>1</sub>) and mM<sub>8</sub>(T<sub>2</sub>), compares them with the Lean literals A<sub>8</sub> and B<sub>8</sub>, and confirms that mM<sub>k</sub>(T<sub>1</sub>) ≠ mM<sub>k</sub>(T<sub>2</sub>) for k = 1, …, 7. '
  'It also reproduces the source’s deletion figure.')

# ---------------------------------------------------------------- 3
H('3. Hook shapes: no constant c works')
P('<i>This section is ordinary mathematics. It is <b>not</b> Lean-verified.</i> A hook H of size n = N + 1 is encoded by a word w ∈ {A, L}<super>N</super>. Letter t records whether entry t + 1 lies in the arm (first row) or in the leg (first column). The map w ↦ H(w) is a bijection onto the hooks in YT(n).')
P('<b>Lemma 2.</b> For N ≥ 1, deleting 1 or 2 from H(w) removes the first letter of w; deleting m ≥ 3 removes letter m − 1.')
P('<i>Proof.</i> For m ≥ 3, the cell m has a neighbour only within its own line, and that line slides back by one. For m = 2, the cell 2 is adjacent to the corner, and its line slides back. For m = 1, the smaller neighbour of the corner is 2. It slides into the corner, and the gap then runs along the line of 2 to its end. After relabelling, the result coincides with that of deleting 2. □')
P('<b>Lemma 3</b> (weight formula). For 1 ≤ k ≤ N − 1,')
D('mM<sub>k</sub>(H(w)) = k! · Σ<sub>P ⊆ [N], |P| = N − k</sub> min(P) · {H(w|<sub>P</sub>)}.')
P('<i>Proof.</i> By Lemma 2, a length-k deletion sequence removes the letters of Q = [N] \\ P one at a time, in some order. Every intermediate word has length at least 2. A step that removes the current first letter arises from two entries, namely 1 and 2; any other step arises from exactly one entry. '
  'A letter q > min P is never first, since min P survives. Put j = min P − 1. A letter q ≤ j is first when it is removed exactly when it comes last among {1, …, q} in the relative order of the letters 1, …, j. '
  'For a uniform random relative order, these j events are independent with probabilities 1/q, so the weighted count is j! Π<sub>q≤j</sub>(1 + 1/q) = (j + 1)!. '
  'Interleaving with the remaining k − j letters gives C(k, j) · (k − j)! · (j + 1)! = k! · min P. □')
P('<b>Theorem 4.</b> For every integer c ≥ 2 and every sufficiently large k, mM<sub>k</sub> is not injective on YT(k + c). Hence for no constant c does “n ≥ k + c implies that mM<sub>k</sub>(T) determines T” hold for all k ≥ 1. '
  'Let f(k) be the least n<sub>0</sub> such that mM<sub>k</sub> is injective on YT(n) for all n ≥ n<sub>0</sub>; it exists by the source’s cubic bound. Then f(k) − k → ∞.')
P('<i>Proof.</i> For a constant c ≤ 4, the bound is already refuted by Theorem 1, since 12 ≥ 8 + c. For the asymptotic statement, fix c ≥ 2, put r = c − 1, take N large, and set n = N + 1 and k = N − r ≥ 1, so that n = k + c and k ≤ N − 1. By Lemma 3,')
D('mM<sub>k</sub>(H(w)) = k! Σ<sub>τ ∈ {A,L}<super>r</super></sub> V<sub>τ</sub>(w) · {H(τ)},    where V<sub>τ</sub>(w) = Σ<sub>|P| = r, w|<sub>P</sub> = τ</sub> min P.')
P('The hooks H(τ) are distinct, so mM<sub>k</sub>(H(w)) and the vector V(w) determine each other. Each coordinate lies in [0, N·C(N, r)], so V takes at most (N·C(N, r) + 1)<super>2<super>r</super></super> values. This is polynomial in N, and hence below 2<super>N</super> for large N. '
  'By pigeonhole, two distinct words have the same vector V. Their hooks are distinct tableaux in YT(k + c) with equal mM<sub>k</sub>. As N ranges over all large integers, so does k. □')
P('For c = 5, an explicit hook collision occurs at n = 16, k = 11. The first hook has first row 1 2 3 4 5 9 10 11 12 13 16 and first column 1 6 7 8 14 15. The second has first row 1 4 5 6 7 8 12 13 14 15 and first column 1 2 3 9 10 11 16. '
  'Both have equal mM<sub>11</sub>, with 16!/5! = 174,356,582,400 minors each. This was confirmed three times: by the discovering lane, by the independent reviewer, and by this manuscript’s check, which also verifies Lemma 3 on both hooks.')
P('The reduction yields a weighted, start-position-sensitive subword deck rather than the classical k-deck of a word. Theorem 4 needs only the counting bound above and makes no use of word-reconstruction results.')

# ---------------------------------------------------------------- 4
H('4. Computational picture (diagnostic)')
P('<i>The following is diagnostic; only Theorem 1 is formally verified.</i> Two independent exhaustive sweeps were run over YT(n). One is the discovering lane’s C program, which propagates two independent random 64-bit linear hashes. The other is the reviewer’s exact Python enumeration for n ≤ 12. They agree as follows.')
P('• At n = k + 4, mM<sub>k</sub> is injective on YT(k + 4) for every k ≤ 7, which extends the authors’ range k ≤ 5. It first fails at k = 8.')
P('• At n = 12 and k = 8 there are exactly <b>4 colliding pairs (8 tableaux)</b> among the 140,152 elements of YT(12). They are the pair of Theorem 1, the hook pair with first rows {1, 5, 6, 8, 12} and {1, 2, 3, 6, 10, 11}, and the transposes of both pairs. This corrects the discovering lane’s note, which spoke of “4 colliding rows”.')
P('• At n = k + 5, mM<sub>k</sub> is injective for k ≤ 7 (both sweeps) and for k = 8, 9, 10 (lane sweep only). The first failure is the hook pair at k = 11 above.')
P('• The lane also reports collisions at n = k + 4 for k = 9, 10 and 11, the absence of c = 6 hook collisions up to n = 26, and non-hook collisions from n = 13 on. These were not rechecked.')

# ---------------------------------------------------------------- 5
H('5. Formal verification in Lean 4')
P('The file formal/TabMinors.lean (sha256 66fee9a4…5fd7) contains the definitions and the kernel proof. It is checked with Lean 4.34.1 (commit 5045d005…) against the cached mathlib d13f23b7…. Its main declarations are as follows.')
story.append(table([
    ['Lean declaration', 'Meaning'],
    ['Tab', 'List (List ℕ): the rows of a tableau, top to bottom.'],
    ['IsSYT n T', 'Rows are nonempty; row lengths weakly decrease; rows strictly increase; columns strictly increase; the flattened entries are a permutation of 1, …, n.'],
    ['slide fuel T i j', 'Jeu de taquin from the gap (i, j): compare the cells (i, j+1) and (i+1, j), move the smaller one in, and remove the final outer corner. The stale gap value is never read. Each move raises i + j, so the fuel size T always suffices.'],
    ['del T m', 'T − m: locate m, call slide (size T) T i j, then subtract 1 from the entries larger than m.'],
    ['minors k T', 'mM<sub>k</sub>(T) as a Multiset: minors 0 T = {T}, and minors (k+1) T is the sum over m = 1, …, size T of minors k (del T m), i.e. one term per deletion sequence.'],
    ['Conjecture', '∀ k n, 1 ≤ k → k + 4 ≤ n → ∀ T U, IsSYT n T → IsSYT n U → minors k T = minors k U → T = U.'],
    ['den k L', 'The weighted denotation Σ c • minors k U over (U, c) in L.'],
    ['step L', 'One deletion level: flatMap over the entries of the list, then norm, which merges equal tableaux (ins/norm).'],
    ['minors_eq_den', 'minors k T = den k [(T, 1)].'],
    ['chain', 'step L = L′ → den (k+1) L = den k L′ (via den_succ, sum_norm, sum_ins).'],
    ['den_perm', 'A.Perm B → den k A = den k B.'],
    ['T₁, T₂', 'The two hooks of Theorem 1; T₁_syt, T₂_syt and T₁_ne_T₂ are kernel decisions.'],
    ['not_conjecture', '¬ Conjecture, by applying a hypothetical proof at k = 8, n = 12 to minors_eq.'],
], [92, 403]))
story.append(Spacer(1, 7))
P('<b>Certificates.</b> The theorems hA1–hA8 and hB1–hB8 establish the sixteen step identities by decide +kernel, and hAB proves A<sub>8</sub>.Perm B<sub>8</sub>. The certificates A1_ok–B8_ok check that every listed minor at level i is a standard Young tableau of size 12 − i. '
  'Merging never discards a tableau, so these certificates confirm on every tableau actually reached that del removed exactly one cell, that is, the fuel was never exhausted. Controls.lean reproduces the source’s deletion figure T − 8. '
  'It also reproduces the source’s n = 7 pair, which has equal sets M<sub>2</sub> but different multisets mM<sub>2</sub>. Two negative controls must fail: NegControl1 asserts A8 = B8 as lists (they are only permutations), and NegControl2 asserts a wrong chain step.')
P('<b>The noncomputable annotations.</b> The discovering lane’s file was accepted with an annotation-only change: root added noncomputable to slide, del, minors, den, ins, norm and step. '
  'For structurally recursive definitions the compiler otherwise emits auxiliary _unsafe_rec companions marked partial. The root’s full flag audit found three of them (minors, slide, ins). The audit rejects any partial or unsafe constant, even a compiler-generated one. '
  'With the annotation, no code is generated and no such companions exist. The kernel still unfolds the definitions, and every decide +kernel certificate is unchanged. The diff consists of exactly seven one-word additions.')
P('<b>Axioms and trust.</b> #print axioms TabMinors.not_conjecture reports exactly propext, Classical.choice and Quot.sound. AuditFull.lean enumerates all 140 constants of module TabMinors, generated ones included. '
  'It fails if any constant is unsafe or partial, lacks a body, is a local axiom, or depends on an axiom outside those three. The source contains no sorry, admit, axiom, unsafe, native_decide or ofReduceBool. '
  'Trust limits: the Lean kernel and leanchecker; the pinned mathlib cache, which was used read-only and not rebuilt from source; and the statement correspondence above, which was checked against the source text by an independent (AI) fidelity review, not proved.')
P('<b>Replay.</b> Root replayed this exact file set (strict -DwarningAsError=true builds, leanchecker on TabMinors, AuditFull and Controls, both negative controls rejected) and recorded PASS. '
  'The dossier contains a portable driver (replay.py, with LEAN_BIN and LEAN_PACKAGES) for the final fresh replay of the source-only archive. This manuscript lane did not run Lean.')

# ---------------------------------------------------------------- 6
H('6. Related work')
P('Monks [3] solved the partition reconstruction problem of Pretzel and Siemons and posed the tableau analogue. Cain and Lehtonen [4] settled k = 1 for sets. The source [1, 2] settles k = 2 for sets (sharp bound n ≥ 8) and gives a cubic bound for multisets. '
  'Jiradilok [5] studies reconstruction of <i>partitions</i> from multisets of k-minors, where multiplicities count standard skew tableaux. He proves that partitions of n are reconstructible exactly when k ≤ G(n), with n − G(n) = O(n/log n). '
  'This concerns a different object and implies nothing about tableaux. However, it is the natural comparison for Theorem 4, which shows that for tableaux the gap n − k needed for reconstruction is unbounded.')
P('Herden’s slides for the Rutgers Experimental Mathematics Seminar of 27 February 2025 [6] postdate the journal version and still present n ≥ k + 4 as a conjecture (slides 22–23). The DIMACS listing of the same talk [7] describes the multiset bound only as “a first step toward a sharp bound in the general multiset case”. '
  'The sibling MathDB record 359278 concerns the set version (source conjecture conj:k^2 + 2k, n ≥ k<super>2</super> + 2k for sets M<sub>k</sub>) and is not addressed here. We make no priority claim beyond the bounded searches recorded in the dossier: OpenAlex listed no work citing [2] as of 3 November 2026, and topical searches and public proof-registry screens were negative.')

# ---------------------------------------------------------------- 7
H('7. Access limits')
P('The journal body of [2] was not read: the publisher route was excluded, and the journal metadata comes from OpenAlex. An unverified search snippet places the multiset conjecture there as Conjecture 7.2. '
  'Of [3]–[5], only what [1] quotes, or the abstract, was read. The arXiv listing of [1] shows only version 1 (24 July 2023).')

# ---------------------------------------------------------------- references
H('References')
refs = [
    '[1] W. Q. Erickson, D. Herden, J. Meddaugh, M. R. Sepanski, C. Hammon, J. Mohn, I. Ruiz-Bolanos, Young tableau reconstruction via minors, arXiv:2307.13161 v1 (2023). <i>Read in full (e-print source), including the definitions, Theorem thm: exp lower bound and the concluding remarks.</i>',
    '[2] The same authors, Young tableau reconstruction via minors, J. Combin. Theory Ser. A 209 (2025) 105950, doi:10.1016/j.jcta.2024.105950. <i>Metadata only; body not read.</i>',
    '[3] M. Monks, The solution to the partition reconstruction problem, J. Combin. Theory Ser. A 116 (2009) 76–91. <i>Not read; cited via [1].</i>',
    '[4] A. J. Cain, E. Lehtonen, Reconstructing Young tableaux, J. Combin. Theory Ser. A 187 (2022) 105578. <i>Not read; cited via [1].</i>',
    '[5] P. Jiradilok, Reconstructing partitions from their multisets of k-minors, arXiv:1610.05354 (2016). <i>Abstract read.</i>',
    '[6] W. Erickson, D. Herden (speaker), J. Meddaugh, M. Sepanski, C. Hammon, J. Mohn, I. Ruiz-Bolanos, Young tableau reconstruction via minors, slides, Rutgers Experimental Mathematics Seminar, 27 February 2025, sites.math.rutgers.edu/~zeilberg/expmath/herden2025.pdf. <i>Read (text extraction).</i>',
    '[7] DIMACS seminar listing, Young tableau reconstruction via minors (talk of 27 February 2025), dimacs.rutgers.edu/dimacsevents/seminar-details/young-tableau-reconstruction-v. <i>Read (abstract page).</i>',
    '[8] MathDB problem 359279, Linear-bound multiset reconstruction conjecture for tableau minors, mathdb.com/p/359279. <i>Record read from the cached corpus line.</i>',
]
for r in refs: P(r, small)

def footer(c, d):
    c.saveState(); c.setFont('Body', 8.5); c.setFillColor(colors.grey)
    c.drawString(52, 26, 'DRAFT  |  MathDB 359279  |  AI-assisted, not peer reviewed'); c.drawRightString(543, 26, str(d.page)); c.restoreState()
doc = SimpleDocTemplate(str(W / 'tabminors-draft.pdf'), pagesize=(595.28, 841.89), leftMargin=52, rightMargin=52, topMargin=46, bottomMargin=46,
                        title='Two hook tableaux of size 12 with equal multisets of 8-minors', author='AI-assisted draft (no human author asserted)',
                        subject='MathDB 359279', creator='ReportLab')
doc.build(story, onFirstPage=footer, onLaterPages=footer)
print('built', W / 'tabminors-draft.pdf')
