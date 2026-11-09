"""Build paper.pdf (DRAFT manuscript for MathDB 355956) with ReportLab.

Run:  python3 write_paper.py      (needs reportlab; fonts from the system paths below)
Mini-markup inside strings: ^{..} superscript, _{..} subscript, `code` monospace,
<i>, <b> as in ReportLab.  Glyphs missing from Liberation Serif fall back to
Noto Sans Math automatically.
"""
import hashlib, json, pathlib, re
from reportlab.lib import colors
from reportlab.lib.enums import TA_CENTER, TA_JUSTIFY
from reportlab.lib.pagesizes import letter
from reportlab.lib.styles import ParagraphStyle
from reportlab.lib.units import inch
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.platypus import KeepTogether, Paragraph, SimpleDocTemplate, Spacer, Table, TableStyle

O = pathlib.Path(__file__).resolve().parent
FONTS = {
    'Serif': '/usr/share/fonts/liberation-serif-fonts/LiberationSerif-Regular.ttf',
    'Serif-Bold': '/usr/share/fonts/liberation-serif-fonts/LiberationSerif-Bold.ttf',
    'Serif-Italic': '/usr/share/fonts/liberation-serif-fonts/LiberationSerif-Italic.ttf',
    'Serif-BoldItalic': '/usr/share/fonts/liberation-serif-fonts/LiberationSerif-BoldItalic.ttf',
    'Mono': '/usr/share/fonts/liberation-mono-fonts/LiberationMono-Regular.ttf',
    'NMath': '/usr/share/fonts/google-noto/NotoSansMath-Regular.ttf',
}
for k, v in FONTS.items():
    pdfmetrics.registerFont(TTFont(k, v))
pdfmetrics.registerFontFamily('Serif', normal='Serif', bold='Serif-Bold', italic='Serif-Italic', boldItalic='Serif-BoldItalic')
SERIF_CMAP = TTFont('probe', FONTS['Serif']).face.charToGlyph
MONO_CMAP = TTFont('probe2', FONTS['Mono']).face.charToGlyph


def fallback(s, cmap):
    return ''.join('<font name="NMath">%s</font>' % c if ord(c) > 127 and ord(c) not in cmap else c for c in s)


def fmt(s):
    parts = s.split('`')
    out = []
    for i, part in enumerate(parts):
        if i % 2:
            code = part.replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;')
            out.append('<font name="Mono" size="8.6">%s</font>' % fallback(code, MONO_CMAP))
        else:
            while True:     # innermost braces first, so nested scripts become nested tags
                new = re.sub(r'\^\{([^{}]*)\}', r'<super rise="3.4" size="7">\1</super>', part)
                new = re.sub(r'_\{([^{}]*)\}', r'<sub rise="2.2" size="7">\1</sub>', new)
                if new == part:
                    break
                part = new
            out.append(fallback(part, SERIF_CMAP))
    return ''.join(out)


ST = {
    'title': ParagraphStyle('title', fontName='Serif-Bold', fontSize=15.5, leading=19, alignment=TA_CENTER, spaceAfter=6),
    'status': ParagraphStyle('status', fontName='Serif-Italic', fontSize=9, leading=11.5, alignment=TA_CENTER,
                             textColor=colors.HexColor('#7a1f1f'), spaceAfter=8),
    'abs': ParagraphStyle('abs', fontName='Serif', fontSize=9.6, leading=14, alignment=TA_JUSTIFY,
                          leftIndent=0.35 * inch, rightIndent=0.35 * inch, spaceAfter=6),
    'h': ParagraphStyle('h', fontName='Serif-Bold', fontSize=11.6, leading=14, spaceBefore=8, spaceAfter=3),
    'h2': ParagraphStyle('h2', fontName='Serif-Bold', fontSize=10.3, leading=13, spaceBefore=5, spaceAfter=2),
    'p': ParagraphStyle('p', fontName='Serif', fontSize=10, leading=14.6, alignment=TA_JUSTIFY, spaceAfter=4.5),
    'stmt': ParagraphStyle('stmt', fontName='Serif-Italic', fontSize=10, leading=14, alignment=TA_JUSTIFY,
                           leftIndent=0.25 * inch, rightIndent=0.25 * inch, spaceAfter=5, spaceBefore=1),
    'cell': ParagraphStyle('cell', fontName='Serif', fontSize=8.4, leading=12.2),
    'cellb': ParagraphStyle('cellb', fontName='Serif-Bold', fontSize=8.4, leading=11.6),
    'ref': ParagraphStyle('ref', fontName='Serif', fontSize=8.9, leading=11.8, leftIndent=16, firstLineIndent=-16, spaceAfter=2.5),
    'code': ParagraphStyle('code', fontName='Mono', fontSize=7.9, leading=9.6, leftIndent=0.2 * inch, spaceAfter=5),
}

story = []
P = lambda s, st='p': story.append(Paragraph(fmt(s), ST[st]))


def table(rows, widths, header=True, size=None):
    data = [[Paragraph(fmt(c), ST['cellb'] if (header and i == 0) else ST['cell']) for c in r] for i, r in enumerate(rows)]
    t = Table(data, colWidths=widths, repeatRows=1 if header else 0, hAlign='CENTER')
    t.setStyle(TableStyle([
        ('GRID', (0, 0), (-1, -1), 0.4, colors.HexColor('#8a8a8a')),
        ('BACKGROUND', (0, 0), (-1, 0), colors.HexColor('#ececec') if header else colors.white),
        ('VALIGN', (0, 0), (-1, -1), 'TOP'),
        ('TOPPADDING', (0, 0), (-1, -1), 2), ('BOTTOMPADDING', (0, 0), (-1, -1), 2.5),
        ('LEFTPADDING', (0, 0), (-1, -1), 3.5), ('RIGHTPADDING', (0, 0), (-1, -1), 3.5)]))
    story.append(KeepTogether([t, Spacer(1, 6)]) if len(rows) <= 12 else t)
    if len(rows) > 12:
        story.append(Spacer(1, 6))


TITLE = 'The prime field is not a maximal clique in GP(5<super rise="6" size="10.5">8</super>, 3): a Lean-certified counterexample to Yip’s maximal subfield clique conjecture'
P(TITLE, 'title')
P('DRAFT research manuscript, 1 November 2026. No human authorship or affiliation is asserted. Prepared with AI assistance '
  '(Claude Opus 5.5) within a user-directed research campaign. Zero accepted campaign credit; final replay, paper review '
  'and acceptance are reserved to the campaign root.', 'status')
P('<b>Abstract.</b> For d &gt; 1 and a prime power q ≡ 1 (mod 2d) of the prime p, Yip conjectured that the largest '
  'subfield 𝔽_{p^{r}} with d ∣ (q−1)/(p^{r}−1) is a maximal clique of the generalized Paley graph GP(q,d), whose '
  'edges join elements of 𝔽_{q} differing by a nonzero d-th power. We show that this fails for q = 5^{8} and d = 3. Here the largest admissible r '
  'is 1, and in every field with 5^{8} elements the prime field 𝔽_{5} is a clique that extends to the strictly larger clique '
  '𝔽_{5} ∪ {x}, where x = 2θ + 4θ^{2} + θ^{3} and θ is any root of X^{8} + X^{7} + 2X^{6} + 2. The proof uses a Frobenius chain '
  'certificate and ten explicit cube and inverse certificates; every step can be checked by hand or with a short computation. '
  'The negation of the conjecture, stated with literal definitions, is proved in Lean 4 with Mathlib using only the '
  'standard axioms. We also give ordinary proofs, outside the formal endpoint, that 𝔽_{5} ⊕ x𝔽_{5} is a 25-clique and that '
  '𝔽_{5} is a maximal subfield clique. The latter shows that the hypothesis q &gt; (n−1)^{2} of Yip’s 2023 theorem cannot '
  'simply be dropped, contrary to a conjecture stated there. That theorem itself remains valid.', 'abs')

P('1. Introduction', 'h')
P('Let p be an odd prime, q a power of p, d &gt; 1 and q ≡ 1 (mod 2d). The <i>d-Paley graph</i> GP(q,d) has vertex set 𝔽_{q}; '
  'distinct g, h are adjacent iff g − h ∈ (𝔽_{q}^{*})^{d}, the set of nonzero d-th powers. The congruence makes −1 a d-th '
  'power, so the graph is undirected. If d ∣ (q−1)/(p^{k}−1), every nonzero element of the subfield 𝔽_{p^{k}} is a d-th '
  'power, so 𝔽_{p^{k}} is a clique. This observation of Broere, Döman and Ridley is quoted in [1, Theorem 1.3]. '
  'Yip conjectured that the largest such subfield is always maximal [1, Conjecture 1.4]:')
P('Conjecture (Yip). Let d &gt; 1 be an integer. Let q ≡ 1 (mod 2d) be a power of a prime p, and let r be the largest '
  'integer such that d ∣ (q−1)/(p^{r}−1). Then the subfield 𝔽_{p^{r}} forms a maximal clique in GP(q,d).', 'stmt')
P('The same statement is Conjecture 1.1 of [2], and it is MathDB problem 355956 [6]. In [2], Theorem 1.2 proves the following. '
  'If q^{n} ≡ 1 (mod 2d), q &gt; (n−1)^{2}, and 𝔽_{q} is a maximal subfield clique of GP(q^{n},d), then 𝔽_{q} is a maximal clique. '
  'Note that in Theorem 1.2, q denotes the size of the base field. The abstract of [2] says that this “confirms a conjecture of '
  'Yip”, and a remark after the proof adds: “We conjecture that the condition q&gt;(n−1)^{2} in Theorem 1.2 can be dropped.” '
  'The same remark reports SageMath verification for n ≤ 5 (all q ≤ (n−1)^{2}) and for n = 6 with q ≤ 17. '
  'A later paper [3, §1] restates [2] without the size hypothesis: “if a generalized Paley graph GP(q,d) admits a clique which '
  'is a subfield of 𝔽_{q} and K is the largest such subfield, the author [Y23] used character sum estimates to show that K is a '
  'maximal clique.” It adds: “It is also tempting to conjecture that ω(GP(q,d)) = |K|.”')
P('<b>Main result.</b> The unrestricted conjecture is false.')
P('<b>Theorem 1.</b> Let K be any field with 5^{8} = 390625 elements, and let θ ∈ K be a root of '
  'f = X^{8} + X^{7} + 2X^{6} + 2 (such a root exists). Put x = 2θ + 4θ^{2} + θ^{3}. Then 𝔽_{5} ⊂ K is a clique of GP(5^{8},3), '
  'x ∉ 𝔽_{5}, and 𝔽_{5} ∪ {x} is a clique. In particular 𝔽_{5} is not a maximal clique.', 'stmt')
P('<b>Corollary 2.</b> Yip’s conjecture is false at (q, d) = (5^{8}, 3), where the largest admissible r is 1.', 'stmt')
P('Theorem 1 and Corollary 2 are certified in Lean (Section 5). Section 4 contains two further statements with ordinary '
  'proofs only: the 25-clique 𝔽_{5} ⊕ x𝔽_{5}, and the fact that 𝔽_{5} is a maximal subfield clique. It also lists '
  'computational diagnostics. Theorem 1.2 of [2] is not contradicted, because there the base field has 5 ≤ (8−1)^{2} = 49 '
  'elements. What fails is the unrestricted conjecture. The remark-conjecture in [2] that the size hypothesis can be dropped '
  'fails as well.')

P('2. Definitions and the exact statement', 'h')
P('Throughout, K is a finite field with q = p^{m} elements, and (K^{*})^{d} = {y^{d} : y ∈ K, y ≠ 0}. GP(q,d) is the graph on K '
  'in which g ∼ h iff g − h ∈ (K^{*})^{d}. A <i>clique</i> is a set C ⊆ K whose distinct elements are pairwise adjacent. A '
  '<i>maximal clique</i> is a clique C such that every clique C′ ⊇ C equals C. For r ∣ m, the subfield 𝔽_{p^{r}} of K is '
  '{z ∈ K : z^{p^{r}} = z}. The quotient (q−1)/(p^{r}−1) in the conjecture is meant as an integer. This forces r ≥ 1 and '
  'p^{r} − 1 ∣ p^{m} − 1, that is, r ∣ m. So r is the largest element of')
P('A(p, m, d) = { r ≥ 1 : (p^{r}−1) ∣ (p^{m}−1) and d ∣ (p^{m}−1)/(p^{r}−1) }.', 'stmt')
P('With these definitions the conjecture reads: <i>for all d &gt; 1, all primes p, all m ≥ 1 and all fields K with |K| = p^{m} '
  'and p^{m} ≡ 1 (mod 2d), if r = max A(p,m,d), then 𝔽_{p^{r}} is a maximal clique of GP(p^{m},d).</i> All fields of order '
  'p^{m} are isomorphic and the property is isomorphism-invariant, so quantifying over every K is equivalent to the source’s '
  '“𝔽_{q}”. A refutation needs one admissible (d, p, m), and Theorem 1 holds for every K of order 5^{8}.')

P('3. Proof of Theorem 1', 'h')
P('3.1 The parameters.', 'h2')
P('q − 1 = 390624 = 2^{5}·3·13·313 = 6·65104, so q ≡ 1 (mod 6). Since p^{r} − 1 ∣ p^{m} − 1 iff r ∣ m, the candidates are '
  'r ∈ {1, 2, 4, 8}. Their quotients are listed below, and only r = 1 is admissible. Hence the conjecture asserts that '
  '𝔽_{5} is a maximal clique of GP(5^{8},3).')
table([['r', '1', '2', '4', '8'], ['(q−1)/(5^{r}−1)', '97656 = 3·32552', '16276 ≡ 1 (mod 3)', '626 ≡ 2 (mod 3)', '1']],
      [1.2 * inch, 1.25 * inch, 1.25 * inch, 1.15 * inch, 0.6 * inch])
P('3.2 Characteristic and the prime field.', 'h2')
P('The characteristic of K is a prime dividing |K| = 5^{8}, so it is 5. In characteristic 5, '
  'z^{5} − z = z(z−1)(z−2)(z−3)(z−4), so {z ∈ K : z^{5} = z} = {0,1,2,3,4} = 𝔽_{5}.')
P('3.3 A root of f in K.', 'h2')
P('In 𝔽_{5}[X]/(f) let t be the class of X; since X^{8} ≡ 4X^{7} + 3X^{6} + 3, classes are represented by polynomials of degree '
  'at most 7. Write B_{i} for the residue of X^{5i} mod f. In characteristic 5, (Σ c_{i}t^{i})^{5} = Σ c_{i}t^{5i} for '
  'c_{i} ∈ 𝔽_{5}. Hence, if t^{5^{k}} = P_{k}(t) with P_{k} = Σ c_{i}X^{i}, then P_{k+1} = Σ c_{i}B_{i}: one multiplication by '
  'the 8 × 8 Frobenius matrix whose rows are the B_{i}. Coefficients are listed from X^{0} to X^{7}.')
rowsB = [[0, '1 0 0 0 0 0 0 0'], [1, '0 0 0 0 0 1 0 0'], [2, '2 2 3 0 0 0 2 3'], [3, '4 1 0 2 4 2 1 1'],
         [4, '4 2 0 0 3 4 0 4'], [5, '2 3 0 3 2 4 4 4'], [6, '0 3 3 0 2 2 3 3'], [7, '1 3 3 0 4 0 4 4']]
rowsP = [[0, '0 1 0 0 0 0 0 0'], [1, '0 0 0 0 0 1 0 0'], [2, '2 3 0 3 2 4 4 4'], [3, '4 3 4 3 0 1 2 0'],
         [4, '1 0 3 4 3 2 1 0'], [5, '4 0 2 4 1 0 1 1'], [6, '4 1 2 3 0 4 0 1'], [7, '4 2 4 3 4 3 2 4'],
         [8, '0 1 0 0 0 0 0 0']]
data = [['i', 'B_{i} = X^{5i} mod f', 'k', 'P_{k} with t^{5^{k}} = P_{k}(t)']]
for j in range(9):
    b = rowsB[j] if j < 8 else ['', '']
    data.append([str(b[0]), '`%s`' % b[1] if b[1] else '', str(rowsP[j][0]), '`%s`' % rowsP[j][1]])
table(data, [0.35 * inch, 1.75 * inch, 0.35 * inch, 2.05 * inch])
P('Since P_{8} = X, t^{5^{8}} = t, so f divides X^{5^{8}} − X in 𝔽_{5}[X] and therefore in K[X]. In K[X], '
  'X^{|K|} − X = ∏_{a∈K}(X − a). By unique factorisation, the monic polynomial f is a product of 8 distinct linear factors '
  'over K, so a root θ ∈ K exists. Irreducibility of f is not needed here. The formal proof performs the same eight steps over '
  'K, inside AdjoinRoot(f). Each step is an exact identity P_{k}(T)^{5} − P_{k+1}(T) = A_{k}(T)f(T) + 5B′_{k}(T) in ℤ[T], '
  'and these identities are checked by `linear_combination`.')
P('3.4 Cube certificates; why −1 is a cube.', 'h2')
P('For each a ∈ 𝔽_{5}, the Lean module contains polynomials y_{a}, h_{a} of degree at most 7 with y_{a}^{3} ≡ x − a and '
  '(x − a)h_{a} ≡ 1 modulo (f, 5), where x = 2X + 4X^{2} + X^{3}:')
table([['a', 'y_{a} (X^{0} … X^{7})', 'h_{a} (X^{0} … X^{7})'],
       ['0', '`0 4 3 3 2 3 0 0`', '`3 2 2 0 4 4 4 3`'], ['1', '`3 4 4 4 1 1 0 4`', '`2 3 3 0 0 3 4 3`'],
       ['2', '`4 4 3 4 4 3 1 2`', '`2 1 2 0 2 3 2 3`'], ['3', '`2 1 0 4 0 0 4 0`', '`2 4 2 4 0 1 1 0`'],
       ['4', '`0 0 1 2 2 4 0 3`', '`1 0 1 2 2 2 1 0`']], [0.35 * inch, 1.9 * inch, 1.9 * inch])
P('Evaluating at θ gives x − a = y_{a}(θ)^{3} and (x − a)·h_{a}(θ) = 1 in K. Hence x − a ≠ 0, so y_{a}(θ) ≠ 0, and x − a is a '
  'nonzero cube. Checking one certificate means one product of polynomials of degree at most 7, reduced mod f over 𝔽_{5}. '
  'Moreover a − x = (−y_{a}(θ))^{3}, because −1 = (−1)^{3} is a cube. More generally, q ≡ 1 (mod 2d) gives d ∣ (q−1)/2, so '
  '−1 = g^{(q−1)/2} is a d-th power for any generator g of K^{*}. Finally, every w ∈ 𝔽_{5}^{*} has w^{4} = 1, so '
  'w = w^{9} = (w^{3})^{3} is a cube.')
P('3.5 The extension; proofs of Theorem 1 and Corollary 2.', 'h2')
P('Differences of distinct elements of 𝔽_{5} are nonzero elements of 𝔽_{5}, hence cubes, so 𝔽_{5} is a clique. '
  'By §3.4, x ≠ a, and both x − a and a − x are nonzero cubes, for every a ∈ 𝔽_{5}. Thus 𝔽_{5} ∪ {x} is a clique that strictly '
  'contains 𝔽_{5}, which proves Theorem 1. For Corollary 2, take (d, p, m) = (3, 5, 8). Then d &gt; 1, 5 is prime, '
  '5^{8} ≡ 1 (mod 6), and max A(5,8,3) = 1 by §3.1. The conjecture would make 𝔽_{5} a maximal clique, contradicting Theorem 1. ∎')
P('3.6 Supplement: irreducibility via the Frobenius orbit.', 'h2')
P('This step is not used above and is not formalised. Since f ∣ X^{5^{8}} − X, f is squarefree and each of its irreducible '
  'factors over 𝔽_{5} has degree dividing 8. If f were reducible, every factor would have degree 1, 2 or 4 and so would divide '
  'X^{5^{4}} − X. Because the factors are distinct, f would then divide X^{625} − X, forcing P_{4} = X. The table shows '
  'P_{4} ≠ X, so f is irreducible. Thus 𝔽_{5}[X]/(f) is a concrete model of 𝔽_{5^{8}}, in which the Frobenius orbit '
  'θ, θ^{5}, …, θ^{5^{7}} has exact length 8. Rabin’s test gives the same answer: gcd(f, P_{4} − X) = 1.')

P('4. Consequences beyond the formal endpoint', 'h')
P('The two propositions below have complete ordinary proofs built from Theorem 1. They are <b>not</b> part of the Lean '
  'endpoint.')
P('<b>Proposition 3.</b> V = 𝔽_{5} ⊕ x𝔽_{5} is a clique of size 25 in GP(5^{8},3); hence ω(GP(5^{8},3)) ≥ 25.', 'stmt')
P('<i>Proof.</i> Take distinct u = a + bx and v = a′ + b′x in V. If b = b′, then u − v = a − a′ ∈ 𝔽_{5}^{*}, which is a cube. '
  'If b ≠ b′, then u − v = (b − b′)(x − c) with c = (a′ − a)/(b − b′) ∈ 𝔽_{5}. This is a product of two nonzero cubes, hence '
  'a nonzero cube. Finally |V| = 25, because x ∉ 𝔽_{5}. ∎ This is the two-dimensional clique predicted by Yip’s lemma '
  '[1, §2].')
P('<b>Proposition 4.</b> 𝔽_{5} is a maximal subfield clique of GP(5^{8},3): none of 𝔽_{25}, 𝔽_{625}, 𝔽_{5^{8}} is a clique.', 'stmt')
P('<i>Proof.</i> Let L be a subfield of K. The differences of distinct elements of L are exactly the elements of L^{*}, so L '
  'is a clique iff L^{*} ⊆ (K^{*})^{3}. Now K^{*} is cyclic of order q − 1, and L^{*} is its unique subgroup of order |L| − 1. '
  'The cubes form the unique subgroup of index 3, of order (q − 1)/3. So L^{*} ⊆ (K^{*})^{3} iff |L| − 1 divides (q − 1)/3, '
  'that is, iff 3 ∣ (q − 1)/(|L| − 1). For |L| = 25, 625 and 5^{8}, the quotients 16276, 626 and 1 are not divisible by 3. ∎ '
  'So the largest subfield clique has 5 elements, and Proposition 3 shows that the guess ω(GP(q,d)) = |K| mentioned in '
  '[3, §1] (where K denotes the largest subfield clique) fails here: ω(GP(5^{8},3)) ≥ 25 &gt; 5.')
P('Apply [2, Theorem 1.2] with base field 𝔽_{5}, n = 8 and d = 3. Then 5^{8} ≡ 1 (mod 6), and 𝔽_{5} is a maximal subfield '
  'clique by Proposition 4, yet 𝔽_{5} is not a maximal clique by Theorem 1. The theorem is consistent with this, because its '
  'hypothesis 5 &gt; (8−1)^{2} fails. The remark in [2] that the condition q &gt; (n−1)^{2} “can be dropped” is therefore false. '
  'The case lies outside the computer checks reported in [2] (n ≤ 5; n = 6 with q ≤ 17). It is also outside the special '
  'case of [4] (n an odd prime, q &gt; n^{2}) and the regime q &gt; (d−1)^{2} for GP(q^{d},d) quoted in [5].')
P('<b>Computational diagnostics (corroboration only; never premises).</b> '
  'An exhaustive discrete-log count over K, in this dossier’s standard-library script, finds exactly 960 elements y ∉ 𝔽_{5} '
  'with 𝔽_{5} ∪ {y} a clique; x is one of them. An independent review script found the same count. None of the 960 lies in '
  '𝔽_{625}, consistent with Yip’s verification for n ≤ 5, which covers GP(625,3). The script also confirms that θ is a '
  'primitive element and that generators of 𝔽_{25}^{*} and 𝔽_{625}^{*} are non-cubes. Finally, the lane that found the '
  'counterexample searched every admissible case with q ≤ 5·10^{6} outside the range of [2, Theorem 1.2] (26 fields, 219 cases) '
  'and found only this failure. That search was not re-run here, and none of these counts is a Lean result.')

P('5. Formal verification', 'h')
P('The module `Yip355956.lean` (22,623 bytes, sha256 `0ccf6655…ee9d7be`) is copied byte-for-byte from the authoring lane. '
  'It imports only Mathlib, uses Lean 4.34.1 (commit `5045d005`), and Mathlib `d13f23b7`. Its literal statement of the '
  'conjecture is:')
def code_block(lines):
    out = []
    for line in lines:
        esc = line.replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;')
        esc = fallback(esc, MONO_CMAP)
        n = len(line) - len(line.lstrip(' '))
        out.append('&nbsp;' * n + esc[n:] if esc.startswith(' ' * n) else esc)
    story.append(Paragraph('<br/>'.join(out), ST['code']))


code_block(['def YipConjecture : Prop :=',
            '  ∀ (d p m : ℕ) (K : Type) [Field K] [Finite K], 1 < d → p.Prime → 0 < m →',
            '    Nat.card K = p ^ m → p ^ m ≡ 1 [MOD 2 * d] →',
            '    ∀ r : ℕ, IsGreatest (admissibleR p m d) r → IsMaximalGPClique K d (subfieldSet K (p ^ r))',
            'theorem yip_conjecture_false : ¬ YipConjecture'])
P('`YipConjectureSG` is identical, except that its conclusion is '
  '`Maximal (fun s => (GPGraph K d).IsClique s) (subfieldSet K (p ^ r))` with `GPGraph K d := SimpleGraph.fromRel (GPAdj K d)`. '
  'It is refuted by `yip_conjecture_SG_false`. Both endpoints instantiate `GaloisField 5 8`, whose cardinality is proved, so '
  'the refutation is not vacuous. The table below lists every definition and every key lemma.')
corr = [['Lean name', 'Formal content (abridged)', 'Mathematical role'],
        ['`dPowers K d`', '{w | ∃ y, y ≠ 0 ∧ y^d = w}', '(K^{*})^{d}, connection set'],
        ['`GPAdj K d g h`', 'g − h ∈ dPowers K d', 'adjacency in Cay(K^{+}, (K^{*})^{d})'],
        ['`IsGPClique K d C`', '∀ u v ∈ C, u ≠ v → GPAdj u v', 'clique'],
        ['`IsMaximalGPClique`', 'clique ∧ ∀ C′ clique, C ⊆ C′ → C′ = C', 'maximal clique'],
        ['`subfieldSet K pr`', '{z | z^pr = z}', '𝔽_{p^{r}} inside K (r ∣ m)'],
        ['`admissibleR p m d`', '{r | 0 &lt; r ∧ p^r−1 ∣ p^m−1 ∧ d ∣ (p^m−1)/(p^r−1)}', 'A(p,m,d); r = its greatest element'],
        ['`YipConjecture`', 'displayed above', 'the conjecture, all quantifiers'],
        ['`admissibleR_greatest`', 'IsGreatest (admissibleR 5 8 3) 1', '§3.1: r = 1'],
        ['`five_eq_zero_of_card`, `mem_subfieldSet_iff`', '|K| = 5^8 → 5 = 0;  z^5 = z ↔ z ∈ {0,…,4}', '§3.2'],
        ['`fK_dvd`', '(5 : K) = 0 → f ∣ X^(5^8) − X in K[X]', '§3.3 Frobenius chain'],
        ['`exists_root`', '|K| = 5^8 → ∃ θ, θ^8+θ^7+2θ^6+2 = 0', '§3.3 splitting'],
        ['`cube_a`, `inv_a` (a = 0…4)', 'y_a(θ)^3 = wit θ − a;  (wit θ − a)·h_a(θ) = 1', '§3.4 certificates'],
        ['`wit_sub_mem`', 'x − a, a − x ∈ dPowers K 3 ∧ x ≠ a', '§3.4, incl. −1 a cube'],
        ['`small_sub_mem`', 'a ≠ b in {0,…,4} → a − b ∈ dPowers K 3', '𝔽_{5} is a clique'],
        ['`not_maximal_of_card`', '|K| = 5^8 → clique ∧ ¬ maximal', 'Theorem 1'],
        ['`yip_conjecture_false`', '¬ YipConjecture', 'Corollary 2'],
        ['`not_maximal_SG_of_card`, `yip_conjecture_SG_false`', '¬ Maximal (IsClique) …;  ¬ YipConjectureSG', 'Mathlib SimpleGraph reading']]
table(corr, [1.85 * inch, 2.75 * inch, 1.9 * inch])
P('<b>Replay and audit.</b> The dossier’s portable driver takes the toolchain locations from LEAN_BIN and LEAN_PACKAGES. '
  'Before running anything it checks the pinned binary hashes and the source manifest, and it refuses to start if any '
  '`.olean` already exists. It then performs these steps:')
P('(i) a strict build: `lean -j1 -DwarningAsError=true`;', 'p')
P('(ii) a kernel re-check with `leanchecker`;', 'p')
P('(iii) a reviewer audit of all 40 constants stored in the module’s data, including auxiliary and generated ones. For each '
  'constant it prints the full type with `pp.all`, checks body presence via `value? true`, checks safe and non-partial '
  'status and the absence of new axioms, and requires transitive axioms within {propext, Classical.choice, Quot.sound};', 'p')
P('(iv) sanity re-statements of the endpoints;', 'p')
P('(v) negative controls: a wrong certificate (x − 1 in place of x − 0) is rejected by `linear_combination`, while its '
  'verbatim twin is accepted; the endpoint does not typecheck as the conjecture itself; `sorry` is rejected in strict mode; '
  'the axiom filter flags an added axiom; and a malformed `.olean` fails `leanchecker` with an invalid-header error. Each '
  'control asserts only what it tests.', 'p')
P('No `sorry`, `admit`, new axiom, `unsafe`, `native_decide` or `ofReduceBool` occurs. The only finite case analysis is an '
  '`interval_cases`/`decide` check on r ≤ 8, which is kernel-checked.')
table([['Certified in Lean', 'Ordinary proof only', 'Computation only (diagnostic)'],
       ['r = 1; 𝔽_{5} is a clique; f has a root in every K with |K| = 5^{8}; x − a and a − x nonzero cubes; 𝔽_{5} not maximal; '
        '¬YipConjecture and ¬YipConjectureSG',
        'irreducibility of f (§3.6); 25-clique and ω ≥ 25 (Prop. 3); 𝔽_{5} a maximal subfield clique (Prop. 4); failure of the '
        'remark-conjecture of [2]',
        '960 extension vertices, none in the subfield of order 625; θ primitive; author sweep up to 5·10^{6} (only failure)']],
      [2.2 * inch, 2.2 * inch, 2.1 * inch])

P('6. Trust, scope and novelty limits', 'h')
P('<b>Formal trust.</b> The Lean kernel, the Lean compiler and the prebuilt Mathlib dependency `.olean` files are trusted. '
  'The upstream dependencies were not rebuilt from source here, and `leanchecker` comes from the same installation, so the '
  'kernel check is not independent of the toolchain. Faithfulness of `YipConjecture` to the source statement is a matter of '
  'human reading. Section 2 records the interpretation used: r ≥ 1 and integral quotients. An independent technical review '
  'reached the same reading, and our own reading of [1, 2] agrees with it.')
P('<b>Resource note.</b> Each tool call ran on at most 2 CPUs, with CPU time ≤ 120 s, wall time ≤ 140 s, an address space '
  'of 64 GiB and MALLOC_ARENA_MAX=2. Where available, each call also ran inside a systemd scope with MemoryMax=6G. The 6 GiB '
  'sampled-RSS guard applies to private memory (anonymous plus shmem). Importing Mathlib maps about 6–7 GB of read-only '
  '`.olean` files, so total VmRSS, which counts those clean file-backed pages, exceeded 6 GiB. The receipts report both '
  'quantities.')
P('<b>Scope.</b> We refute the unrestricted conjecture and the remark-conjecture of [2]. We make no claim about which pairs '
  '(q, d) fail in general, about the exact clique number of GP(5^{8},3), or about a corrected sharp hypothesis. '
  '[2, Theorem 1.2] remains valid. The abstract of [2] says “confirms”, and [3, §1] restates [2] without the size '
  'hypothesis; both should be read with that hypothesis in mind.')
P('<b>Novelty.</b> We make no claim of worldwide priority. The search for prior art was bounded. It read the bodies of '
  '[1]–[5]. Among works citing [1], three listed by OpenAlex were not read, and neither was Yip’s doctoral thesis. Web and '
  'registry searches on 1 November 2026 found no report of this counterexample. The MathDB/Palomar comment and solution '
  'state could not be accessed (HTTP 403). MathDB lists the problem as open, but its references field attaches a quotation '
  'about the Peisert-graph analogue that is unrelated to this conjecture.')
P('<b>AI assistance.</b> The counterexample and the Lean module were produced in an earlier AI-assisted research lane of '
  'the same campaign. Separate AI-assisted lanes then reviewed its technical fidelity and its novelty and significance. '
  'This manuscript and its dossier were prepared with AI assistance (Claude Opus 5.5). No human has reviewed this draft.')

P('References', 'h')
refs = [
    '[1] C. H. Yip, On maximal cliques of Cayley graphs over fields, J. Algebraic Combin. 56(2) (2022) 323–333; '
    'arXiv:2101.09652 (v2 TeX source read). Conjecture 1.4; Theorem 1.3 (Broere–Döman–Ridley); lemma in §2.',
    '[2] C. H. Yip, Maximality of subfields as cliques in Cayley graphs over finite fields, Algebr. Comb. 6(4) (2023) '
    '901–905, doi:10.5802/alco.291; arXiv:2209.00864 (published TeX and arXiv v2 TeX read). Conjecture 1.1, Theorem 1.2 and '
    'the remark after its proof.',
    '[3] C. H. Yip, Exact values and improved bounds on the clique number of cyclotomic graphs, arXiv:2304.13213 (v5 TeX '
    'read; recorded by the independent source review as published in Des. Codes Cryptogr., 2025; journal version not read).',
    '[4] S. Asgarli and C. H. Yip, Van Lint–MacWilliams’ conjecture and maximum cliques in Cayley graphs over finite fields, '
    'J. Combin. Theory Ser. A 192 (2022) 105667; arXiv:2106.01522 (TeX read; restates the conjecture and proves the case n '
    'an odd prime, q &gt; n^{2}).',
    '[5] G. Martin and C. H. Yip, Distribution of power residues over shifted subfields and maximal cliques in generalized '
    'Paley graphs, arXiv:2403.04312 (TeX read; journal version not read).',
    '[6] MathDB problem 355956, “Yip’s maximal subfield clique conjecture for generalized Paley graphs”, '
    'https://mathdb.com/p/355956/ (raw record from the 2026-09-29 corpus snapshot, sha256 4d6b71c7…6d81d; live page not '
    'accessed).',
    '[7] The Lean 4 theorem prover, v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52; The Mathlib Community, '
    'Mathlib, commit d13f23b723b8a846827a245b89c10fc7d3f11612.',
]
for r in refs:
    P(r, 'ref')


def on_page(canv, doc):
    canv.saveState()
    canv.setFont('Serif-Italic', 7.8)
    canv.setFillColor(colors.HexColor('#7a1f1f'))
    canv.drawString(0.85 * inch, 0.5 * inch, 'DRAFT — AI-assisted — zero accepted credit — MathDB 355956')
    canv.setFillColor(colors.black)
    canv.drawRightString(letter[0] - 0.85 * inch, 0.5 * inch, 'page %d' % doc.page)
    canv.restoreState()


def build(out):
    doc = SimpleDocTemplate(str(out), pagesize=letter, leftMargin=0.85 * inch, rightMargin=0.85 * inch,
                            topMargin=0.8 * inch, bottomMargin=0.8 * inch,
                            title='The prime field is not a maximal clique in GP(5^8, 3): a Lean-certified counterexample to Yip’s maximal subfield clique conjecture',
                            author='AI-assisted draft (Claude Opus 5.5); no human authorship asserted',
                            subject='DRAFT manuscript for MathDB 355956; zero accepted credit; root review pending',
                            keywords='generalized Paley graph, maximal clique, subfield clique, counterexample, Lean 4, Mathlib, MathDB 355956, DRAFT',
                            creator='write_paper.py (ReportLab)', producer='ReportLab', initialFontName='Serif')
    doc.build(story, onFirstPage=on_page, onLaterPages=on_page)


if __name__ == '__main__':
    build(O / 'paper.pdf')
    fonts = {k: hashlib.sha256(pathlib.Path(v).read_bytes()).hexdigest() for k, v in FONTS.items()}
    (O / 'paper-build.json').write_text(json.dumps({'fonts': FONTS, 'font_sha256': fonts,
                                                    'pdf_sha256': hashlib.sha256((O / 'paper.pdf').read_bytes()).hexdigest()}, indent=2))
    print('wrote paper.pdf')
