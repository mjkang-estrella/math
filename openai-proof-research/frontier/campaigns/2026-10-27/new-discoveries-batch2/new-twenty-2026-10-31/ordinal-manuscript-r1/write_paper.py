"""Build paper.pdf (DRAFT manuscript for MathDB 366371) with ReportLab.

Run:  python3 -I -B write_paper.py      (needs reportlab 4.x; fonts from the system paths below)
Mini-markup inside strings: ^{..} superscript, _{..} subscript, `code` monospace, <b>, <i>, <br/>.
Every other '<', '>' and '&' is escaped automatically.  Glyphs missing from Liberation Serif/Mono
fall back to Noto Sans Math; a glyph absent from both fonts aborts the build.
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
MATH_CMAP = TTFont('probe3', FONTS['NMath']).face.charToGlyph
TAGS = ['<b>', '</b>', '<i>', '</i>', '<br/>']


def fallback(s, cmap):
    out = []
    for c in s:
        if ord(c) > 127 and ord(c) not in cmap:
            assert ord(c) in MATH_CMAP, 'missing glyph %r' % c
            out.append('<font name="NMath">%s</font>' % c)
        else:
            out.append(c)
    return ''.join(out)


def esc(s):
    s = s.replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;')
    for t in TAGS:
        s = s.replace(t.replace('<', '&lt;').replace('>', '&gt;'), t)
    return s


def fmt(s):
    parts = s.split('`')
    out = []
    for i, part in enumerate(parts):
        if i % 2:
            code = part.replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;')
            out.append('<font name="Mono" size="7.9">%s</font>' % fallback(code, MONO_CMAP))
        else:
            part = esc(part).replace(', …, ', ',\u00a0…,\u00a0')
            while True:     # innermost braces first, so nested scripts become nested tags
                new = re.sub(r'\^\{([^{}]*)\}', r'<super rise="3.4" size="7">\1</super>', part)
                new = re.sub(r'_\{([^{}]*)\}', r'<sub rise="2.2" size="7">\1</sub>', new)
                if new == part:
                    break
                part = new
            out.append(fallback(part, SERIF_CMAP))
    return ''.join(out)


ST = {
    'title': ParagraphStyle('title', fontName='Serif-Bold', fontSize=15.5, leading=19, alignment=TA_CENTER, spaceAfter=4),
    'subtitle': ParagraphStyle('subtitle', fontName='Serif', fontSize=11.5, leading=14, alignment=TA_CENTER, spaceAfter=6),
    'status': ParagraphStyle('status', fontName='Serif-Italic', fontSize=9, leading=11.5, alignment=TA_CENTER,
                             textColor=colors.HexColor('#7a1f1f'), spaceAfter=8),
    'abs': ParagraphStyle('abs', fontName='Serif', fontSize=9.6, leading=13.6, alignment=TA_JUSTIFY,
                          leftIndent=0.35 * inch, rightIndent=0.35 * inch, spaceAfter=6),
    'h': ParagraphStyle('h', fontName='Serif-Bold', fontSize=11.6, leading=14, spaceBefore=8, spaceAfter=3),
    'p': ParagraphStyle('p', fontName='Serif', fontSize=10, leading=14.4, alignment=TA_JUSTIFY, spaceAfter=4.5),
    'item': ParagraphStyle('item', fontName='Serif', fontSize=10, leading=14.2, alignment=TA_JUSTIFY, leftIndent=0.3 * inch,
                           firstLineIndent=-0.22 * inch, spaceAfter=1.5),
    'disp': ParagraphStyle('disp', fontName='Serif', fontSize=10, leading=19, leftIndent=0.3 * inch, spaceAfter=5, spaceBefore=2),
    'stmt': ParagraphStyle('stmt', fontName='Serif-Italic', fontSize=10, leading=14, alignment=TA_JUSTIFY,
                           leftIndent=0.25 * inch, rightIndent=0.25 * inch, spaceAfter=5, spaceBefore=1),
    'cell': ParagraphStyle('cell', fontName='Serif', fontSize=8.4, leading=11.6),
    'cellc': ParagraphStyle('cellc', fontName='Serif', fontSize=8.6, leading=11.6, alignment=TA_CENTER),
    'cellb': ParagraphStyle('cellb', fontName='Serif-Bold', fontSize=8.4, leading=11.6),
    'ref': ParagraphStyle('ref', fontName='Serif', fontSize=8.9, leading=11.8, leftIndent=16, firstLineIndent=-16, spaceAfter=2.5),
    'code': ParagraphStyle('code', fontName='Mono', fontSize=7.8, leading=9.6, leftIndent=0.2 * inch, spaceAfter=5),
}

story = []
P = lambda s, st='p': story.append(Paragraph(fmt(s), ST[st]))


def items(lst):
    for s in lst:
        P(s, 'item')
    story.append(Spacer(1, 3))


def table(rows, widths, header=True, center=False, keep=True):
    cst = ST['cellc'] if center else ST['cell']
    data = [[Paragraph(fmt(c), ST['cellb'] if (header and i == 0) else cst) for c in r] for i, r in enumerate(rows)]
    t = Table(data, colWidths=widths, repeatRows=1 if header else 0, hAlign='CENTER')
    t.setStyle(TableStyle([
        ('GRID', (0, 0), (-1, -1), 0.4, colors.HexColor('#8a8a8a')),
        ('FONTNAME', (0, 0), (-1, -1), 'Serif'),
        ('BACKGROUND', (0, 0), (-1, 0), colors.HexColor('#ececec') if header else colors.white),
        ('VALIGN', (0, 0), (-1, -1), 'TOP'),
        ('TOPPADDING', (0, 0), (-1, -1), 2), ('BOTTOMPADDING', (0, 0), (-1, -1), 2.5),
        ('LEFTPADDING', (0, 0), (-1, -1), 3), ('RIGHTPADDING', (0, 0), (-1, -1), 3)]))
    story.append(KeepTogether([t, Spacer(1, 6)]) if keep else t)
    if not keep:
        story.append(Spacer(1, 6))


def code_block(lines):
    out = []
    for line in lines:
        e = line.replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;')
        e = fallback(e, MONO_CMAP)
        n = len(line) - len(line.lstrip(' '))
        out.append('&nbsp;' * n + e[n:] if e.startswith(' ' * n) else e)
    story.append(Paragraph('<br/>'.join(out), ST['code']))


TITLE = 'A six-point ordinal space with the majorization property that does not embed in the real line'
P(TITLE, 'title')
P('A Lean-certified counterexample to Conjecture 7.4 of Keller and Petrov (MathDB 366371)', 'subtitle')
P('DRAFT research manuscript, 1 November 2026. No human authorship or affiliation is asserted. Prepared with AI assistance '
  '(Claude Opus 5.5) within a user-directed research campaign, from an author lane, an independent review and a root '
  'adjudication. Zero accepted campaign credit; final review and acceptance are reserved to the campaign root.', 'status')
P('<b>Abstract.</b> Keller and Petrov introduced ordinal spaces, which record only whether one pair of points is closer '
  'than, as close as, or farther than another. They showed that an ordinal space embeddable in the real line has an '
  'enumeration with a <i>majorization property</i>, proved the converse for at most four points, and conjectured the '
  'converse in general (Conjecture 7.4 of [1]). We give a six-point ordinal space, defined by a strict ranking of its 15 '
  'pairs, whose identity enumeration has the majorization property for chains of every length, with repeated indices and '
  'arbitrary permutations, but which does not embed in the line. Majorization for all chain lengths is reduced, by counting '
  'pieces above each threshold, to a finite check over 63 × 63 pairs of strictly increasing lists. Non-embeddability '
  'follows from five comparisons whose sum is a strict inequality between two equal linear forms. The negation of the '
  'conjecture, with literal definitions, is proved in Lean 4 with Mathlib using only the standard axioms. The phenomenon is '
  'the analogue, for ordinal spaces on the line, of classical results in measurement theory; we make no priority claim '
  'beyond a bounded search.', 'abs')

P('1. Introduction', 'h')
P('Ordinal data analysis works with comparisons of dissimilarities rather than their values. Keller and Petrov [1] '
  'axiomatize this setting: an <i>ordinal space</i> is a set X with a map δ that, for every two pairs {x, y} and {z, w}, '
  'says which pair is closer. A natural question is when such a space is the ordinal shadow of points on the real line. '
  'For this, [1, Section 7] defines a combinatorial condition on an enumeration x_{1}, …, x_{n} of the points, the '
  'majorization property (Definition 2.3 below). Proposition 7.3 of [1] shows that every space embeddable in ℝ^{1} has such '
  'an enumeration, and Theorem 7.5 shows the converse when |X| = 4. The authors write: “We are not able to say whether the '
  'existence of an enumeration with majorization property is also sufficient for embeddability in ℝ^{1} if n > 5, but for '
  'n ≤ 4 we have sufficiency”, and state the converse as Conjecture 7.4. MathDB records this as problem 366371 [7].')
P('<b>Main result.</b> Conjecture 7.4 is false, already for six points (Theorem 3.1). The witness is a strict ranking of the '
  '15 pairs of {0, …, 5}. Two features make the proof short and fully checkable. First, the majorization property quantifies '
  'over chains of every length k, but for this space it reduces exactly to a finite statement about strictly increasing '
  'lists and thresholds (Section 4). Second, once the order of the points on a putative line is forced, five comparisons '
  'add up to the contradiction 0 < 0 (Section 5). Both parts, and the negation of the conjecture with the source '
  'definitions, are kernel-checked in Lean (Section 6).')
P('<b>Context.</b> Finite representation problems of this kind are classical in measurement theory, where '
  'representability is characterized by cancellation conditions, that is, by solvability of linear inequalities [2, 3], '
  'and where Kraft, Pratt and Seidenberg [4] gave a five-atom qualitative probability that satisfies de Finetti’s axioms but '
  'has no agreeing measure. The present result is of that type, and is expected in spirit. It is not, however, a '
  'consequence of those results (Section 7). It settles the case left open in [1] with a small explicit witness; its '
  'depth is modest.')

P('2. Definitions and the conjecture', 'h')
P('We follow [1] (arXiv v1, which we read; see Section 8). Write δ(x, y) < δ(z, w) for δ(x, y, z, w) = ‘<’, and '
  'similarly for = and >.')
P('<b>Definition 2.1</b> ([1, Definition 1.1]). Let X be a nonempty set and δ : X × X × X × X → {‘<’, ‘=’, ‘>’}. Then '
  '(X, δ) is an <i>ordinal space</i> if for all x, y, u, v, z, w ∈ X:', 'p')
items(['(i) δ(x, y, x, y) = ‘=’;',
       '(ii) δ(x, y, z, w) = δ(y, x, z, w) = δ(x, y, w, z);',
       '(iii) δ(x, y, z, w) = −δ(z, w, x, y), where −‘<’ = ‘>’, −‘>’ = ‘<’ and −‘=’ = ‘=’;',
       '(iv) δ(x, y, u, v) = δ(u, v, z, w) = ‘=’ implies δ(x, y, z, w) = ‘=’;',
       '(v) δ(x, y, u, v) = ‘<’ and δ(u, v, z, w) ∈ {‘<’, ‘=’} imply δ(x, y, z, w) = ‘<’;',
       '(vi) δ(x, y, u, v) ∈ {‘<’, ‘=’} and δ(u, v, z, w) = ‘<’ imply δ(x, y, z, w) = ‘<’;',
       '(vii) δ(x, x, z, w) = ‘<’ if z ≠ w, and δ(x, x, z, w) = ‘=’ if z = w.'])
P('<b>Definition 2.2</b> ([1, (7.1)–(7.3)]). (X, δ) <i>embeds in the line</i>, written X ↪ ℝ^{1}, if there is '
  'Φ : X → ℝ such that for all x, y, z, w ∈ X, δ(x, y) <, =, > δ(z, w) holds if and only if '
  '|Φ(x) − Φ(y)| <, =, > |Φ(z) − Φ(w)|, respectively.')
P('For n ∈ ℕ^{+} let ℐ_{n} be the set of tuples (i_{0}, i_{1}, …, i_{k}) ∈ {1, …, n}^{k+1} with k ∈ ℕ^{+} and '
  'i_{0} ≤ i_{1} ≤ ⋯ ≤ i_{k}; repeated indices are allowed. We call such a tuple a <i>chain</i> of length k.')
P('<b>Definition 2.3</b> ([1, Definition 7.1]). Let x_{1}, …, x_{n} be an enumeration of X, |X| = n, and let '
  '(i_{0}, …, i_{k}), (j_{0}, …, j_{k}) ∈ ℐ_{n} have the same length k. Write (i) ∼ (j), respectively (i) ≺ (j), if there '
  'is a permutation π of {1, …, k} such that')
P('(7.4)  δ(x_{i_{l−1}}, x_{i_{l}}) = δ(x_{j_{π(l)−1}}, x_{j_{π(l)}}) for all l ∈ {1, …, k}, respectively<br/>'
  'δ(x_{i_{l−1}}, x_{i_{l}}) ≤ δ(x_{j_{π(l)−1}}, x_{j_{π(l)}}) for all l ∈ {1, …, k}, but not (7.4).', 'disp')
P('The enumeration has the <i>majorization property</i> if for every k ∈ ℕ^{+} and all chains (i), (j) of length k, '
  '(i) ≺ (j) implies δ(x_{i_{0}}, x_{i_{k}}) < δ(x_{j_{0}}, x_{j_{k}}), and (i) ∼ (j) implies '
  'δ(x_{i_{0}}, x_{i_{k}}) = δ(x_{j_{0}}, x_{j_{k}}).')
P('<b>Conjecture 2.4</b> ([1, Conjecture 7.4]). <i>Let (X, δ) be an ordinal space with |X| = n ∈ ℕ^{+} and let there exist '
  'an enumeration x_{1}, x_{2}, …, x_{n} of the points of the space X satisfying the majorization property. Then '
  'X ↪ ℝ^{1}.</i>')
P('Theorem 7.5 of [1] proves that for |X| = 4, X ↪ ℝ^{1} if and only if some enumeration has the majorization property '
  '(and gives a third, explicit equivalent condition); together with the easy cases this gives sufficiency for n ≤ 4. '
  'The quoted sentence leaves n = 5 formally unaddressed; our witness has n = 6, in the open range under any reading.')
P('<b>Remark 2.5</b> (reading of “but not (7.4)”). We read it, as the Lean module does, as “not all k equalities hold for '
  'this same π”. The other possible reading, “not (i) ∼ (j)”, gives the same relation: δ restricted to pairs is a total '
  'preorder and may be replaced by integer ranks; if the pieces of (i) are termwise at most those of (j) under π and the '
  'two multisets of pieces coincide, the rank sums are equal, so every termwise inequality is an equality. The '
  'diagnostic of Section 6 also checks both readings literally for k ≤ 4.')

P('3. The witness', 'h')
P('Let X = {0, 1, 2, 3, 4, 5}. Let D be the symmetric function on X × X with D(x, x) = 0 and off-diagonal values given by '
  'Table 1; D ranks the 15 pairs from 1 (closest) to 15 (farthest). Define δ(x, y, z, w) to be the comparison of the '
  'natural numbers D(x, y) and D(z, w). We use the enumeration x_{i+1} = i, so from now on chains are nondecreasing tuples '
  'in {0, …, 5}.')
table([['pair', '23', '34', '12', '24', '01', '13', '14', '45', '35', '02', '25', '03', '04', '15', '05'],
       ['D'] + [str(v) for v in range(1, 16)]], [0.42 * inch] + [0.37 * inch] * 15, center=True)
P('Table 1. The witness: “ab” denotes the pair {a, b}. Equivalently, the rows of the Lean matrix `D` are '
  '(0, 5, 10, 12, 13, 15), (5, 0, 3, 6, 7, 14), (10, 3, 0, 1, 4, 11), (12, 6, 1, 0, 2, 9), (13, 7, 4, 2, 0, 8), '
  '(15, 14, 11, 9, 8, 0).', 'cell')
story.append(Spacer(1, 4))
P('<b>Theorem 3.1.</b> (X, δ) is an ordinal space with n = 6 points; the enumeration x_{i+1} = i has the majorization '
  'property; and X does not embed in ℝ^{1}. Hence Conjecture 2.4 is false.', 'stmt')
P('<i>Proof that (X, δ) is an ordinal space.</i> D is symmetric, D(x, x) = 0, and D(x, y) ≥ 1 for x ≠ y. Comparison of '
  'natural numbers is a total preorder, so (i)–(vi) are reflexivity, symmetry, antisymmetry and the transitivity laws of '
  '= and < on ℕ (with symmetry of D for (ii)), and (vii) holds since D(x, x) = 0 < D(z, w) exactly when z ≠ w. ∎')
P('As a consistency check with [1, Proposition 7.2(ii), (iii)], which any majorizing enumeration must satisfy: '
  'D(0, 1) < D(0, 2) < D(0, 3) < D(0, 4) < D(0, 5) = 15 > D(1, 5) > D(2, 5) > D(3, 5) > D(4, 5) '
  '(values 5, 10, 12, 13, 15, 14, 11, 9, 8), and {0, 5} is the unique farthest pair. The remaining two parts are proved in '
  'Sections 4 and 5.')

P('4. Majorization for chains of every length', 'h')
P('For a chain I = (i_{0} ≤ ⋯ ≤ i_{k}) its <i>pieces</i> are f_{I}(l) = D(i_{l−1}, i_{l}) for l = 1, …, k. A piece with '
  'i_{l−1} = i_{l} is <i>degenerate</i> and has value 0. For a threshold t let c_{I}(t) be the number of l with '
  'f_{I}(l) ≥ t. For a list A = (a_{0}, …, a_{r}) let adj_{t}(A) be the number of consecutive pairs (a_{s−1}, a_{s}) '
  'with D(a_{s−1}, a_{s}) ≥ t.')
P('<b>Lemma 4.1</b> (counting). Let I, J be chains of length k and π a permutation of {1, …, k} with '
  'f_{I}(l) ≤ f_{J}(π(l)) for all l. Then c_{I}(t) ≤ c_{J}(t) for every t. If moreover f_{I}(l_{0}) < f_{J}(π(l_{0})), '
  'then c_{I}(t_{0}) < c_{J}(t_{0}) for t_{0} = f_{J}(π(l_{0})). If f_{I}(l) = f_{J}(π(l)) for all l, then '
  'c_{I} = c_{J}.', 'p')
P('<i>Proof.</i> Let S_{I}(t) = {l : f_{I}(l) ≥ t}. If l ∈ S_{I}(t) then f_{J}(π(l)) ≥ f_{I}(l) ≥ t, so π maps S_{I}(t) '
  'injectively into S_{J}(t). For t = t_{0} the image misses π(l_{0}) ∈ S_{J}(t_{0}): by injectivity its only preimage is '
  'l_{0}, and f_{I}(l_{0}) < t_{0}. So the inclusion is proper. The last claim follows by applying the first to π and '
  'to π^{−1}. ∎')
P('<b>Lemma 4.2</b> (reduction). For a chain I let red(I) be the list obtained by deleting consecutive repeated entries. '
  'Then red(I) is a nonempty strictly increasing list in {0, …, 5}, that is, one of the 63 nonempty subsets of '
  '{0, …, 5} listed increasingly; it starts with i_{0} and ends with i_{k}; and c_{I}(t) = adj_{t}(red(I)) for every '
  't ≥ 1.', 'p')
P('<i>Proof.</i> Deleting an entry i_{l} equal to i_{l−1} removes the degenerate piece, whose value 0 is below t ≥ 1, and '
  'changes no other piece: the piece (i_{l}, i_{l+1}) becomes (i_{l−1}, i_{l+1}), the same pair. The first entry is never '
  'deleted, and the last surviving entry equals i_{k}. A nondecreasing list without consecutive repeats is strictly '
  'increasing. ∎')
P('<b>Lemma 4.3</b> (finite check). For all nonempty strictly increasing lists A = (a_{0} < ⋯ < a_{r}) and '
  'B = (b_{0} < ⋯ < b_{s}) in {0, …, 5}:', 'p')
items(['(a) if adj_{t}(A) ≤ adj_{t}(B) for all t ∈ {1, …, 15}, with strict inequality for some such t, then '
       'D(a_{0}, a_{r}) < D(b_{0}, b_{s});',
       '(b) if adj_{t}(A) = adj_{t}(B) for all t ∈ {1, …, 15}, then D(a_{0}, a_{r}) = D(b_{0}, b_{s}).'])
P('<i>Proof.</i> This is a finite statement about 63 × 63 = 3969 pairs and 15 thresholds, verified exhaustively. In Lean '
  'it is the theorem `finite_check`, evaluated by the kernel (`decide +kernel`), and it is recomputed independently by the '
  'standard-library script `diagnostic.py`. ∎')
P('<b>Proposition 4.4.</b> The enumeration x_{i+1} = i has the majorization property.', 'p')
P('<i>Proof.</i> Let I, J be chains of length k ≥ 1, and put A = red(I), B = red(J). Suppose I ≺ J via π. Then '
  'f_{I}(l) ≤ f_{J}(π(l)) for all l, and the inequality is strict for some l_{0}, since not all of them are equalities. '
  'By Lemma 4.1, c_{I} ≤ c_{J} everywhere and c_{I}(t_{0}) < c_{J}(t_{0}) with t_{0} = f_{J}(π(l_{0})). As '
  't_{0} > f_{I}(l_{0}) ≥ 0 and all values of D are at most 15, t_{0} ∈ {1, …, 15}. By Lemma 4.2 the same relations '
  'hold between adj_{t}(A) and adj_{t}(B) for t ∈ {1, …, 15}, and A, B have the endpoints of I, J. Lemma 4.3(a) gives '
  'D(i_{0}, i_{k}) < D(j_{0}, j_{k}), i.e. δ(x_{i_{0}}, x_{i_{k}}) < δ(x_{j_{0}}, x_{j_{k}}). If I ∼ J, Lemma 4.1 '
  'gives c_{I} = c_{J}, hence adj_{t}(A) = adj_{t}(B) for t ∈ {1, …, 15}, and Lemma 4.3(b) gives equality of the endpoint '
  'values. ∎')
P('For example, (2, 3, 5) ≺ (0, 2, 3): the pieces are (1, 9) and (10, 1), and only the transposition matches them '
  'termwise; accordingly D(2, 5) = 11 < 12 = D(0, 3). Literal checks of Definition 2.3, with repeated indices and all '
  'permutations, for k ≤ 4 (82,957 pairs of chains, no violation) were made by the author lane, by the independent review '
  'and by `diagnostic.py`. They corroborate Proposition 4.4 but are not used in its proof.')

P('5. Non-embeddability', 'h')
P('<b>Proposition 5.1.</b> There is no Φ : X → ℝ such that δ(x, y) < δ(z, w) implies |Φ(x) − Φ(y)| < '
  '|Φ(z) − Φ(w)| for all x, y, z, w. In particular X does not embed in ℝ^{1}.', 'p')
P('<i>Proof.</i> Suppose Φ exists. Since D(0, 0) = 0 < D(0, 5), we have Φ(0) ≠ Φ(5); replacing Φ by −Φ, which '
  'preserves all distances, assume Φ(0) < Φ(5). For x ∈ {1, 2, 3, 4} the table gives D(0, x) < D(0, 5) and '
  'D(x, 5) < D(0, 5); hence Φ(x) − Φ(0) < Φ(5) − Φ(0) and Φ(5) − Φ(x) < Φ(5) − Φ(0), so Φ(0) < Φ(x) < Φ(5). '
  'Then |Φ(x) − Φ(0)| = Φ(x) − Φ(0), and D(0, 1) < D(0, 2) < D(0, 3) < D(0, 4) forces '
  'Φ(0) < Φ(1) < Φ(2) < Φ(3) < Φ(4) < Φ(5). Put g_{i} = Φ(i) − Φ(i − 1) > 0 for i = 1, …, 5, so that '
  '|Φ(a) − Φ(b)| = g_{a+1} + ⋯ + g_{b} for a < b. The five comparisons in Table 2 hold in Table 1. Adding the five '
  'resulting inequalities gives g_{1} + 2g_{2} + 2g_{3} + 2g_{4} + g_{5} < g_{1} + 2g_{2} + 2g_{3} + 2g_{4} + g_{5}, '
  'a contradiction. ∎')
table([['comparison', 'values', 'consequence'],
       ['D(2, 3) < D(3, 4)', '1 < 2', 'g_{3} < g_{4}'],
       ['D(1, 2) < D(2, 4)', '3 < 4', 'g_{2} < g_{3} + g_{4}'],
       ['D(0, 1) < D(1, 3)', '5 < 6', 'g_{1} < g_{2} + g_{3}'],
       ['D(1, 4) < D(4, 5)', '7 < 8', 'g_{2} + g_{3} + g_{4} < g_{5}'],
       ['D(3, 5) < D(0, 2)', '9 < 10', 'g_{4} + g_{5} < g_{1} + g_{2}'],
       ['sum', '', 'both sides: g_{1} + 2g_{2} + 2g_{3} + 2g_{4} + g_{5}']],
      [1.5 * inch, 0.8 * inch, 2.7 * inch])
P('Table 2. The five-comparison certificate. The gap-coefficient vectors of the two sides both sum to (1, 2, 2, 2, 1).', 'cell')
story.append(Spacer(1, 4))
P('<b>Remark 5.2.</b> Once the order of the points is forced, and since D has no ties, embeddability is the feasibility '
  'of a homogeneous system of strict linear inequalities in g ∈ ℝ^{5} with g > 0. By Gordan’s theorem of the '
  'alternative [8], infeasibility is always witnessed by a nonnegative combination of the inequalities that sums to zero; '
  'Table 2 is such a witness with five unit coefficients. Since the majorization property holds, this cancellation is '
  'not one of the majorization conditions: those compare the total intervals of two chains whose pieces can be matched '
  'termwise, while the five intervals on each side of Table 2 do not arise in that way.')

P('6. Formal verification', 'h')
P('The Lean module `OrdinalLine.lean` (20,774 bytes, sha256 `da892a4d…cec7703f`) is copied byte for byte from the author '
  'lane; it imports only Mathlib and is checked with Lean 4.34.1 (commit `5045d005`) and Mathlib `d13f23b7` [9]. Its '
  'statement of the conjecture and the two endpoints are:')
code_block(['def MajorizationConjecture : Prop :=',
            '  ∀ (X : Type) (δ : X → X → X → X → Ordering) (n : ℕ) (e : Fin n → X),',
            '    0 < n → IsOrdinalSpace δ → Function.Bijective e → HasMajorization δ e →',
            '    EmbeddableInLine δ',
            'theorem witness : IsOrdinalSpace δW ∧ Function.Bijective (id : Fin 6 → Fin 6) ∧',
            '    HasMajorization δW (id : Fin 6 → Fin 6) ∧ ¬ EmbeddableInLine δW',
            'theorem not_majorizationConjecture : ¬ MajorizationConjecture'])
table([['source', 'Lean (namespace OrdinalSpaces366371)', 'remarks'],
       ['Definition 2.1', '`IsOrdinalSpace δ`', 'fields `ax_i`–`ax_vii`; δ : X → X → X → X → Ordering; (iii) via `Ordering.swap`; “∈ {‘<’, ‘=’}” as `≠ .gt`'],
       ['Definition 2.2', '`EmbeddableInLine δ`', '∃ Φ : X → ℝ with the three equivalences for |Φ x − Φ y|'],
       ['ℐ_{n}, ≺, ∼', '`Prec δ e I J`, `Sim δ e I J`', 'I, J : Fin (k+1) → Fin n; one π : Equiv.Perm (Fin k); piece l is (I l.castSucc, I l.succ)'],
       ['majorization property', '`HasMajorization δ e`', 'for all k > 0 and all monotone I, J (repeats allowed)'],
       ['Conjecture 2.4', '`MajorizationConjecture`', '|X| = n encoded by a bijection e : Fin n → X; x_{i+1} = e i'],
       ['Table 1', '`D`, `δW`', 'δW x y z w = compare (D x y) (D z w)'],
       ['Section 3', '`isOrdinalSpace_W`', 'uses `D_symm`, `D_zero_iff` (kernel `decide`)'],
       ['Lemma 4.1', '`count_le`, `count_lt`, `card_eq_sum`', ''],
       ['Lemma 4.2', '`adj`, `dd`, `lastD`, `red`, `adj_dd`, `lastD_dd`, `pairwise_dd`, `red_mem_sublists`, `sum_pieces_eq_adj`, `adj_red`',
        'recursion via `List.rec`, so no compiler auxiliaries'],
       ['Lemma 4.3', '`okB`, `finite_check`, `okB_spec`', '`decide +kernel` over 64 × 64 sublists, t = 1, …, 15'],
       ['Proposition 4.4', '`majorization_W`', ''],
       ['Proposition 5.1', '`core`, `not_embeddable_W`', '`core` assumes Φ 0 < Φ 5; reflection in `not_embeddable_W`'],
       ['Theorem 3.1', '`witness`, `not_majorizationConjecture`', 'endpoints']],
      [1.05 * inch, 2.35 * inch, 3.3 * inch], keep=False)
P('Table 3. Correspondence between the paper and the Lean module. The conjecture is quantified over `X : Type`; its '
  'negation there already refutes the source statement, since the witness lives on `Fin 6`.', 'cell')
story.append(Spacer(1, 4))
P('<b>Replay.</b> A source-only archive was extracted with a path-checking extractor into a new directory, and a portable '
  'driver (paths given by `LEAN_BIN` and `LEAN_PACKAGES`; it refuses pre-existing oleans) ran every step with at most 2 CPUs, '
  '120 s CPU, 140 s wall, a 6 GiB private-memory guard and a systemd scope with MemoryMax=6G. The strict build '
  '`lean -j1 -DwarningAsError=true` produced an empty log, and its olean is byte-identical to the ones reported by the '
  'author lane and the independent review. `leanchecker` re-checked the module. A reviewer audit enumerated all 95 '
  'constants stored in the module (23 definitions, 69 theorems including generated auxiliaries, and the structure with its '
  'constructor and recursor), printed their full types, required a body for every definition and theorem, rejected '
  'axioms, opaque, unsafe, partial, implemented_by and extern constants and any `sorry`, and found the transitive axioms '
  'of every constant within {propext, Classical.choice, Quot.sound}. No `native_decide` or `ofReduceBool` is used.')
P('<b>Negative controls.</b> Each asserts only what it tests: dropping the fifth comparison of Table 2 makes `linarith` '
  'fail; exchanging the values of the pairs {0, 3} and {0, 4} makes the kernel evaluate the finite check of Lemma 4.3 to '
  '`false` (a non-majorizing table is rejected); the endpoint does not inhabit the conjecture; `sorry` and an added axiom '
  'are rejected; a malformed olean is rejected by `leanchecker`. Two positive twins re-check the verbatim extracted '
  'fragments, validating the harness.')
P('<b>Certified content versus diagnostics.</b> Theorem 3.1, Lemmas 4.1–4.3 and Propositions 4.4 and 5.1 are '
  'Lean-certified (Proposition 5.1 in the form ¬ EmbeddableInLine δW; Lemmas 4.1–4.2 in the forms listed in Table 3). '
  'Remarks 2.5 and 5.2 are ordinary mathematics and are not formalized. The following are diagnostics only, used by no proof: the literal checks for k ≤ 4 mentioned above; and the author lane’s '
  'floating-point linear-programming scans, which report that every majorizing weak order on five points found by its '
  'pruned search (477, of which 114 tie-free) is embeddable, and that among the 2612 majorizing tie-free orders on six '
  'points it found, 4 are non-embeddable, including Table 1. These scans were not independently reproduced. We make no '
  'minimality claim; in particular we do not claim that Conjecture 2.4 holds for n = 5.')

P('7. Relation to measurement theory and to citing work', 'h')
P('Representing a finite comparison structure by numbers is a linear feasibility problem, so by the theorem of the '
  'alternative non-representability always has a cancellation certificate. Scott [2] and Krantz, Luce, Suppes and '
  'Tversky [3] develop this viewpoint: finite representability is characterized by cancellation conditions of all '
  'orders, and conditions of bounded order do not suffice in general. The classical instance closest in spirit to ours '
  'is the counterexample of Kraft, Pratt and Seidenberg [4] to de Finetti’s axioms for qualitative probability.')
P('Those results do not decide Conjecture 2.4. The majorization property is a family of conditions of <i>unbounded</i> '
  'order (every chain length k) but of a <i>restricted shape</i>: each side is a chain along the enumeration, the chain '
  'pieces are matched termwise by a permutation, and only the two total intervals are compared. A general statement that '
  'bounded-order conditions are insufficient says nothing about this particular unbounded family, so an explicit example '
  'was needed. Theorem 3.1 shows that the family misses a cancellation of order five.')
P('Two works citing [1] were checked: Pech and Pech, <i>Echeloned spaces</i> [5], read by the independent review '
  '(metrizability, Fraïssé limits and Ramsey properties; nothing on embeddings in the line or on majorization), and '
  'Stumme, Dürrschnabel and Hanika, <i>Towards ordinal data science</i> [6], identified by the review as a position paper; '
  'we did not read its body.')

P('8. Limitations and status', 'h')
items(['• Source. We read arXiv:2412.17391v1 (submitted 23 December 2024). The journal version [1] was published in 2019/2020; '
       'its text was not read (institutional access only), and its Conjecture 7.4 is assumed to coincide with arXiv v1. '
       'MathDB cites the arXiv version.',
       '• Prior art. Searches were bounded: one web search and one arXiv author search by the author lane, and five web '
       'searches by the independent review (one specific to this conjecture), all on 1 November 2026, found no refutation. '
       'The classical unidimensional-scaling and absolute-difference literature was not searched body by body. '
       '<b>We make no priority claim.</b>',
       '• Significance. The witness was found by computer search and the certificate is short; the result settles the '
       'case left open in [1] but is modest in depth and expected in spirit.',
       '• Trust. The Lean kernel, compiler and prebuilt Mathlib oleans are trusted (no upstream rebuild); statement fidelity '
       'rests on human reading of the source. This is a DRAFT with zero accepted credit; acceptance is reserved to the '
       'campaign root.'])

P('References', 'h')
refs = [
    '[1] K. Keller and E. Petrov, Ordinal spaces, Acta Math. Hungar. 160 (2020), no. 1, 119–152, '
    'doi:10.1007/s10474-019-00972-z (online 5 September 2019; text not read); arXiv:2412.17391v1 (2024; read).',
    '[2] D. Scott, Measurement structures and linear inequalities, J. Math. Psych. 1 (1964), 233–247.',
    '[3] D. H. Krantz, R. D. Luce, P. Suppes and A. Tversky, Foundations of Measurement, Vol. I: Additive and Polynomial '
    'Representations, Academic Press, New York, 1971.',
    '[4] C. H. Kraft, J. W. Pratt and A. Seidenberg, Intuitive probability on finite sets, Ann. Math. Statist. 30 (1959), 408–419.',
    '[5] C. Pech and M. Pech, Echeloned spaces, Forum Math. Sigma (2025), doi:10.1017/fms.2025.47; arXiv:2312.11141.',
    '[6] G. Stumme, D. Dürrschnabel and T. Hanika, Towards ordinal data science, Trans. Graph Data Knowl. 1 (2023), no. 1, '
    'article 6, doi:10.4230/TGDK.1.1.6; arXiv:2307.09477.',
    '[7] MathDB problem 366371, “The majorization characterization conjecture for ordinal spaces embeddable in the line”, '
    'https://mathdb.com/p/366371/ (raw record from the 2026-09-29 corpus snapshot, sha256 585e249c…82e7d8; live page not '
    'accessed).',
    '[8] A. Schrijver, Theory of Linear and Integer Programming, Wiley, Chichester, 1986 (Gordan’s theorem of the alternative).',
    '[9] The Lean 4 theorem prover, v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52; The Mathlib Community, '
    'Mathlib, commit d13f23b723b8a846827a245b89c10fc7d3f11612.',
]
for r in refs:
    P(r, 'ref')


def on_page(canv, doc):
    canv.saveState()
    canv.setFont('Serif-Italic', 7.8)
    canv.setFillColor(colors.HexColor('#7a1f1f'))
    canv.drawString(0.85 * inch, 0.5 * inch, 'DRAFT — AI-assisted — zero accepted credit — MathDB 366371')
    canv.setFillColor(colors.black)
    canv.drawRightString(letter[0] - 0.85 * inch, 0.5 * inch, 'page %d' % doc.page)
    canv.restoreState()


def build(out):
    doc = SimpleDocTemplate(str(out), pagesize=letter, leftMargin=0.85 * inch, rightMargin=0.85 * inch,
                            topMargin=0.8 * inch, bottomMargin=0.8 * inch, title=TITLE,
                            author='AI-assisted draft (Claude Opus 5.5); no human authorship asserted',
                            subject='DRAFT manuscript for MathDB 366371; zero accepted credit; root review pending',
                            keywords='ordinal space, majorization property, line embedding, counterexample, Lean 4, Mathlib, MathDB 366371, DRAFT',
                            creator='write_paper.py (ReportLab)', producer='ReportLab', initialFontName='Serif',
                            invariant=1)
    doc.build(story, onFirstPage=on_page, onLaterPages=on_page)


if __name__ == '__main__':
    build(O / 'paper.pdf')
    fonts = {k: hashlib.sha256(pathlib.Path(v).read_bytes()).hexdigest() for k, v in FONTS.items()}
    (O / 'paper-build.json').write_text(json.dumps({'engine': 'ReportLab', 'invariant': 'ReportLab invariant mode: fixed timestamps (1999-12-31) and IDs, so rebuilding gives identical bytes',
                                                    'fonts': FONTS, 'font_sha256': fonts,
                                                    'pdf_sha256': hashlib.sha256((O / 'paper.pdf').read_bytes()).hexdigest()}, indent=2))
    print('wrote paper.pdf')
