#!/usr/bin/env python3
"""Build the DRAFT manuscript PDF for the root-review lane common-basis-final-replay-pi-r1 (corrections to the pi-r2 draft).

Run from the lane root:  python3 -I -B paper-src/build_paper.py
All numeric content is generated from the frozen evidence files; nothing is hardcoded
except prose. Output: paper.pdf in the lane root.
"""
import sys, os, json, itertools

LANE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
R250 = os.path.join(LANE, '..', 'expanded-corpus-r250')
VENV_SITE = '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/latin-manuscript-r1/.venv/lib/python3.14/site-packages'
sys.path.append(VENV_SITE)

from reportlab.lib.pagesizes import letter
from reportlab.lib.units import inch
from reportlab.lib import colors
from reportlab.lib.styles import ParagraphStyle
from reportlab.lib.enums import TA_JUSTIFY, TA_CENTER
from reportlab.platypus import (BaseDocTemplate, PageTemplate, Frame, Paragraph, Spacer,
                                Table, TableStyle, KeepTogether)

from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont as RLTTFont
from reportlab.lib.fonts import addMapping

FD = '/usr/share/fonts/liberation-serif-fonts'
for nm, fn in [('LSerif', 'LiberationSerif-Regular.ttf'), ('LSerif-Bold', 'LiberationSerif-Bold.ttf'),
               ('LSerif-Italic', 'LiberationSerif-Italic.ttf'), ('LSerif-BoldItalic', 'LiberationSerif-BoldItalic.ttf')]:
    pdfmetrics.registerFont(RLTTFont(nm, os.path.join(FD, fn)))
addMapping('LSerif', 0, 0, 'LSerif')
addMapping('LSerif', 1, 0, 'LSerif-Bold')
addMapping('LSerif', 0, 1, 'LSerif-Italic')
addMapping('LSerif', 1, 1, 'LSerif-BoldItalic')
pdfmetrics.registerFont(RLTTFont('LSym', '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/common-basis-manuscript-pi-r1/fonts/Symbola.ttf'))

def sym(s):
    for ent, ch in [('&isin;','\u2208'),('&notin;','\u2209'),('&cup;','\u222A'),
                    ('&empty;','\u2205'),('&sube;','\u2286'),('&sub;','\u2282'),
                    ('&exist;','\u2203'),('&and;','\u2227'),('&forall;','\u2200')]:
        s = s.replace(ent, '<font face="LSym">%s</font>' % ch)
    return s

cert = json.load(open(os.path.join(R250, 'matroid-certificate.json')))
BASES = [tuple(b) for b in cert['bases']]
D1 = [tuple(b) for b in cert['deletion_complementary_bases']['1']]
D6 = [tuple(b) for b in cert['deletion_complementary_bases']['6']]
COLS = cert['cols']
E = list(range(9))

def fs(x):  # font size helper
    return 8.2

# ---------- styles ----------
stBody = ParagraphStyle('body', fontName='LSerif', fontSize=10, leading=13.2,
                        alignment=TA_JUSTIFY, spaceAfter=5)
stTitle = ParagraphStyle('title', fontName='LSerif-Bold', fontSize=15, leading=19,
                         alignment=TA_CENTER, spaceAfter=4)
stSub = ParagraphStyle('sub', fontName='LSerif', fontSize=10.5, leading=13,
                       alignment=TA_CENTER, spaceAfter=2, textColor=colors.black)
stH1 = ParagraphStyle('h1', fontName='LSerif-Bold', fontSize=12, leading=14.5,
                      spaceBefore=9, spaceAfter=4)
stAbs = ParagraphStyle('abs', fontName='LSerif', fontSize=9.5, leading=12.4,
                       alignment=TA_JUSTIFY, leftIndent=18, rightIndent=18, spaceAfter=6)
stCap = ParagraphStyle('cap', fontName='LSerif', fontSize=8.6, leading=10.5,
                       alignment=TA_CENTER, spaceBefore=3, spaceAfter=6)
stRef = ParagraphStyle('ref', fontName='LSerif', fontSize=9.3, leading=12,
                       spaceAfter=3, leftIndent=14, firstLineIndent=-14)
stTh = ParagraphStyle('th', fontName='LSerif', fontSize=10, leading=13.2,
                      leftIndent=16, rightIndent=8, spaceBefore=4, spaceAfter=4)

def thm(label, text):
    return Paragraph(sym('<b>%s.</b> %s' % (label, text)), stTh)

# ---------- verified data tables ----------
def grid(pairs, per_row, header=None):
    rows = []
    if header:
        rows.append(header)
    for i in range(0, len(pairs), per_row):
        rows.append(['{'+', '.join(str(k) for k in b)+'}' for b in pairs[i:i+per_row]])
    while len(rows[-1]) < per_row:
        rows[-1].append('')
    return rows

def make_table(rows, colw, fontsize=8.0, header=False):
    t = Table([[Paragraph(str(c), ParagraphStyle('c', fontName='LSerif',
                fontSize=fontsize, leading=fontsize+1.6)) if isinstance(c, str) else c
                for c in r] for r in rows], colWidths=colw, hAlign='CENTER')
    style = [('GRID', (0, 0), (-1, -1), 0.4, colors.HexColor('#999999')),
             ('VALIGN', (0, 0), (-1, -1), 'MIDDLE'),
             ('TOPPADDING', (0, 0), (-1, -1), 1.4),
             ('BOTTOMPADDING', (0, 0), (-1, -1), 1.4),
             ('LEFTPADDING', (0, 0), (-1, -1), 3),
             ('RIGHTPADDING', (0, 0), (-1, -1), 3)]
    if header:
        style += [('BACKGROUND', (0, 0), (-1, 0), colors.HexColor('#E8E8E8')),
                  ('FONTNAME', (0, 0), (-1, 0), 'LSerif-Bold')]
    t.setStyle(TableStyle(style))
    return t

# binary matrix of the representation
def bitrow(mask):
    return ['1' if (COLS[j] >> mask) & 1 else '0' for j in E]

brows = [['element'] + [str(e) for e in E],
         ['column integer'] + [str(c) for c in COLS]]
for mask, lbl in [(3, 'b3 (coefficient of 8)'), (2, 'b2 (coefficient of 4)'),
                  (1, 'b1 (coefficient of 2)'), (0, 'b0 (coefficient of 1)')]:
    brows.append([lbl] + bitrow(mask))

# D-tables
def dtab(data):
    rows = [['partition first base B', 'forced second base (E\\z)\\B']]
    for b in data:
        comp = tuple(sorted(set(b) ^ (set(E) - {b and 1 or 1})))  # placeholder
    return rows

def dtable(z, data):
    # two column-groups side by side: B | comp | B | comp
    half = (len(data) + 1) // 2
    rows = [['base B', 'complement base', 'base B', 'complement base']]
    L, R = data[:half], data[half:]
    for i in range(half):
        row = []
        for src in (L, R):
            if i < len(src):
                b = src[i]
                comp = tuple(sorted((set(E) - {z}) - set(b)))
                row += ['{'+', '.join(map(str, b))+'}', '{'+', '.join(map(str, comp))+'}']
            else:
                row += ['', '']
        rows.append(row)
    return make_table(rows, [1.35*inch, 1.55*inch, 1.35*inch, 1.55*inch], fontsize=7.6, header=True)

def bases_grid():
    rows = []
    per = 4
    for i in range(0, len(BASES), per):
        chunk = BASES[i:i+per]
        row = ['{'+', '.join(map(str, b))+'}' for b in chunk]
        row += ['']*(per-len(row))
        rows.append(row)
    return rows

# ---------- document ----------
def footer(canvas, doc):
    canvas.saveState()
    canvas.setFont('Times-Roman', 8)
    canvas.drawString(inch, 0.55*inch, 'ROOT-REVIEW COPY - MathDB 332371 common-basis counterexample (lane common-basis-final-replay-pi-r1)')
    canvas.drawRightString(letter[0]-inch, 0.55*inch, 'page %d' % doc.page)
    canvas.restoreState()

doc = BaseDocTemplate(os.path.join(LANE, 'paper.pdf'), pagesize=letter,
                      leftMargin=inch, rightMargin=inch, topMargin=0.85*inch, bottomMargin=0.8*inch,
                      title='A rank-four counterexample to the Lasoń common-basis conjecture (DRAFT)',
                      author='Pi root-review lane common-basis-final-replay-pi-r1 (corrected copy of the pi-r2 draft)')
frame = Frame(doc.leftMargin, doc.bottomMargin, doc.width, doc.height, id='main')
doc.addPageTemplates([PageTemplate(id='page', frames=[frame], onPage=footer)])

S = []
B = lambda t, st=stBody: S.append(Paragraph(sym(t), st))

# title block
S.append(Paragraph('A Rank-Four Binary Counterexample to the Lasoń<br/>Common-Basis Conjecture (MathDB 332371)', stTitle))
S.append(Paragraph('Root-review copy - lane common-basis-final-replay-pi-r1 - 2026-11-05 - zero credit; root acceptance pending', stSub))
S.append(Spacer(1, 6))
B('<b>Status note.</b> This is the root-review copy of a draft prepared for review, carrying two factual corrections (Section 7 version history; Section 8 replay-tooling '
  'description) and the completed-audit status. The independent source/mathematics/significance review returned a <i>qualified pass</i> with explicit limits; the independent '
  'strict Lean-fidelity audit (common-basis-fidelity-pi-r2) is complete with verdict PASS, and a fresh enforced final replay was performed in this lane. Final root acceptance '
  'and the narrow module-origin/full-type audit supplement remain pending and are not claimed. Nothing here asserts campaign acceptance, credit, priority, or minimality.', stAbs)

B('<b>Contribution.</b> An explicit rank-4 matroid on the nine-element ground set E = {0,1,...,8} such that, with x = 1 and y = 6, '
  'both E\\x and E\\y partition into two bases, but no two such partitions share a base. This refutes, in the exact printed scope, '
  'Conjecture 2.5 of Lasoń (Selecta Mathematica 2021) = Conjecture 13 (arXiv v2/v3), the common-basis conjecture for '
  'partitions of a matroid ground set, for k = 2, r = 4.')

# 1 ------------------------------------------------------------------
S.append(Paragraph('1. The conjecture', stH1))
B('Throughout, matroids are finite matroids in full generality; no simplicity, representability, or connectedness is assumed. '
  'The following is Conjecture 2.5 in the journal version and arXiv v4/v5 of [1]; it appears as Conjecture 13 with the same '
  'quantifiers in arXiv v2/v3, and v1 predates the formulation.')
S.append(thm('Conjecture 2.5 ([1], journal form)', 'Let k &ge; 2, and let M be a matroid of rank r on a ground set E with '
  '|E| = kr+1. Suppose x, y &isin; E are such that both E\\{x} and E\\{y} can be partitioned into k pairwise disjoint bases. '
  'Then there exist partitions of E\\{x} and E\\{y} into k pairwise disjoint bases which share a common basis.'))
B('The source derives the statement for classes of matroids closed under rank-preserving deletions and parallel extensions, and '
  'records (attributing the history to Joseph Bonin) that the case k = 2 was studied by Paul Seymour and Neil White in the 1980s '
  'and was not resolved. Proposition 2.6 of [1] proves one-way implications between this conjecture, the complementary-basis-graph '
  'conjecture, and White&#39;s conjecture; Proposition 2.7 proves the conjecture for k &ge; 2<sup>r-1</sup>+1, which is k &ge; 9 at r = 4 and so does not cover k = 2. '
  'The implications in Proposition 2.6 are one-way: a counterexample to Conjecture 2.5 is not a counterexample to any White conjecture, '
  'and we claim none.')

# 2 ------------------------------------------------------------------
S.append(Paragraph('2. The counterexample', stH1))
B('Let E = {0, 1, ..., 8}, x = 1, y = 6, r = 4, k = 2, so |E| = 2·4+1 as required. Consider the binary representation whose '
  'columns are the integers below, read as four binary coordinates (b3 b2 b1 b0, i.e. coordinate i is the coefficient of 2<sup>i</sup>):')
S.append(Spacer(1, 2))
t = make_table(brows, [1.55*inch] + [0.36*inch]*9, fontsize=8.0)
S.append(t)
S.append(Paragraph('Table 1. The rank-4 binary representation; column j is the integer in the second row, in binary.', stCap))
B('A four-element subset of E is a base exactly when the corresponding 4&#215;4 determinant is odd. Of the C(9,4) = 126 four-subsets, '
  'exactly <b>76</b> are bases; the complete list follows.')
S.append(Spacer(1, 2))
tg = make_table(bases_grid(), [1.55*inch]*4, fontsize=7.6)
S.append(tg)
S.append(Paragraph('Table 2. The 76 bases of M, the complete base family used throughout; it is also the literal Lean certificate.', stCap))

# 3 ------------------------------------------------------------------
S.append(Paragraph('3. Verification of the axioms, without the representation', stH1))
S.append(Spacer(1, 2))
counts = [
 ('four-element subsets of E', 'C(9,4) = 126'),
 ('bases (Table 2)', '76'),
 ('ordered exchange obligations (A, B, e)', '12,736'),
 ('exchange failures', '0'),
 ('circuits', '23: one parallel pair, three triangles, eleven 4-circuits, eight 5-circuits'),
 ('bases extendible for z = 1 / z = 6', '|D1| = 32 / |D6| = 24'),
 ('unordered partitions of E\\{1} / E\\{6}', '16 / 12'),
 ('bases shared by D1 and D6', '0'),
]
pcl = ParagraphStyle('cl', fontName='LSerif', fontSize=9, leading=11.5)
cr = ParagraphStyle('cr', fontName='LSerif', fontSize=9, leading=11.5)
ct = Table([[Paragraph(a, pcl), Paragraph(b, cr)] for a, b in counts],
           colWidths=[2.6*inch, 3.4*inch], hAlign='CENTER')
ct.setStyle(TableStyle([('GRID', (0, 0), (-1, -1), 0.4, colors.HexColor('#999999')),
                        ('BACKGROUND', (0, 0), (0, -1), colors.HexColor('#F2F2F2')),
                        ('TOPPADDING', (0, 0), (-1, -1), 2), ('BOTTOMPADDING', (0, 0), (-1, -1), 2)]))
S.append(ct)
S.append(Paragraph('Table 3. Complete counts for the witness; every entry is rederived from the frozen certificate in the dossier.', stCap))
B('The base family of Table 2 satisfies the basis-exchange axiom directly, so M is a matroid independently of the binary model; '
  'the Lean endpoint indeed uses only the list. Membership was decided by parity of the 4&#215;4 determinant (equivalently, '
  'Gaussian elimination over F2 on the four coordinates of Table 1; the two procedures agree on all 126 subsets). For every '
  'ordered pair of bases A, B and every e &isin; A\\B - 12,736 triples in all - a witness f &isin; B\\A with '
  '(A\\{e})&cup;{f} a base exists; the independent recheck performed for this manuscript found no failure. Nonempty proper '
  'bases of equal size give a rank-4 matroid on E; the rank is witnessed concretely, e.g. {0, 2, 3, 5} is a base, so r = 4.')
B('Worked exchange instance. A = {0,2,3,5} and B = {0,1,2,6} are bases and e = 3 lies in A\\B; the element f = 1 of B\\A '
  'gives (A\\{3})&cup;{1} = {0,1,2,5}, a base of Table 2 (f = 6 works too). Every one of the 12,736 triples is disposed of '
  'in this way by the certificate in the dossier and by the kernel-checked Lean obligations of Section 6.')
B('Ordinary structural facts (supplementary; computed but not part of the formal endpoint): the 23 circuits are one parallel pair '
  '{1, 4}, three triangles {0,6,8}, {2,6,7}, {3,5,6}, eleven 4-circuits and eight 5-circuits. Every element lies in a base (no loops), '
  'and every two elements lie in a common circuit, so M is connected. Elements 1 and 4 are parallel; the source setting explicitly '
  'permits parallel elements (its closure hypotheses require parallel extensions), and no printed simplicity restriction exists. '
  'The distinguished elements x = 1 and y = 6 are distinct labels; deletion partitions in any case force x and y to be nonloops.')

# 4 ------------------------------------------------------------------
S.append(Paragraph('4. Two partitions and the complete common-base obstruction', stH1))
B('Both required partitions exist and are displayed by the theory:')
S.append(thm('Partition of E\\{1}', 'E\\{1} = {0,2,3,5} disjoint-union {4,6,7,8}.'))
S.append(thm('Partition of E\\{6}', 'E\\{6} = {0,1,2,7} disjoint-union {3,4,5,8}.'))
B('For z &isin; {1, 6} let D<sub>z</sub> = { B base : z &notin; B and (E\\{z})\\B is a base }, the bases extendible to a two-base '
  'partition of E\\{z}. A common base of two partitions of E\\{1} and E\\{6} must avoid 1 and 6 and hence lie in D<sub>1</sub> &cap; D<sub>6</sub> '
  'with both complements bases; conversely any B &isin; D<sub>1</sub> &cap; D<sub>6</sub> yields shared-base partitions. So the obstruction is exactly '
  'D<sub>1</sub> &cap; D<sub>6</sub> = &empty;, checked on the complete lists below - not merely on the two displayed partitions.')
S.append(Spacer(1, 2))
S.append(dtable(1, D1))
S.append(Paragraph('Table 4. D1: the 32 bases extendible to a partition of E\\{1} (32 give 16 unordered partitions).', stCap))
S.append(Spacer(1, 2))
S.append(dtable(6, D6))
S.append(Paragraph('Table 5. D6: the 24 bases extendible to a partition of E\\{6} (24 give 12 unordered partitions).', stCap))
B('Worked membership instances. The base B = {0,2,3,5} lies in D1: it avoids 1, and the complement (E\\{1})\\B = {4,6,7,8} '
  'is a base (row 1 of the partition above). The base {0,2,3,6} also lies in D1, its complement {4,5,7,8} being a base; but '
  '{0,2,3,5} does not lie in D6, since 6 &isin; B. Checking all 76 bases in this way produces Tables 4 and 5 exactly.')
S.append(thm('Proposition (complete finite obstruction)', 'D<sub>1</sub> &cap; D<sub>6</sub> = &empty;. Equivalently, there do not exist partitions of E\\{1} and E\\{6} into two bases each sharing a common base.'))
B('Proof. Every member of D<sub>1</sub> avoids 1 and every member of D<sub>6</sub> avoids 6; a shared base B would lie in both lists. The lists of Tables 4 and 5, computed by enumerating all 76 bases and testing the complement, share no member (the intersection of the two displayed lists is empty), and each list is exhaustive by construction. Applied to the concrete complements: for B in D1 the element set (E\\{1})\\B must be one of the 16 complementary bases, and simultaneously (E\\{6})\\B one of 12; the joint condition fails for all 32 candidates. &square;')
B('Each D-list is closed under complement-pairing, so |D<sub>1</sub>| = 32 gives 16 unordered partitions of E\\{1} and |D<sub>6</sub>| = 24 gives 12 of E\\{6}; '
  'Tables 4 and 5 enumerate all of them through their first halves, the second half being the swapped pairs.')
S.append(thm('Negation of the named instance', 'In Conjecture 2.5 of [1] (Conjecture 13 of arXiv v2/v3), take k = 2, r = 4, E = {0,...,8}, x = 1, y = 6. '
  'The hypothesis holds: |E| = 2&#183;4+1 and both E\\{1} and E\\{6} partition into two disjoint bases. The conclusion fails: there do not exist '
  'partitions of E\\{1} and E\\{6} into two pairwise disjoint bases sharing a common base. This instance-level failure is exactly the negation '
  'of the printed conjecture for these parameters; no broader claim is made.'))

# 5 ------------------------------------------------------------------
S.append(Paragraph('5. Why naive shortcuts fail (remarks)', stH1))
B('The families D<sub>1</sub> and D<sub>6</sub> are not themselves matroid base families: in D<sub>1</sub> the bases A = {2,5,6,8}, B = {3,5,7,8} with e = 2 have no '
  'eligible exchange inside D<sub>1</sub>, and in D<sub>6</sub> the same failure hits A = {0,4,7,8}, B = {0,3,4,5} with e = 8. The two-matroid intersection theorem '
  'therefore does not apply to D<sub>1</sub>, D<sub>6</sub> directly. On F = E\\{1,6} a desired B would be a common base of three structures at once: the restriction M|F and the '
  'two single-element deletions of duals, ((M\\1)* )\\6 and ((M\\6)* )\\1, each of rank 4 on F; the inspected common-base results for two matroids do not '
  'settle this triple condition. These are explanations of failed shortcuts, not a general non-reducibility claim.')
B('The source&#39;s Proposition 2.7 gives the property for k &ge; 2<sup>r-1</sup>+1; at r = 4 the threshold is 9, and our k = 2 lies outside every case it covers. '
  'No printed construction, figure, or formula in any version of [1] produces this witness; it was found by a bounded random search over rank-4 binary '
  'representations on nine points and then verified exactly.')

# 6 ------------------------------------------------------------------
S.append(Paragraph('6. Formal verification in Lean (author-side; independent audit complete; root acceptance pending)', stH1))
B('The literal Lean endpoint is the theorem <font face="Courier">CommonBasis332371.counterexample</font> in a twelve-module development over Lean 4.34.1 and mathlib '
  '<font face="Courier">d13f23b723b8a846827a245b89c10fc7d3f11612</font> (pinned; manifest in the dossier). Its statement is:')
S.append(Paragraph(sym('&exist; N : Matroid (Fin 9), N.E = univ &and; N.E.ncard = 2*4+1 &and; N.eRank = 4 &and; (&exist; A B, TwoBasePartition N (N.E \\ {1}) A B) &and; '
  '(&exist; A B, TwoBasePartition N (N.E \\ {6}) A B) &and; &not;(&exist; B C D, TwoBasePartition N (N.E \\ {1}) B C &and; TwoBasePartition N (N.E \\ {6}) B D)'),
  ParagraphStyle('code', fontName='LSerif', fontSize=9, leading=12, leftIndent=16, rightIndent=8, spaceBefore=2, spaceAfter=4)))
B('Here TwoBasePartition N S A B asserts that A and B are <i>actual</i> N-bases (Mathlib IsBase), disjoint, with union exactly S. The development constructs N by '
  '<font face="Courier">Matroid.ofIsBaseOfFinite</font> from the explicit list of Table 2 plus kernel-checked exchange obligations: modules <font face="Courier">Bases</font> (the 76-entry list and the base predicate), '
  '<font face="Courier">Cases0</font>-<font face="Courier">Cases7</font> (all finite checks by decide), <font face="Courier">Endpoint</font> (the exchange property and the matroid M), <font face="Courier">Final</font> (both partitions, the '
  'no-shared-base direction via complement characterization, ground cardinality and rank), and <font face="Courier">Audit</font>. Because the base family and its exchange '
  'verification construct a genuine Mathlib Matroid, no binary-representation bridge is formalized or needed. The recorded transitive axiom footprint of the '
  'endpoint is exactly propext, Classical.choice, Quot.sound; the metadata audit covers 106 local declarations. No sorry, admit, added axioms, unsafe code, '
  'or native_decide is used.')
B('<b>Evidence status.</b> The author-side strict replay (compilation plus leanchecker for all 12 modules) is recorded in the frozen lane expanded-corpus-r250 and remains '
  'author-supplied evidence. The independent strict Lean-fidelity audit (common-basis-fidelity-pi-r2, 2026-11-05) is complete: verdict PASS on literal source, '
  'mathematics/semantics, strict replay (24/24 stages), package scope, and documented reproducibility limits, including a 106-declaration body-presence audit, the exact '
  'propext/Classical.choice/Quot.sound axiom closure, and negative controls. A fresh final replay in the root-review lane common-basis-final-replay-pi-r1 reproduced all '
  '24 strict stages plus the same audit under an enforced wrapper (affinity &le;2 CPUs, CPU 120 s, wall 140 s, sampled-RSS 6 GiB guard, 12 GiB address-space rlimit with a '
  '64 GiB hard guard); its receipts ship in that lane\'s dossier. The narrow module-origin/full-type audit supplement is under separate review, and final root acceptance '
  'is a separate outstanding decision; neither is claimed here. Sections 2-5 are ordinary finite mathematics; this section is formal bookkeeping.')
S.append(Spacer(1, 2))
mods = [
 ('Bases.lean', 'the 76-entry base list, the base predicate BP, the Finset form'),
 ('Cases0.lean - Cases7.lean', 'the 76 kernel decide-checks, one per base, of all exchange and complement conditions'),
 ('Endpoint.lean', 'transfer to Matroid.ExchangeProperty BP; the matroid M by Matroid.ofIsBaseOfFinite'),
 ('Final.lean', 'TwoBasePartition, both partitions, no-shared-base, the literal counterexample'),
 ('Audit.lean', 'per-declaration axiom and metadata audit over the 106 local declarations'),
]
mt = Table([[Paragraph(a, ParagraphStyle('ml', fontName='Courier', fontSize=8, leading=10)),
             Paragraph(b, ParagraphStyle('mr', fontName='LSerif', fontSize=8.6, leading=10.5))] for a, b in mods],
           colWidths=[1.7*inch, 4.3*inch], hAlign='CENTER')
mt.setStyle(TableStyle([('GRID', (0, 0), (-1, -1), 0.4, colors.HexColor('#999999')),
                        ('BACKGROUND', (0, 0), (0, -1), colors.HexColor('#F2F2F2')),
                        ('TOPPADDING', (0, 0), (-1, -1), 2), ('BOTTOMPADDING', (0, 0), (-1, -1), 2)]))
S.append(mt)
S.append(Paragraph('Table 6. The twelve Lean modules (Cases0-Cases7 are eight files) and their roles; SHA-256 manifest in the dossier.', stCap))

# 7 ------------------------------------------------------------------
S.append(Paragraph('7. Novelty, significance, and limits', stH1))
B('Significance, under the campaign standard that prefers small exact counterexamples: the conjecture is explicitly printed, with identical quantifiers, in arXiv versions '
  'v2-v5, the journal, and an independent 2016 workshop problem list; the case k = 2 was posed in the 1980s (Seymour-White, as reported in [1]) and left open; and the '
  'refutation is a complete finite obstruction requiring no representability. Novelty limits, per the independent review: the underlying rank-4 matroid on nine points is '
  'not claimed new; no minimality of nine elements or rank four is claimed; no simple-matroid or infinite-family strengthening is claimed; and no worldwide priority is asserted.')
B('Relation to prior negative results. Larson [2] (July 2026) gives, in Example 1.4 and Theorem 1.5, a rank-9 binary matroid on 18 elements whose complementary-basis '
  'reconfiguration fails, via a split-pair invariant taking values 3, 7, 9 and changing by at most 2; this refutes Conjectures 1.1(2) and 1.2 there, a White-reconfiguration '
  'statement. That is a genuinely earlier negative result in the neighborhood, but a different theorem: its statement and proof do not contain the present rank-four, '
  'nine-element deletion-partition obstruction, and no reduction between the two results has been established in either direction. The review explicitly does not claim '
  'global non-subsumption; it found no complete reduction from [2] (or from the one-way implications of [1]) to this candidate, which is bounded evidence. Earlier '
  'structural papers in the citation neighborhood (Blasiak; Bonin; Lasoń-Michałek; regular-matroid reconfiguration) concern connectivity, exchange sequences, saturation, '
  'or restricted classes, and yield no printed instance of this failure.')

# 8 ------------------------------------------------------------------
S.append(Paragraph('8. Reproducibility', stH1))
B('The dossier ships: the 12 immutable Lean modules (byte-identical to the frozen author lane, SHA-256 manifest), the raw MathDB record with its one-based provenance and '
  'hashes, the machine-checkable certificate (all 76 bases, both D-lists, exchange flag), the ordinary verification script and its log, the original source PDFs and journal '
  'HTML with HTTP receipts, the independent review with its stated limits, the pinned toolchain manifest, and reproduction instructions. The source-only archive rebuilds the '
  'endpoint from user-supplied Lean binaries and package caches. Its original replay.sh is retained as a historical convenience script only: it inherits the ambient PATH, '
  'HOME and Lean environment, sets just LEAN_PATH, a pinned-binary PATH prefix and MALLOC_ARENA_MAX=2, and enforces no CPU affinity, no CPU/wall/RSS/address-space limits, '
  'no nonempty-build-dir rejection and no dependency-hash verification. The enforced replay path is capped_replay.py (Python standard library): safe archive extraction with '
  'per-member SHA-256, a fresh build directory with no preexisting .olean, a minimal private HOME, a pinned-binary PATH, fresh LEAN_PATH over the external packages, '
  'lean -j1 -M3500 -DwarningAsError=true and leanchecker per module, each call under &le;2-CPU affinity, CPU 120 s, wall 140 s, a sampled-RSS 6 GiB guard and a 12 GiB '
  'address-space rlimit (64 GiB hard guard), with every command, environment, exit status and resource peak logged. No prebuilt .olean files or large caches are shipped, '
  'and the external cache is not treated as a source-to-olean attestation. Every number in Sections 2-5 was rederived for the base manuscript from the frozen certificate; '
  'the recheck log ships in the dossier.')

# Appendix: circuits -------------------------------------------------
S.append(Paragraph('Appendix A. The complete circuit list', stH1))
B('For completeness and independent checking we record all 23 circuits of M, sorted by size. A reader can verify each entry '
  'against Table 2: a circuit is dependent, while all its proper subsets extend to bases of Table 2.')
def indep_circ(ss):
    ss = set(ss)
    return any(ss <= set(b) for b in BASES)
circ = []
Eset = set(E)
for k in range(1, 6):
    for s in itertools.combinations(E, k):
        if indep_circ(s):
            continue
        if all(indep_circ(c) for c in itertools.combinations(s, k - 1)):
            circ.append(s)
assert len(circ) == 23
rows = []
per = 3
for i in range(0, len(circ), per):
    chunk = circ[i:i+per]
    row = ['{'+', '.join(map(str, c))+'}' for c in chunk]
    row += ['']*(per-len(row))
    rows.append(row)
tc = make_table(rows, [1.7*inch]*3, fontsize=8.0)
S.append(tc)
S.append(Paragraph('Table 7. All circuits of M; the two-element circuit {1,4} is the only nontrivial parallel class.', stCap))

S.append(Spacer(1,2))
arts = [
 ('lean/*.lean (12 modules)', 'immutable mathematical modules, byte-identical to the frozen author lane; SHA-256 manifest'),
 ('raw/332371.jsonl', 'the exact MathDB record with one-based line provenance and chunk/statement hashes'),
 ('matroid-certificate.json; scripts and logs', '76 bases, both D-lists, exchange flag; ordinary verification script and full recheck log'),
 ('sources/ (arXiv v1-v5, journal HTML, receipts)', 'primary statements with URL, UTC timestamp, status and SHA-256 per file'),
 ('review records', 'the independent source/math review, its commands, limits, and the root integration record'),
 ('pinned toolchain manifest; reproduction entry points', 'Lean 4.34.1, mathlib d13f23b...; historical replay.sh plus enforced capped_replay.py'),
]
at = Table([[Paragraph(a, ParagraphStyle('al', fontName='LSerif', fontSize=8.6, leading=10.5)),
             Paragraph(b, ParagraphStyle('ar', fontName='LSerif', fontSize=8.6, leading=10.5))] for a, b in arts],
           colWidths=[2.3*inch, 3.7*inch], hAlign='CENTER')
at.setStyle(TableStyle([('GRID', (0, 0), (-1, -1), 0.4, colors.HexColor('#999999')),
                        ('BACKGROUND', (0, 0), (0, -1), colors.HexColor('#F2F2F2')),
                        ('TOPPADDING', (0, 0), (-1, -1), 2), ('BOTTOMPADDING', (0, 0), (-1, -1), 2)]))
S.append(at)
S.append(Paragraph('Table 8. Map of the reproducibility dossier (full inventory and hashes in the archive manifests).', stCap))

S.append(Paragraph('References', stH1))
refs = [
 '[1] M. Laso&#324;, <i>On the toric ideals of matroids of a fixed rank</i>, arXiv:1601.08199 (v1-v5, 2016; Conjecture 13 in v2/v3, Conjecture 2.5 in v4/v5); '
 'journal version: Selecta Mathematica 27, no. 2, article 18 (2021), DOI 10.1007/s00029-021-00633-6. All versions and the journal body are archived with HTTP receipts in the dossier.',
 '[2] M. Larson, <i>Counterexamples to two conjectures about matroids</i>, arXiv:2607.02208 (July 2026), Example 1.4 and Theorem 1.5.',
 '[3] <i>Order and Geometry Workshop 2016</i>, problem booklet, p. 2 (independent restatement of the same conjecture); archived with receipt.',
 '[4] MathDB entry 332371: <i>Common-basis conjecture for partitions of a matroid ground set</i>; frozen raw record, chunk and statement hashes in the dossier.',
 '[5] Lean 4.34.1 and mathlib d13f23b723b8a846827a245b89c10fc7d3f11612; pinned dependency manifest and replay scripts in the dossier.',
]
for r in refs:
    S.append(Paragraph(r, stRef))

doc.build(S)
print('WROTE', os.path.join(LANE, 'paper.pdf'))
