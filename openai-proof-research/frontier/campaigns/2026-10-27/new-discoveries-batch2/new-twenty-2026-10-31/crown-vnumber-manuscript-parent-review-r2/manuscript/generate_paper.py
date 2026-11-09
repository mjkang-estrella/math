#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# Manuscript generator: "Local v-numbers of binomial edge ideals of crown graphs"
# Ordinary-proof research DRAFT for MathDB 369163.
# ReportLab; A4; LiberationSerif family; Symbola fallback for math glyphs.
#
# Content mini-markup:  *x*   -> italic toggle (balanced in each string)
#                       _{..} ^{..} -> sub/superscript, nestable one level
# Non-ASCII glyphs absent from LiberationSerif are wrapped in Symbola.
import os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
LANE = os.path.dirname(HERE)
OUT  = os.path.join(LANE, 'output', 'pdf', 'paper.pdf')

from reportlab.lib.pagesizes import A4
from reportlab.lib.units import mm as MM
from reportlab.lib.styles import ParagraphStyle
from reportlab.lib.enums import TA_JUSTIFY, TA_CENTER, TA_LEFT, TA_RIGHT
from reportlab.lib import colors
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont, TTFontFile
from reportlab.platypus import (BaseDocTemplate, PageTemplate, Frame, Paragraph,
                                Spacer, Table, TableStyle)

LIB = '/usr/share/fonts/liberation-serif-fonts'
pdfmetrics.registerFont(TTFont('Serif',    os.path.join(LIB, 'LiberationSerif-Regular.ttf')))
pdfmetrics.registerFont(TTFont('Serif-B',  os.path.join(LIB, 'LiberationSerif-Bold.ttf')))
pdfmetrics.registerFont(TTFont('Serif-I',  os.path.join(LIB, 'LiberationSerif-Italic.ttf')))
pdfmetrics.registerFont(TTFont('Serif-BI', os.path.join(LIB, 'LiberationSerif-BoldItalic.ttf')))
pdfmetrics.registerFont(TTFont('Sym',      '/usr/share/fonts/gdouros-symbola/Symbola.ttf'))

_tt = TTFontFile(os.path.join(LIB, 'LiberationSerif-Regular.ttf'))
LIBCHARS = set(_tt.charToGlyph.keys())

def _symwrap(ch):
    return ch if ord(ch) <= 126 or ch in LIBCHARS else '<font name="Sym">%s</font>' % ch

SUBF = 0.72  # size factor per sub/superscript level

def mm(s, depth=0, rise=0.0):
    out, i, n, ital = [], 0, len(s), False
    while i < n:
        c = s[i]
        if c == '*':
            out.append('</i>' if ital else '<i>')
            ital = not ital; i += 1
        elif c in '_^' and i + 1 < n and s[i + 1] == '{':
            j, level = i + 2, 1
            while j < n and level:
                if s[j] == '{': level += 1
                elif s[j] == '}': level -= 1
                j += 1
            if level: raise ValueError('unbalanced braces: ' + s)
            inner = s[i + 2:j - 1]
            # empirically calibrated on reportlab 4.4.9: a percentage rise r
            # yields a baseline shift of -r% of the context font size for sub
            # (and +... for sup); 72% size keeps subscripts readable.
            if c == '_':
                nr, tag = 20, 'sub'   # drop 0.20 em
            else:
                nr, tag = 38, 'sup'   # raise 0.38 em
            out.append('<%s size="72%%" rise="%d%%">' % (tag, nr))
            out.append(mm(inner, depth + 1, nr))
            out.append('</%s>' % tag)
            i = j
        else:
            out.append(_symwrap(c)); i += 1
    if ital: raise ValueError('unbalanced *: ' + s)
    return ''.join(out)

# ------------------------------- styles ----------------------------------------
def st(name, **kw):
    base = dict(fontName='Serif', fontSize=10.5, leading=14.6,
                alignment=TA_JUSTIFY, spaceAfter=5, spaceBefore=0)
    base.update(kw)
    return ParagraphStyle(name, **base)

S = dict(
    title    = st('title', fontName='Serif-B', fontSize=16.5, leading=21, alignment=TA_CENTER, spaceAfter=6),
    subtitle = st('subtitle', fontSize=11.5, leading=15, alignment=TA_CENTER, spaceAfter=2),
    dateline = st('dateline', fontSize=10, alignment=TA_CENTER, spaceAfter=10,
                  textColor=colors.Color(0.25, 0.25, 0.25)),
    h1       = st('h1', fontName='Serif-B', fontSize=12.5, leading=16, alignment=TA_LEFT,
                  spaceBefore=13, spaceAfter=5),
    body     = st('body'),
    thm      = st('thm', spaceBefore=7, spaceAfter=5),
    proof    = st('proof', spaceBefore=1, spaceAfter=7),
    eq       = st('eq', alignment=TA_CENTER, spaceBefore=7, spaceAfter=7),
    eqnum    = st('eqnum', alignment=TA_RIGHT, spaceAfter=0),
    abstract = st('abstract', fontSize=10, leftIndent=16, rightIndent=16, leading=13.8),
    bib      = st('bib', fontSize=9.5, leading=12.4, leftIndent=20, firstLineIndent=-20,
                  spaceAfter=2.6),
    box      = st('box', fontSize=9.3, leading=12.8),
)

def on_page(canv, doc):
    canv.saveState()
    w, h = A4
    if doc.page > 1:
        canv.setFont('Serif-I', 8.5)
        canv.setFillColor(colors.Color(0.35, 0.35, 0.35))
        canv.drawString(22 * MM, h - 12.6 * MM,
                        'Local v-numbers of binomial edge ideals of crown graphs')
        canv.drawRightString(w - 22 * MM, h - 12.6 * MM, 'DRAFT - ordinary proof')
        canv.setStrokeColor(colors.Color(0.65, 0.65, 0.65))
        canv.setLineWidth(0.4)
        canv.line(22 * MM, h - 14 * MM, w - 22 * MM, h - 14 * MM)
    canv.setFont('Serif', 9)
    canv.setFillColor(colors.Color(0.25, 0.25, 0.25))
    canv.drawCentredString(w / 2.0, 10.5 * MM, str(doc.page))
    canv.restoreState()

# ------------------------- story-building helpers ------------------------------
story = []

class Num:
    def __init__(self):
        self.section = 0
        self.counts = dict()
    def next(self, kind):
        self.counts[kind] = self.counts.get(kind, 0) + 1
        return '%d.%d' % (self.section, self.counts[kind])

NUM = Num()

def h1(title):
    NUM.section += 1
    NUM.counts = dict()
    story.append(Paragraph('%d.&nbsp;&nbsp;%s' % (NUM.section, title), S['h1']))

def env(kind, label, text):
    name = label or ('%s %s' % (kind, NUM.next(kind)))
    story.append(Paragraph('<b>%s.</b>&nbsp; %s' % (mm(name.rstrip('.')), mm(text)), S['thm']))

def proof(text):
    story.append(Paragraph('<i>Proof.</i>&nbsp; ' + mm(text) +
                           '&nbsp;&nbsp;<font name="Sym">\u25a1</font>', S['proof']))

def p(text, style='body'):
    story.append(Paragraph(mm(text), S[style]))

EQN = [0]
def eqn():
    EQN[0] += 1
    return EQN[0]

def eq(text, num=None):
    if num is None:
        story.append(Paragraph(mm(text), S['eq']))
    else:
        t = Table([[Paragraph(mm(text), S['eq']),
                    Paragraph('(%d)' % num, S['eqnum'])]],
                  colWidths=[None, 30])
        t.setStyle(TableStyle([('VALIGN', (0, 0), (-1, -1), 'MIDDLE'),
                               ('LEFTPADDING', (0, 0), (-1, -1), 0),
                               ('RIGHTPADDING', (0, 0), (-1, -1), 0),
                               ('TOPPADDING', (0, 0), (-1, -1), 0),
                               ('BOTTOMPADDING', (0, 0), (-1, -1), 0)]))
        story.append(t)

def box(lines):
    cells = [[Paragraph(mm(l), S['box'])] for l in lines]
    t = Table(cells, colWidths=[None])
    t.setStyle(TableStyle([
        ('BOX', (0, 0), (-1, -1), 0.8, colors.Color(0.35, 0.35, 0.35)),
        ('BACKGROUND', (0, 0), (-1, -1), colors.Color(0.965, 0.965, 0.94)),
        ('LEFTPADDING', (0, 0), (-1, -1), 9),
        ('RIGHTPADDING', (0, 0), (-1, -1), 9),
        ('TOPPADDING', (0, 0), (-1, -1), 4),
        ('BOTTOMPADDING', (0, 0), (-1, -1), 4),
    ]))
    story.append(t)
    story.append(Spacer(1, 6))

def bib(num, text):
    story.append(Paragraph('[%d]&nbsp;&nbsp;%s' % (num, mm(text)), S['bib']))

# frequent atoms
def xa(i): return '*x*_{*a*_{%s}}' % i
def xb(i): return '*x*_{*b*_{%s}}' % i
def ya(i): return '*y*_{*a*_{%s}}' % i
def yb(i): return '*y*_{*b*_{%s}}' % i
def A_(i): return '*a*_{%s}' % i
def B_(i): return '*b*_{%s}' % i

def h1u(title):  # unnumbered section heading (References)
    story.append(Paragraph(title, S['h1']))

# ================================ FRONT MATTER ==================================
story.append(Paragraph('Local v-numbers of binomial edge ideals of crown graphs', S['title']))
story.append(Paragraph('An ordinary-proof research draft', S['subtitle']))
story.append(Paragraph('6 November 2026 &nbsp;-&nbsp; research draft; author line omitted', S['dateline']))

box([
 '<b>DRAFT - ordinary proof; formalization PENDING.</b> '
 'This manuscript is a research draft containing a complete ordinary (pen-and-paper) proof. '
 'A Lean formalization of the main theorem is in progress but not complete: no kernel-checked '
 'Lean endpoint, replay, or certificate exists in the evidence accompanying this draft, and no '
 'completed formalization, acceptance, or campaign credit is claimed here.',
 '<b>Evidence status.</b> Literal-fidelity and ordinary-mathematics reviews: PASS. Root '
 'qualification: bounded (credit 0; campaign count 52/60); acceptance: PENDING. No author, '
 'affiliation, priority, or novelty-certification claim is made.',
])

story.append(Paragraph(mm('<b>Abstract.</b>&nbsp; Let <i>G</i> = <i>C</i>_{<i>n,n</i>} be the crown '
 'graph, obtained from the complete bipartite graph <i>K</i>_{<i>n,n</i>} by deleting a perfect '
 'matching, and let <i>J</i>_{<i>G</i>} be its binomial edge ideal over a field <i>K</i>, in 4<i>n</i> '
 'variables. We prove that for every field <i>K</i>, every <i>n</i> \u2265 4, and every cut set '
 '<i>T</i> \u2208 <i>C</i>(<i>G</i>), the local v-number of <i>J</i>_{<i>G</i>} at the determinantal prime '
 '<i>P</i>_{<i>T</i>}(<i>G</i>) equals four: <i>v</i>_{<i>P</i>_{<i>T</i>}(<i>G</i>)}(<i>J</i>_{<i>G</i>}) = 4. The argument is '
 'uniform over all fields, including characteristic two. Lower bounds follow from a '
 'vertex-support analysis of multihomogeneous components and a Gauss-lemma divisibility by a '
 'product of two nonassociate irreducible 2 x 2 minors; matching upper bounds are explicit '
 'quartic witnesses. This settles the v-number conjecture for crown graphs, Conjecture 5.6 of '
 'Kumar, Pomeroy and Tran, simultaneously for every cut-point prime. The full-side cases carry '
 'the substantive step; the remaining cases and all quartic witnesses follow known source '
 'constructions. Ordinary proof only: the formalization status is stated in the box above and '
 'in Section 11.'), S['abstract']))
story.append(Spacer(1, 4))

# ============================== 1 INTRODUCTION ==================================
h1('Introduction')

p('Throughout, <i>K</i> is an arbitrary field and <i>n</i> \u2265 4 is an integer. The '
 '<i>crown graph</i> <i>G</i> = <i>C</i>_{<i>n,n</i>} has vertex set <i>V</i> = <i>X</i> \u222a <i>Y</i> with '
 '<i>X</i> = {'+A_('1')+', ..., '+A_('n')+'} and <i>Y</i> = {'+B_('1')+', ..., '+B_('n')+'}, and its '
 'edges are exactly '+A_('i')+B_('j')+' with <i>i</i> \u2260 <i>j</i>; thus <i>G</i> is <i>K</i>_{<i>n,n</i>} '
 'with the perfect matching {'+A_('i')+B_('i')+'} deleted. It is connected, has 2<i>n</i> vertices, '
 'and is (<i>n</i> \u2212 1)-regular. On the polynomial ring <i>S</i> = <i>K</i>[<i>x</i>_{<i>v</i>}, '
 '<i>y</i>_{<i>v</i>} : <i>v</i> \u2208 <i>V</i>] in 4<i>n</i> variables over <i>K</i> sits the binomial edge '
 'ideal <i>J</i>_{<i>G</i>} introduced in [1]; our conventions follow [3] and are fixed in '
 'Section 2.')

p('For a subset <i>T</i> \u2286 <i>V</i>, the determinantal prime <i>P</i>_{<i>T</i>}(<i>G</i>) is recalled '
 'in Section 2; for the crown graph, the deleted sets <i>T</i> that occur are classified in '
 '[3, Theorem 3.3]. Following the source literature, the <i>local v-number</i> of '
 '<i>J</i>_{<i>G</i>} at <i>P</i>_{<i>T</i>}(<i>G</i>) is the minimum total degree of a homogeneous '
 '<i>f</i> \u2208 <i>S</i> with the exact colon equality (<i>J</i>_{<i>G</i>} : <i>f</i>) = '
 '<i>P</i>_{<i>T</i>}(<i>G</i>); see Definition 2.3. Section 3 relates this reading to the module '
 'formulation used in [3, Lemma 5.7].')

p('<b>The problem.</b> Let <i>C</i>(<i>G</i>) be the family of cut sets of <i>G</i> (Definition 2.2). '
 'The source [3, Section 5] proves 3 \u2264 <i>v</i>(<i>J</i>_{<i>G</i>}) \u2264 4 for <i>n</i> \u2265 4, '
 'the upper bound <i>v</i>_{<i>P</i>_{<i>T</i>}(<i>G</i>)}(<i>J</i>_{<i>G</i>}) \u2264 4 for every <i>T</i> \u2208 '
 '<i>C</i>(<i>G</i>), and equality for <i>T</i> = \u2205; the value 4 at <i>every</i> cut-point prime is '
 'Conjecture 5.6 of [3], recorded as MathDB problem 369163 [6]. The mixed two-component cuts '
 'are known over the complex numbers by [4, Theorem 4.15]. The following uniform statement '
 'completes the conjecture for all cut primes and all fields at once.')

env('Theorem', 'Theorem 1.1 (main theorem).',
 '<i>Let <i>K</i> be a field, let <i>n</i> \u2265 4, let <i>G</i> = <i>C</i>_{<i>n,n</i>} be the crown '
 'graph, and let <i>J</i>_{<i>G</i>} \u2282 <i>S</i> be its binomial edge ideal. Then for every '
 '<i>T</i> \u2208 <i>C</i>(<i>G</i>),</i>')
eq('<i>v</i>_{<i>P</i>_{<i>T</i>}(<i>G</i>)}(<i>J</i>_{<i>G</i>}) = 4.', 1)

p('In particular the minimum in Definition 2.3 is attained, and no homogeneous polynomial of '
 'degree at most three has exact colon <i>P</i>_{<i>T</i>}(<i>G</i>) for any cut <i>T</i>. A stronger '
 'equality on low-degree pieces is recorded in Corollary 9.2.')

p('<b>Strategy and credit.</b> Everything rests on two elementary lemmas: an exact-separator characterization for a finite irredundant decomposition into pairwise incomparable primes (Lemma 3.1), and a contraction lemma that tests membership of a multihomogeneous component on its support by setting all other coordinates to zero (Lemma 4.2). The lower bound at the full-side primes <i>P</i>_{<i>X</i>} and <i>P</i>_{<i>Y</i>} (Propositions 5.1 and 5.2) is the substantive step: a separator of degree at most three is divisible by a product of two nonassociate irreducible quadrics, hence has degree at least four. The one-deleted-side bounds (Section 6) and the empty and mixed bounds (Section 7) are short support computations, and the lower bound is assembled in Theorem 7.3. The nonempty-cut quartic witnesses in Section 8 follow [3, Proposition 5.2], up to relabeling and coordinate symmetry; its Q-case subscript slip is corrected by direct verification. The empty-prime monomial uses [3, Lemma 5.1] and [2, Proposition 3.6]. None of these witnesses is new. No determinantal quotient is ever assumed to be a unique factorization domain, and no characteristic is excluded. In keeping with the accompanying reviews, no worldwide-novelty or priority claim is made; the bounded qualification record is summarized in Section 11.')

p('<b>Organization.</b> Section 2 fixes notation and the six families of cut-point primes. '
 'Sections 3 and 4 prove the two reduction lemmas. Sections 5, 6 and 7 prove the lower bound '
 'family by family, assembled in Theorem 7.3. Section 8 gives the quartic witnesses, and '
 'Section 9 concludes the proof of Theorem 1.1, together with the low-degree equality of '
 'Corollary 9.2. Section 10 compares the result with the source and prior theorems, and '
 'Section 11 records status, limitations and reproducibility.')

# ================= 2 THE CROWN GRAPH AND ITS CUT-POINT PRIMES ===================
h1('The crown graph and its cut-point primes')

env('Notation', 'Notation 2.1 (rings, minors, ideals).',
 'Variables are indexed by vertices: the coordinate pair of '+A_('i')+' is ('+xa('i')+', '+ya('i')+'), '
 'and that of '+B_('j')+' is ('+xb('j')+', '+yb('j')+'). For distinct <i>u</i>, <i>v</i> \u2208 <i>V</i> put '
 '[<i>u</i>, <i>v</i>] = <i>x</i>_{<i>u</i>}<i>y</i>_{<i>v</i>} \u2212 <i>x</i>_{<i>v</i>}<i>y</i>_{<i>u</i>}, '
 'a 2 x 2 minor of the two-row matrix with columns (<i>x</i>_{<i>w</i>}, <i>y</i>_{<i>w</i>})_{<i>w</i>}. '
 'For <i>W</i> \u2286 <i>V</i> set <i>D</i>(<i>W</i>) = ([<i>u</i>, <i>v</i>] : <i>u</i>, <i>v</i> \u2208 <i>W</i>) '
 'and <i>L</i>(<i>W</i>) = (<i>x</i>_{<i>w</i>}, <i>y</i>_{<i>w</i>} : <i>w</i> \u2208 <i>W</i>). The binomial '
 'edge ideal of <i>G</i> is <i>J</i>_{<i>G</i>} = ([ '+A_('i')+', '+B_('j')+' ] : <i>i</i> \u2260 <i>j</i>); it is '
 'quadratic and homogeneous. All degrees in this paper are ordinary total degrees, except for '
 'the finer vertex grading introduced in Section 4.')

env('Definition', 'Definition 2.2 (cut sets).',
 'For <i>T</i> \u2286 <i>V</i> let <i>G</i>_{<i>V</i>\u2216<i>T</i>} denote the induced subgraph on '
 '<i>V</i> \u2216 <i>T</i>. Following [1, Corollary 3.9], <i>T</i> is a <i>cut set</i>, written '
 '<i>T</i> \u2208 <i>C</i>(<i>G</i>), if <i>T</i> = \u2205, or if every <i>t</i> \u2208 <i>T</i> is a cut vertex '
 'of the induced subgraph on (<i>V</i> \u2216 <i>T</i>) \u222a {<i>t</i>}.')

env('Definition', 'Definition 2.3 (local v-number).', 'Let <i>I</i> ⊆ <i>S</i> be a homogeneous ideal and <i>P</i> a minimal prime of <i>I</i>. The local v-number of <i>I</i> at <i>P</i> is <i>v</i>_{<i>P</i>}(<i>I</i>) = min{ <i>d</i> ≥ 0 : some nonzero homogeneous <i>f</i> ∈ <i>S</i> of degree <i>d</i> satisfies (<i>I</i> : <i>f</i>) = <i>P</i> }, provided this set is nonempty.')

env('Theorem', 'Theorem 2.4 (the cut-point primes; [1], Section 3 and Theorem 3.3 of [3]).',
 'Let <i>n</i> \u2265 4. The binomial edge ideal <i>J</i>_{<i>G</i>} is radical, and its minimal '
 'prime ideals are exactly the following pairwise distinct, pairwise incomparable primes, '
 'whose intersection is <i>J</i>_{<i>G</i>}:')
eq('<i>P</i>_{0} = <i>D</i>(<i>V</i>),&nbsp;&nbsp;&nbsp;&nbsp;'
   '<i>P</i>_{<i>X</i>} = <i>L</i>(<i>X</i>),&nbsp;&nbsp;&nbsp;&nbsp;<i>P</i>_{<i>Y</i>} = <i>L</i>(<i>Y</i>),<br/>'
   '<i>Q</i>_{<i>i</i>} = <i>L</i>(<i>X</i> \u2212 {'+A_('i')+'}) + <i>D</i>({'+A_('i')+'} \u222a (<i>Y</i> \u2212 {'
   +B_('i')+'})),<br/>'
   '<i>R</i>_{<i>i</i>} = <i>L</i>(<i>Y</i> \u2212 {'+B_('i')+'}) + <i>D</i>({'+B_('i')+'} \u222a (<i>X</i> \u2212 {'
   +A_('i')+'}))&nbsp;&nbsp;&nbsp;for 1 \u2264 <i>i</i> \u2264 <i>n</i>,<br/>'
   '<i>M</i>_{<i>ij</i>} = <i>L</i>(<i>V</i> \u2212 {'+A_('i')+', '+B_('i')+', '+A_('j')+', '+B_('j')+'}) + '
   '([ '+A_('i')+', '+B_('j')+' ], [ '+A_('j')+', '+B_('i')+' ]),&nbsp;&nbsp;&nbsp;1 \u2264 <i>i</i> &lt; '
   '<i>j</i> \u2264 <i>n</i>,', 2)

proof('By [1, Corollary 2.2] the ideal <i>J</i>_{<i>G</i>} is radical, and by [1, Theorem 3.2, Corollary 3.9] its minimal primes are the ideals <i>P</i>_{<i>T</i>}(<i>G</i>) as <i>T</i> ranges over <i>C</i>(<i>G</i>), where for <i>T</i> with <i>G</i>_{<i>V</i>∖<i>T</i>} having connected components <i>C</i>_{1}, ..., <i>C</i>_{<i>r</i>} one takes <i>P</i>_{<i>T</i>}(<i>G</i>) to be <i>L</i>(<i>T</i>) together with, for each connected component <i>C</i> of the induced subgraph on <i>V</i> − <i>T</i>, the ideal of 2 x 2 minors supported on the completion of <i>C</i> to a clique. For the crown, every completion is a clique, so the general form specializes to the displayed ideals once the cut sets are known. The classification of cut sets is [3, Theorem 3.3]: for <i>n</i> ≥ 3 the nonempty <i>T</i> ∈ <i>C</i>(<i>G</i>) are exactly <i>X</i>; <i>Y</i>; <i>X</i> − {*a*_{i}}; <i>Y</i> − {*b*_{i}}; and the sets <i>T</i> = <i>A</i> ∪ { *b*_{c} : *a*_{c} ∈ <i>A</i> } with <i>A</i> ⊆ <i>X</i>, |<i>A</i>| = <i>n</i> − 2, which are <i>T</i> = <i>V</i> − {*a*_{i}, *b*_{i}, *a*_{j}, *b*_{j}} for a pair <i>i</i> &lt; <i>j</i>. The empty set occurs because <i>G</i> is connected, giving <i>P</i>_{0} = <i>D</i>(<i>V</i>); the mixed cut with surviving index pair {<i>i</i>, <i>j</i>} gives <i>M</i>_{<i>ij</i>}. Each displayed ideal is prime by the completed-component prime theorem [1, Section 3], applied to its disjoint completed components; isolated surviving coordinates remain free. Distinctness of the six families follows from their degree-one parts, which are <i>L</i>(<i>T</i>) for the six distinct deleted sets <i>T</i> (for <i>P</i>_{0} the degree-one part is zero, and 2<i>n</i> − 4 &gt; 0 since <i>n</i> ≥ 4, so no mixed prime has empty L-part). As minimal primes of a radical ideal they are pairwise incomparable, and radicality identifies their intersection with <i>J</i>_{<i>G</i>} itself, not merely with its radical. Every vertex degree of the classification is strict for <i>n</i> ≥ 4, which is the only structural place the hypothesis <i>n</i> ≥ 4 enters; the full-side witnesses of Section 8 use it as well.')

env('Remark', 'Remark 2.5 (normalization of the mixed indices).',
 '<i>M</i>_{<i>ij</i>} is indexed by the unordered pair {<i>i</i>, <i>j</i>}: '
 '<i>M</i>_{<i>ij</i>} = <i>M</i>_{<i>ji</i>} is a single ideal; distinct pairs {<i>i</i>, <i>j</i>} have distinct deleted sets, '
 'hence give distinct ideals, and the same holds across the six families. Thus a statement about <i>M</i>_{<i>ij</i>} for unspecified <i>i</i>, <i>j</i> is to be '
 'read with <i>i</i> &lt; <i>j</i>, and references to <i>M</i>_{<i>ij</i>} with <i>j</i> &lt; <i>i</i> denote '
 '<i>M</i>_{<i>ji</i>}.')

env('Remark', 'Remark 2.6 (the shape of <i>Q</i>_{<i>i</i>} and <i>R</i>_{<i>i</i>}).',
 'In <i>Q</i>_{<i>i</i>} the completed component is the clique on {'+A_('i')+'} \u222a (<i>Y</i> \u2212 {'
 +B_('i')+'}): the vertex '+A_('i')+' lies in the same completed component as all of <i>Y</i> \u2212 {'
 +B_('i')+'}, while '+B_('i')+' is isolated. Omitting '+A_('i')+' from the determinantal block would '
 'give a different, wrong ideal. In particular, one cannot test nonmembership in <i>Q</i>_{<i>i</i>} '
 'by setting all <i>X</i>-coordinates to zero; the correct specializations are computed in '
 'Section 8.3. The description of <i>R</i>_{<i>i</i>} is symmetric.')

# ===================== 3 THE EXACT-SEPARATOR REDUCTION ==========================
h1('The exact-separator lemma')

env('Lemma', 'Lemma 3.1 (exact separators).',
 'Let <i>J</i> = \u2229_{\u03bb} <i>P</i>_{\u03bb} be a finite irredundant decomposition into primes '
 'which are pairwise incomparable, and let <i>P</i>_{\u03c4} be one of them. Then for <i>f</i> \u2208 '
 '<i>S</i> one has (<i>J</i> : <i>f</i>) = <i>P</i>_{\u03c4} if and only if <i>f</i> \u2209 <i>P</i>_{\u03c4} and '
 '<i>f</i> \u2208 <i>P</i>_{\u03bb} for every \u03bb \u2260 \u03c4.')

proof('For a prime <i>P</i> and <i>f</i> \u2208 <i>S</i> one has (<i>P</i> : <i>f</i>) = <i>P</i> if '
 '<i>f</i> \u2209 <i>P</i>, and (<i>P</i> : <i>f</i>) = <i>S</i> if <i>f</i> \u2208 <i>P</i>: the first '
 'because <i>P</i> prime and <i>f</i>, <i>g</i> \u2209 <i>P</i> force <i>fg</i> \u2209 <i>P</i>, so '
 '(<i>P</i> : <i>f</i>) \u2286 <i>P</i>; the second because <i>fg</i> \u2208 <i>P</i> for all <i>g</i> '
 'when <i>f</i> \u2208 <i>P</i>. Distributing the colon over the decomposition, '
 '(<i>J</i> : <i>f</i>) = \u2229 { <i>P</i>_{\u03bb} : <i>f</i> \u2209 <i>P</i>_{\u03bb} }. If <i>f</i> \u2209 '
 '<i>P</i>_{\u03c4} and <i>f</i> \u2208 <i>P</i>_{\u03bb} for \u03bb \u2260 \u03c4, the index set is {<i>τ</i>} '
 'and the equality follows. Conversely suppose (<i>J</i> : <i>f</i>) = <i>P</i>_{\u03c4}. The index '
 'set is nonempty, for otherwise (<i>J</i> : <i>f</i>) = <i>S</i>, while <i>P</i>_{\u03c4} is proper. '
 'If the index set contained no <i>τ</i>, then from each intersectand <i>P</i>_{\u03bb}, \u03bb \u2260 '
 '<i>τ</i>, one may choose <i>g</i>_{\u03bb} \u2208 <i>P</i>_{\u03bb} \u2216 <i>P</i>_{\u03c4}, which is '
 'possible because the primes are incomparable and distinct; their product lies in the '
 'intersection, hence in <i>P</i>_{\u03c4}, but outside <i>P</i>_{\u03c4} since the latter is prime, a '
 'contradiction. Pairwise incomparability likewise excludes any additional intersectand '
 'besides <i>P</i>_{\u03c4}: if <i>P</i>_{\u03c4} \u2229 <i>P</i>_{\u03bc} appeared with \u03bc \u2260 \u03c4 the '
 'intersection would equal <i>P</i>_{\u03c4} only if <i>P</i>_{\u03c4} \u2286 <i>P</i>_{\u03bc}. Hence the index '
 'set is exactly {<i>τ</i>}, that is, <i>f</i> \u2209 <i>P</i>_{\u03c4} and <i>f</i> \u2208 <i>P</i>_{\u03bb} for '
 'all other \u03bb.')

env('Remark', 'Remark 3.2 (zero and constant witnesses; the module reading).',
 'If <i>f</i> = 0 then (<i>J</i> : <i>f</i>) = <i>S</i>, and if <i>f</i> is a nonzero constant then '
 '<i>f</i> lies in no member of the decomposition and (<i>J</i> : <i>f</i>) = <i>J</i>; neither is a '
 'proper cut prime, so every exact-colon witness is nonconstant. Furthermore, distributing as '
 'in the proof and using incomparability exactly as above gives (<i>J</i> : '
 '<i>P</i>_{\u03c4}) = \u2229_{\u03bb\u2260\u03c4} <i>P</i>_{\u03bb}, because (<i>P</i>_{\u03bb} : '
 '<i>P</i>_{\u03c4}) = <i>P</i>_{\u03bb} for \u03bb \u2260 \u03c4: if <i>g</i> \u2209 <i>P</i>_{\u03bb} and '
 '<i>g</i><i>P</i>_{\u03c4} \u2286 <i>P</i>_{\u03bb}, the image of <i>P</i>_{\u03c4} in the domain '
 '<i>S</i>/<i>P</i>_{\u03bb} is annihilated by a nonzero class, hence vanishes, forcing <i>P</i>_{\u03c4} '
 '\u2286 <i>P</i>_{\u03bb}. Consequently a class <i>g</i> of positive degree in '
 '(\u2229_{\u03bb\u2260\u03c4}<i>P</i>_{\u03bb})/<i>J</i> lies outside <i>P</i>_{\u03c4}, being outside '
 '<i>J</i> while inside every other factor, and Lemma 3.1 turns it into an exact-colon '
 'witness; and conversely, via the same two lemmas, a homogeneous <i>f</i> with '
 '(<i>J</i> : <i>f</i>) = <i>P</i>_{\u03c4} is the same datum as a nonzero class in '
 '(\u2229_{\u03bb\u2260\u03c4}<i>P</i>_{\u03bb})/<i>J</i> of the same degree. This is the reading of the '
 'invariant used in [3, Lemma 5.7]; here it is derived directly, and no colon inclusion is '
 'ever treated as an equality of ideals.')

p('Throughout the paper, (2) denotes this six-family list; its members are the minimal '
 'primes of <i>J</i>_{<i>G</i>}, and unindexed references such as <i>P</i>_{\u03bb} range over it. '
 'For the lower bound it suffices to prove the following implication, for every '
 '<i>P</i>_{\u03c4} in (2) and every homogeneous <i>f</i> of degree <i>d</i> \u2264 3:')
eq('<i>f</i> \u2208 \u2229_{\u03bb\u2260\u03c4} <i>P</i>_{\u03bb}&nbsp;&nbsp;implies&nbsp;&nbsp;'
   '<i>f</i> \u2208 <i>P</i>_{\u03c4}.', 3)
p('Indeed, if (<i>J</i>_{<i>G</i>} : <i>f</i>) = <i>P</i>_{\u03c4} with <i>d</i> \u2264 3, Lemma 3.1 gives '
 '<i>f</i> \u2209 <i>P</i>_{\u03c4} and <i>f</i> \u2208 <i>P</i>_{\u03bb} for all other \u03bb; (3) then '
 'forces <i>f</i> \u2208 <i>P</i>_{\u03c4} as well. A homogeneous <i>f</i> of degree at most '
 'three with (<i>J</i>_{<i>G</i>} : <i>f</i>) = <i>P</i>_{\u03c4} would thus satisfy both <i>f</i> \u2209 '
 '<i>P</i>_{\u03c4}, by Lemma 3.1, and <i>f</i> \u2208 <i>P</i>_{\u03c4}, by (3): a contradiction. '
 'Hence, once (3) is proved for a prime <i>P</i>_{\u03c4}, no homogeneous polynomial of degree '
 'at most three has exact colon <i>P</i>_{\u03c4}, i.e. <i>v</i>_{<i>P</i>_{\u03c4}}(<i>J</i>_{<i>G</i>}) '
 '\u2265 4. Sections 5, 6 and 7 prove (3) for each family of (2).')

# ============= 4 MULTIGRADING, RESTRICTION AND CONTRACTION ======================
h1('Multigrading, restriction and contraction')

p('Give <i>x</i>_{<i>v</i>} and <i>y</i>_{<i>v</i>} both degree <i>e</i>_{<i>v</i>} in '
 '<i>N</i>^{<i>V</i>}, the free commutative monoid on the vertices. Every generator displayed '
 'in Section 2, and every generator of <i>J</i>_{<i>G</i>}, is homogeneous for this '
 '<i>V</i>-grading; hence so is each of the primes in (2) and their intersection. In '
 'consequence:')

env('Lemma', 'Lemma 4.1 (multihomogeneous components).',
 'Let <i>I</i> be one of the ideals in (2) or <i>J</i>_{<i>G</i>} itself, and <i>f</i> \u2208 <i>S</i> '
 'with multihomogeneous components <i>f</i>_{\u03b1} of multidegree \u03b1. Then <i>f</i> \u2208 <i>I</i> '
 'if and only if <i>f</i>_{\u03b1} \u2208 <i>I</i> for every \u03b1. A nonzero component of ordinary '
 'degree <i>d</i> has vertex support supp(\u03b1) = { <i>v</i> : \u03b1_{<i>v</i>} &gt; 0 } of size at '
 'most <i>d</i>; if the size equals 3 and <i>d</i> \u2264 3, then <i>d</i> = 3 and \u03b1 is 1 at '
 'each supported vertex. Moreover, if supp(\u03b1) meets the deleted set <i>T</i> of a prime '
 '<i>P</i>_{<i>T</i>} from (2), then every monomial of <i>f</i>_{\u03b1} is divisible by <i>x</i>_{<i>w</i>} '
 'or <i>y</i>_{<i>w</i>} for some <i>w</i> \u2208 supp(\u03b1) \u2229 <i>T</i>, so <i>f</i>_{\u03b1} \u2208 '
 '<i>L</i>(<i>T</i>) \u2286 <i>P</i>_{<i>T</i>} automatically.')

proof('Homogeneity of <i>I</i> gives <i>I</i> = \u2295_{\u03b1} <i>I</i>_{\u03b1} as a direct sum of its '
 'pieces, and a decomposition of <i>f</i> into multihomogeneous parts is unique, so membership '
 'is componentwise. If <i>f</i>_{\u03b1} \u2260 0 its ordinary degree is the sum \u2211_{<i>v</i>} '
 '\u03b1_{<i>v</i>} (each monomial of multidegree \u03b1 has total degree \u2211\u03b1_{<i>v</i>}), '
 'giving |supp(\u03b1)| \u2264 <i>d</i>, with equality forcing \u03b1 \u2261 1 on its support when the '
 'support has three vertices and <i>d</i> \u2264 3. For the last claim, a monomial of multidegree '
 '\u03b1 involves the variable pair of <i>v</i> whenever \u03b1_{<i>v</i>} &gt; 0, since the total '
 'exponent of <i>x</i>_{<i>v</i>} and <i>y</i>_{<i>v</i>} in that monomial is exactly '
 '\u03b1_{<i>v</i>}. If some <i>w</i> \u2208 supp(\u03b1) \u2229 <i>T</i>, every monomial is therefore '
 'divisible by <i>x</i>_{<i>w</i>} or <i>y</i>_{<i>w</i>} \u2208 <i>L</i>(<i>T</i>).')

env('Lemma', 'Lemma 4.2 (retraction and contraction).',
 'Let <i>U</i> \u2286 <i>V</i> and let \u03c0 : <i>S</i> \u2192 <i>S</i>_{<i>U</i>} = <i>K</i>[<i>x</i>_{<i>v</i>}, '
 '<i>y</i>_{<i>v</i>} : <i>v</i> \u2208 <i>U</i>] be the retraction setting all coordinates outside '
 '<i>U</i> to zero, so that \u03c0 restricts to the identity on <i>S</i>_{<i>U</i>}. For each ideal '
 '<i>I</i> of (2), the contraction <i>I</i> \u2229 <i>S</i>_{<i>U</i>} is generated, as an ideal of '
 '<i>S</i>_{<i>U</i>}, by exactly those displayed generators whose support lies in <i>U</i>: the '
 'surviving linear coordinates <i>x</i>_{<i>w</i>}, <i>y</i>_{<i>w</i>} with <i>w</i> \u2208 <i>U</i> \u2229 '
 '(deleted set), and the minors [<i>u</i>, <i>v</i>] with <i>u</i>, <i>v</i> \u2208 <i>U</i> from the '
 'determinantal block. Consequently, a polynomial <i>h</i> supported in <i>U</i> (i.e. in '
 '<i>S</i>_{<i>U</i>}) satisfies <i>h</i> \u2208 <i>I</i> if and only if <i>h</i> lies in that '
 'survivor ideal.')

proof('Each displayed generator maps under \u03c0 either to itself, when both indices lie in '
 '<i>U</i>, or to 0, when some index does not; this holds for linear generators and for '
 'minors alike. Hence \u03c0(<i>I</i>) is the survivor ideal. If <i>h</i> \u2208 <i>I</i> \u2229 '
 '<i>S</i>_{<i>U</i>} then <i>h</i> = \u03c0(<i>h</i>) \u2208 \u03c0(<i>I</i>), since \u03c0 fixes '
 '<i>S</i>_{<i>U</i>} pointwise; conversely \u03c0(<i>g</i>) \u2208 <i>I</i> for every generator, '
 'being either a generator or 0, so the survivor ideal is contained in <i>I</i> \u2229 '
 '<i>S</i>_{<i>U</i>}. This is a computation on ideals, not on monomials: it applies to '
 'arbitrary coefficient combinations, repeated vertex degrees and all cancellations, and no '
 'elimination theorem or determinantal-quotient structure is used. The characterization of '
 'membership of supported polynomials follows since such <i>h</i> lies in <i>S</i>_{<i>U</i>}.')

env('Remark', 'Remark 4.3.',
 'Lemmas 4.1 and 4.2 together reduce every membership below to a statement about polynomial '
 'rings in at most three pairs of variables. Characteristic two requires no separate treatment: '
 'no sign, no determinant and no factoriality argument below depends on the characteristic, and '
 'the two spots where a sign appears explicitly (the evaluations in Section 8) are computed '
 'with the sign retained.')

# ================ 5 LOWER BOUND: FULL-SIDE PRIMES ===============================
h1('The lower bound at the full-side primes')

env('Proposition', 'Proposition 5.1 (<i>P</i>_{<i>X</i>}).',
 'Every homogeneous <i>f</i> of degree <i>d</i> \u2264 3 with <i>f</i> \u2208 \u2229_{\u03bb\u2260'
 '<i>P</i>_{X}}<i>P</i>_{\u03bb} satisfies <i>f</i> \u2208 <i>P</i>_{<i>X</i>}; thus implication (3) holds '
 'for <i>P</i>_{<i>X</i>}.')

p('<i>Proof.</i>&nbsp; Work componentwise (Lemma 4.1). A component whose support meets <i>X</i> lies in <i>P</i>_{<i>X</i>} = <i>L</i>(<i>X</i>) automatically. Consider a nonzero component <i>h</i> supported in <i>U</i> ⊆ <i>Y</i>. Since <i>P</i>_{<i>Y</i>}, all <i>Q</i>_{<i>i</i>}, all <i>R</i>_{<i>i</i>}, all <i>M</i>_{<i>ij</i>} and <i>P</i>_{0} are among the primes of (2) different from <i>P</i>_{<i>X</i>}, membership <i>h</i> ∈ <i>Q</i>_{<i>i</i>} for every <i>i</i> is available. By Lemma 4.2, <i>h</i> ∈ <i>Q</i>_{<i>i</i>} ∩ <i>S</i>_{<i>U</i>}, and the survivor ideal of <i>Q</i>_{<i>i</i>} in <i>S</i>_{<i>U</i>} is generated by the minors of <i>D</i>(<i>Y</i> − {*b*_{i}}) with both endpoints in <i>U</i>; there are none unless |<i>U</i> − {*b*_{i}}| ≥ 2.', 'proof')

p('If |<i>U</i>| \u2264 2, choose <i>i</i> \u2208 <i>U</i> when <i>U</i> is nonempty and any '
 '<i>i</i> otherwise. Fewer than two supported vertices survive in <i>Y</i> \u2212 {'
 +B_('i')+'}, so the survivor ideal is zero and <i>h</i> = 0.')
p('Otherwise |<i>U</i>| = 3, so <i>d</i> = 3 and, by Lemma 4.1, \u03b1 equals 1 at each vertex '
 'of <i>U</i> = {'+B_('r')+', '+B_('s')+', '+B_('t')+'}. The restrictions of <i>Q</i>_{<i>r</i>} and '
 '<i>Q</i>_{<i>s</i>} give, in <i>S</i>_{<i>U</i>},')
eq('<i>h</i> \u2208 ([ '+B_('s')+', '+B_('t')+' ])&nbsp;&nbsp;&nbsp;and&nbsp;&nbsp;&nbsp;'
   '<i>h</i> \u2208 ([ '+B_('r')+', '+B_('t')+' ]).', None)
p('These two quadrics are irreducible and nonassociate in the polynomial unique factorization domain <i>S</i>_{<i>U</i>}, over any field. Indeed, as a polynomial in *x*_{*b*_{s}}, the minor [ *b*_{s}, *b*_{t} ] = *x*_{*b*_{s}}*y*_{*b*_{t}} − *x*_{*b*_{t}}*y*_{*b*_{s}} is linear and primitive: its coefficients *y*_{*b*_{t}} and −*x*_{*b*_{t}}*y*_{*b*_{s}} have no nonconstant common divisor, so Gauss’s lemma proves irreducibility. Nonassociation follows from the distinct vertex multidegrees of the two minors. Irreducible elements of this unique factorization domain are prime, and two nonassociate irreducibles are coprime; since both divide <i>h</i>, their product divides <i>h</i>. A nonzero multiple of that product has degree at least 4 &gt; 3 = <i>d</i>, so <i>h</i> = 0. The coefficient pair is coprime in characteristic two as well, where − equals +; no sign or factoriality beyond the polynomial ring <i>S</i>_{<i>U</i>} is used, and in particular no unique factorization of a determinantal quotient. Hence every pure-<i>Y</i> component of <i>f</i> vanishes, the remaining components lie in <i>P</i>_{<i>X</i>}, and <i>f</i> ∈ <i>P</i>_{<i>X</i>}. □')

env('Proposition', 'Proposition 5.2 (<i>P</i>_{<i>Y</i>}).',
 'Implication (3) holds for <i>P</i>_{<i>Y</i>} as well: every homogeneous <i>f</i> of degree '
 '\u2264 3 with <i>f</i> \u2208 \u2229_{\u03bb\u2260<i>P</i>_{Y}}<i>P</i>_{\u03bb} satisfies <i>f</i> \u2208 '
 '<i>P</i>_{<i>Y</i>}.')
proof('Apply the symmetry that exchanges <i>x</i> with <i>y</i> and *a*_{i} with *b*_{i} for each index. It fixes <i>J</i>_{<i>G</i>}, <i>P</i>_{0} and each <i>M</i>_{<i>ij</i>}, exchanges <i>P</i>_{<i>X</i>} and <i>P</i>_{<i>Y</i>}, and exchanges <i>Q</i>_{<i>i</i>} with <i>R</i>_{<i>i</i>}; it preserves homogeneity and degree. Let σ denote this involution. Then σ(<i>f</i>) satisfies the hypothesis of Proposition 5.1 for <i>P</i>_{<i>X</i>}; hence σ(<i>f</i>) ∈ <i>P</i>_{<i>X</i>}, and applying σ again gives <i>f</i> ∈ <i>P</i>_{<i>Y</i>}.')

env('Remark', 'Remark 5.3.',
 'Propositions 5.1 and 5.2 are the obstructions that the earlier partial results do not '
 'supply: a separator for <i>P</i>_{<i>X</i>} of degree at most three would have to be a common '
 'multiple of two nonassociate irreducible quadrics, hence of degree at least four. The '
 'argument uses unique factorization only in the polynomial ring <i>S</i>_{<i>U</i>}, never in a '
 'determinantal quotient, and is valid over every field including characteristic two.')

# ================ 6 LOWER BOUND: ONE-DELETED-SIDE PRIMES ========================
h1('The lower bound at the one-deleted-side primes')

env('Proposition', 'Proposition 6.1 (<i>Q</i>_{<i>i</i>}).',
 'For every <i>i</i>, implication (3) holds for <i>Q</i>_{<i>i</i>}: every homogeneous <i>f</i> of '
 'degree \u2264 3 with <i>f</i> \u2208 \u2229_{\u03bb\u2260<i>Q</i>_{i}}<i>P</i>_{\u03bb} satisfies '
 '<i>f</i> \u2208 <i>Q</i>_{<i>i</i>}.')
p('<i>Proof.</i>&nbsp; Work componentwise, and fix <i>i</i>. A component whose support meets <i>X</i> − {*a*_{i}} lies in <i>L</i>(<i>X</i> − {*a*_{i}}) automatically. So consider a nonzero component <i>h</i> with support <i>U</i> ⊆ {*a*_{i}} ∪ <i>Y</i>. Since <i>P</i>_{<i>X</i>} is a prime of (2) different from <i>Q</i>_{<i>i</i>}, <i>h</i> ∈ <i>P</i>_{<i>X</i>}; the piece of <i>P</i>_{<i>X</i>} = <i>L</i>(<i>X</i>) in the multidegree of <i>h</i> is nonzero only if some vertex of <i>X</i> has positive vertex degree, and the only vertex of <i>X</i> available is *a*_{i}: thus α_{*a*_{i}} &gt; 0, i.e. <i>h</i> has positive *a*_{i}-degree.', 'proof')

p('If '+B_('i')+' \u2209 <i>U</i>: membership in <i>P</i>_{0} = <i>D</i>(<i>V</i>) holds, and Lemma 4.2 '
 'gives <i>h</i> \u2208 <i>D</i>(<i>U</i>), the survivor ideal being generated by all pairs in <i>U</i>. '
 'Since <i>U</i> \u2286 {'+A_('i')+'} \u222a (<i>Y</i> \u2212 {'+B_('i')+'}) in this case, '
 '<i>D</i>(<i>U</i>) \u2286 <i>D</i>({'+A_('i')+'} \u222a (<i>Y</i> \u2212 {'+B_('i')+'})) \u2286 '
 '<i>Q</i>_{<i>i</i>}, as required.')

p('If *b*_{i} ∈ <i>U</i>: the degree is at most three and both *a*_{i} and *b*_{i} occur, leaving room for at most one further vertex, which would be some *b*_{j} with <i>j</i> ≠ <i>i</i> (no further *a*_{c} can occur, the support being contained in {*a*_{i}} ∪ <i>Y</i>). If such a *b*_{j} occurs, then <i>U</i> = {*a*_{i}, *b*_{i}, *b*_{j}} exactly. The prime <i>M</i>_{<i>ij</i>} (its pair unordered, Remark 2.5) is a member of (2) different from <i>Q</i>_{<i>i</i>}, so <i>h</i> ∈ <i>M</i>_{<i>ij</i>}; by Lemma 4.2 its survivor ideal in <i>S</i>_{<i>U</i>} is generated solely by [ *a*_{i}, *b*_{j} ], the other generator [ *a*_{j}, *b*_{i} ] having the unsupported endpoint *a*_{j}. Hence <i>h</i> ∈ ([ *a*_{i}, *b*_{j} ]) ⊆ <i>Q</i>_{<i>i</i>}, since *a*_{i} and *b*_{j} lie in the block {*a*_{i}} ∪ (<i>Y</i> − {*b*_{i}}).')

p('If no such '+B_('j')+' occurs, then <i>U</i> = {'+A_('i')+', '+B_('i')+'}. Choose any '
 '<i>j</i> \u2260 <i>i</i> and use <i>M</i>_{<i>ij</i>} again: its contraction to the ring in '
 '<i>x</i>_{'+A_('i')+'}, <i>y</i>_{'+A_('i')+'}, <i>x</i>_{'+B_('i')+'}, <i>y</i>_{'+B_('i')+'} is '
 'zero, because both defining minors have an endpoint outside the pair; hence <i>h</i> = 0. '
 'The argument nowhere assumes squarefree exponents, so arbitrary powers supported on these '
 'two vertices are covered as well.')

p('Every component has now been treated, so <i>f</i> ∈ <i>Q</i>_{<i>i</i>}. This is a symbolic support argument, uniform in <i>n</i>: <i>h</i> throughout is an arbitrary homogeneous polynomial in the indicated multidegree, not a tested monomial. □')

env('Corollary', 'Corollary 6.2 (<i>R</i>_{<i>i</i>}).',
 'For every <i>i</i>, implication (3) holds for <i>R</i>_{<i>i</i>} as well.')
proof('This is Proposition 6.1 read through the symmetry of the proof of Proposition 5.2, '
 'which exchanges <i>Q</i>_{<i>i</i>} and <i>R</i>_{<i>i</i>} while preserving the list (2), '
 'homogeneity and degree.')

# ============= 7 LOWER BOUND: EMPTY AND MIXED PRIMES ============================
h1('The lower bound at the empty and mixed primes')

env('Proposition', 'Proposition 7.1 (<i>P</i>_{0}).',
 'Implication (3) holds for <i>P</i>_{0} = <i>D</i>(<i>V</i>).')
proof('Let <i>h</i> be a nonzero component of <i>f</i>, supported in <i>U</i>, not automatic in '
 '<i>P</i>_{0}: since <i>D</i>(<i>V</i>) has empty L-part, no support is automatic, and the '
 'argument below uses the other memberships. Membership in <i>P</i>_{<i>X</i>} and '
 '<i>P</i>_{<i>Y</i>} (both different from <i>P</i>_{0}) forces, by Lemma 4.1, positive degree at '
 'some vertex of <i>X</i> and at some vertex of <i>Y</i>: the support meets both sides. With '
 'degree at most three, one side is a singleton, say {'+A_('i')+'} on the <i>X</i>-side (the '
 'other case is symmetric). Then <i>h</i> \u2208 <i>Q</i>_{<i>i</i>}, and the survivor ideal of '
 '<i>Q</i>_{<i>i</i>} in <i>S</i>_{<i>U</i>} is generated by minors [ '+A_('i')+', '+B_('c')+' ] '
 'with '+B_('c')+' \u2208 <i>U</i> \u2229 (<i>Y</i> \u2212 {'+B_('i')+'}), the L-part '
 '<i>L</i>(<i>X</i> \u2212 {'+A_('i')+'}) contributing nothing as no other '+A_('c')+' occurs. Each '
 'such minor has both endpoints in <i>U</i>, so <i>h</i> \u2208 <i>D</i>(<i>U</i>) \u2286 '
 '<i>D</i>(<i>V</i>) = <i>P</i>_{0}. If instead the singleton is '+B_('j')+' on the <i>Y</i>-side, '
 'the same argument with <i>R</i>_{<i>j</i>} applies. This independently recovers the already '
 'known lower bound at the empty prime, where the exact value 4 is [3, Lemma 5.1] via '
 'connected domination [2].')

env('Proposition', 'Proposition 7.2 (the mixed primes <i>M</i>_{<i>ij</i>}).',
 'For every pair <i>i</i> &lt; <i>j</i>, implication (3) holds for <i>M</i>_{<i>ij</i>}.')
proof('Fix the pair and write <i>W</i> = {'+A_('i')+', '+B_('i')+', '+A_('j')+', '+B_('j')+'}. A '
 'component that is not automatic in <i>M</i>_{<i>ij</i>} has support <i>U</i> \u2286 <i>W</i>, the '
 'deleted set of <i>M</i>_{<i>ij</i>} being <i>V</i> \u2212 <i>W</i>. Membership in <i>P</i>_{<i>X</i>} '
 'and <i>P</i>_{<i>Y</i>} again forces both sides in the support, and degree at most three '
 'forces one side to be a singleton: one of '+A_('i')+', '+A_('j')+', '+B_('i')+', ' +B_('j')+'. If it is '+A_('i')+', <i>h</i> \u2208 <i>Q</i>_{<i>i</i>}, whose survivor ideal in '
 '<i>S</i>_{<i>U</i>} is generated, if at all, by [ '+A_('i')+', '+B_('j')+' ]: the L-part '
 'contributes nothing ('+A_('j')+' \u2209 <i>U</i>), and among the block minors only '
 '[ '+A_('i')+', '+B_('j')+' ] has both endpoints in <i>U</i>. Likewise '+A_('j')+' singleton '
 'gives [ '+A_('j')+', '+B_('i')+' ] via <i>Q</i>_{<i>j</i>}, and a singleton '+B_('i')+' or '
 +B_('j')+' gives, via <i>R</i>_{<i>i</i>} or <i>R</i>_{<i>j</i>} in exactly the symmetric way, the '
 'minor [ '+A_('j')+', '+B_('i')+' ] or [ '+A_('i')+', '+B_('j')+' ], or nothing. All these '
 'testing primes differ from <i>M</i>_{<i>ij</i>} - they remain distinct even at <i>n</i> = 4, '
 'by Remark 2.5 and distinct deleted sets - and each displayed minor is a generator of '
 '<i>M</i>_{<i>ij</i>}. Hence <i>h</i> \u2208 <i>M</i>_{<i>ij</i>} or <i>h</i> = 0, and '
 '<i>f</i> \u2208 <i>M</i>_{<i>ij</i>}. This support route also avoids the informal comparison of '
 'two representations modulo <i>J</i>_{<i>G</i>} used in the proof of [3, Lemma 5.7].')

env('Theorem', 'Theorem 7.3 (the lower bound).',
 'For every field <i>K</i>, every <i>n</i> \u2265 4, and every <i>T</i> \u2208 <i>C</i>(<i>G</i>), '
 'no homogeneous polynomial of degree at most three has exact colon '
 '<i>P</i>_{<i>T</i>}(<i>G</i>); equivalently, <i>v</i>_{<i>P</i>_{<i>T</i>}(<i>G</i>)}(<i>J</i>_{<i>G</i>}) '
 '\u2265 4.')
proof('By Theorem 2.4 the minimal primes of <i>J</i>_{<i>G</i>} are exactly the members of (2), '
 'and <i>P</i>_{<i>T</i>}(<i>G</i>) is one of them. Propositions 5.1, 5.2 and 6.1, Corollary 6.2 '
 'and Propositions 7.1 and 7.2 establish implication (3) for every member. The reduction '
 'after Remark 3.2 then rules out separators of degree at most three, as recorded there.')

# ===================== 8 QUARTIC WITNESSES ======================================
h1('Quartic witnesses')

p('The witnesses of this section are homogeneous of degree four; their membership and nonmembership verifications are direct. For nonempty cuts these are the constructions of [3, Proposition 5.2], up to relabeling and coordinate symmetry; its Q-case subscript slip is corrected explicitly below. The empty-prime monomial follows from the connected dominating set in [3, Lemma 5.1] and the construction [2, Proposition 3.6]. No witness is new. Distinct indices <i>i</i>, <i>j</i>, <i>k</i> appear below; the full-side witnesses use four distinct vertices of one side, which is where <i>n</i> ≥ 4 is needed, while the remaining witnesses need at most three distinct indices.')

env('Construction', 'Construction 8.1 (a witness for <i>P</i>_{0}).',
 'Put <i>f</i> = '+xa('1')+xa('3')+xb('1')+xb('2')+'.')
proof('Every member of (2) other than <i>P</i>_{0} contains <i>f</i>: its deleted set meets '
 '{'+A_('1')+', '+A_('3')+', '+B_('1')+', '+B_('2')+'}. The full sides do so trivially; a '
 'one-deleted side retains all but one vertex of its side; and a mixed prime deletes only two '
 'indices, whereas these four vertices involve the three indices 1, 2, 3, so some supported '
 'vertex survives in the L-part and the corresponding linear generator divides <i>f</i>. For '
 'nonmembership in <i>P</i>_{0} = <i>D</i>(<i>V</i>), specialize <i>x</i>_{<i>v</i>} = '
 '<i>t</i>_{<i>v</i>} and <i>y</i>_{<i>v</i>} = 0: every generator [<i>u</i>, <i>v</i>] of '
 '<i>D</i>(<i>V</i>) maps to <i>t</i>_{<i>u</i>}\u00b70 \u2212 <i>t</i>_{<i>v</i>}\u00b70 = 0, so the image '
 'of <i>P</i>_{0} is zero, while <i>f</i> maps to the nonzero monomial '
 '<i>t</i>_{'+A_('1')+'}<i>t</i>_{'+A_('3')+'}<i>t</i>_{'+B_('1')+'}<i>t</i>_{'+B_('2')+'}. Hence '
 '(<i>J</i>_{<i>G</i>} : <i>f</i>) = <i>P</i>_{0} by Lemma 3.1.')

env('Construction', 'Construction 8.2 (a witness for <i>P</i>_{<i>X</i>}).',
 'Put <i>f</i> = [ '+B_('1')+', '+B_('2')+' ]\u00b7[ '+B_('3')+', '+B_('4')+' ], a product of two '
 'disjoint Y-minors; use the symmetric construction [ '+A_('1')+', '+A_('2')+' ]\u00b7[ '
 +A_('3')+', '+A_('4')+' ] for <i>P</i>_{<i>Y</i>}.')
proof('The polynomial is a nonzero element of the Y-subring, so it is outside '
 '<i>P</i>_{<i>X</i>} = <i>L</i>(<i>X</i>): the survivor ideal of <i>L</i>(<i>X</i>) in the '
 'Y-subring is zero (Lemma 4.2), and <i>f</i> \u2260 0 there. It lies in <i>P</i>_{0}, both '
 'factors being minors in <i>D</i>(<i>V</i>). For <i>Q</i>_{<i>i</i>}: one of the two disjoint '
 'pairs avoids the index <i>i</i>, and its minor lies in the block <i>D</i>({'+A_('i')+'} \u222a '
 '(<i>Y</i> \u2212 {'+B_('i')+'})). For <i>P</i>_{<i>Y</i>} and every <i>R</i>_{<i>i</i>}: each '
 'two-vertex Y-minor [ '+B_('c')+', '+B_('d')+' ] lies in <i>L</i>(<i>Y</i>), and in '
 '<i>L</i>(<i>Y</i> \u2212 {'+B_('i')+'}) as soon as <i>c</i> \u2260 <i>i</i> or <i>d</i> \u2260 <i>i</i>, '
 'which holds for one of the two factors; expanding, each monomial of that factor is '
 'divisible by an available coordinate, so the factor, and then <i>f</i>, lies in '
 '<i>R</i>_{<i>i</i>}. For a mixed prime <i>M</i>_{<i>rs</i>}: at least one of the four distinct '
 'Y-vertices '+B_('1')+', '+B_('2')+', '+B_('3')+', '+B_('4')+' survives in its L-part, and the '
 'factor containing it lies in the prime; hence so does the product. Together with '
 'Lemma 3.1 this gives (<i>J</i>_{<i>G</i>} : <i>f</i>) = <i>P</i>_{<i>X</i>}, and symmetrically '
 'for the A-minor witness and <i>P</i>_{<i>Y</i>}.')

w, z = xa('i'), xb('k')
env('Construction', 'Construction 8.3 (a witness for <i>Q</i>_{<i>i</i>}).',
 'Choose distinct indices <i>i</i>, <i>j</i>, <i>k</i> and put <i>f</i> = '+w+z+'[ '
 +B_('i')+', '+B_('j')+' ].')
proof('Membership. The factor '+w+' places <i>f</i> in <i>P</i>_{<i>X</i>} and in every '
 '<i>Q</i>_{<i>l</i>} with <i>l</i> \u2260 <i>i</i>. The minor is a generator of <i>D</i>(<i>V</i>), '
 'so <i>f</i> \u2208 <i>P</i>_{0}; the minor lies in <i>L</i>(<i>Y</i>), each of its monomials '
 'being divisible by an '+xb('c')+' or '+yb('c')+', so <i>f</i> \u2208 <i>P</i>_{<i>Y</i>}. For '
 '<i>R</i>_{<i>l</i>}: if <i>l</i> \u2260 <i>k</i> the factor '+z+' lies in <i>L</i>(<i>Y</i> \u2212 {'
 +B_('l')+'}), while if <i>l</i> = <i>k</i> the minor lies in <i>L</i>(<i>Y</i> \u2212 {'+B_('k')+'}), '
 'its monomials being divisible by coordinates of '+B_('i')+' or '+B_('j')+', indices distinct '
 'from <i>k</i>. Finally let <i>M</i>_{<i>rs</i>} be a mixed prime, with deleted set <i>T</i> = '
 '<i>V</i> \u2212 {'+A_('r')+', '+B_('r')+', '+A_('s')+', '+B_('s')+'}. If '+A_('i')+' \u2208 <i>T</i>, '
 'every monomial of <i>f</i> is divisible by '+w+'; if instead '+B_('k')+' \u2208 <i>T</i>, every '
 'monomial is divisible by '+z+'; otherwise <i>i</i>, <i>k</i> \u2208 {<i>r</i>, <i>s</i>}, i.e. '
 '{<i>r</i>, <i>s</i>} = {<i>i</i>, <i>k</i>}, and then '+B_('j')+' \u2208 <i>T</i>, so the two '
 'monomials '+w+z+xb('i')+yb('j')+' and '+w+z+xb('j')+yb('i')+' are divisible by '+yb('j')+' '
 'and '+xb('j')+' respectively. In every case some divisor of each monomial lies in '
 '<i>L</i>(<i>T</i>), whence <i>f</i> \u2208 <i>M</i>_{<i>rs</i>}.')

p('Nonmembership in <i>Q</i>_{<i>i</i>}. Let \u03c6 be the ring homomorphism that keeps '+w+' '
 'and every '+xb('c')+', '+B_('c')+' \u2208 <i>Y</i> \u2212 {'+B_('i')+'}, as indeterminates, and '
 'sends to zero the following coordinates: both coordinates of every '+A_('c')+' with '
 '<i>c</i> \u2260 <i>i</i>; '+ya('i')+'; '+yb('c')+' for all '+B_('c')+' \u2208 <i>Y</i> \u2212 {'
 +B_('i')+'}; and '+xb('i')+', while '+yb('i')+' is sent to a new indeterminate <i>s</i>. '
 'Every generator of <i>Q</i>_{<i>i</i>} maps to 0 - the linear generators by construction, '
 'and each block minor because its monomials contain a vanishing y-coordinate. '
 'Hence the image of <i>Q</i>_{<i>i</i>} is zero, while the image of the witness is')
eq('\u03c6(<i>f</i>) = '+w+ z + '\u00b7( '+xb('i')+'\u00b70 \u2212 '+xb('j')+'\u00b7<i>s</i> ) = '
   '\u2212'+w+z+xb('j')+'\u00b7<i>s</i>,', None)
p('the negative of a nonzero monomial, nonzero in every characteristic. Thus <i>f</i> \u2209 '
 '<i>Q</i>_{<i>i</i>}, and Lemma 3.1 gives (<i>J</i>_{<i>G</i>} : <i>f</i>) = <i>Q</i>_{<i>i</i>}. '
 'The symmetric witness '+yb('i')+ya('k')+'[ '+A_('i')+', '+A_('j')+' ] for <i>R</i>_{<i>i</i>} is '
 'obtained from the symmetry of Section 5, which exchanges <i>Q</i>_{<i>i</i>} and '
 '<i>R</i>_{<i>i</i>}, preserves the list (2) and degrees, and whose mirrored specialization '
 'proves nonmembership; we do not spell the mirror out.')

env('Construction', 'Construction 8.4 (a witness for <i>M</i>_{<i>ij</i>}).',
 'For <i>i</i> &lt; <i>j</i> put <i>f</i> = [ '+A_('i')+', '+A_('j')+' ]\u00b7[ '+B_('i')+', '
 +B_('j')+' ], a product of one X-pair minor and one Y-pair minor.')
proof('Membership. Each factor is a generator of <i>D</i>(<i>V</i>), so <i>f</i> \u2208 '
 '<i>P</i>_{0}. The X-pair minor [ '+A_('i')+', '+A_('j')+' ] lies in <i>L</i>(<i>X</i>), its '
 'monomials '+xa('i')+ya('j')+' and '+xa('j')+ya('i')+' being divisible by X-coordinates; '
 'hence <i>f</i> \u2208 <i>P</i>_{<i>X</i>}, and symmetrically <i>f</i> \u2208 <i>P</i>_{<i>Y</i>} '
 'through the Y-pair minor. For <i>Q</i>_{<i>l</i>}: the X-pair minor lies in <i>L</i>(<i>X</i> \u2212 {'
 +A_('l')+'}) for every <i>l</i>, since each of '+xa('i')+ya('j')+', '+xa('j')+ya('i')+' is '
 'divisible by a coordinate of '+A_('c')+' with <i>c</i> \u2208 {<i>i</i>,<i>j</i>} \u2229 ([<i>n</i>] \u2212 '
 '{<i>l</i>}) with <i>c</i> \u2260 <i>l</i>, which exists because <i>i</i> \u2260 <i>j</i>. '
 'Hence <i>f</i> \u2208 <i>Q</i>_{<i>l</i>} for every <i>l</i>, and, symmetrically through the '
 'Y-pair minor, <i>f</i> \u2208 <i>R</i>_{<i>l</i>} for every <i>l</i>. Let <i>M</i>_{<i>rs</i>} \u2260 '
 '<i>M</i>_{<i>ij</i>} be a mixed prime, with deleted set <i>T</i>. At least one of '+A_('i')+', '
 +A_('j')+' lies in <i>T</i>, since otherwise {<i>r</i>, <i>s</i>} = {<i>i</i>, <i>j</i>}; write '
 +A_('c')+' for it, <i>c</i> \u2208 {<i>i</i>, <i>j</i>}. Both monomials of the X-pair minor are '
 'then divisible by '+xa('c')+' or '+ya('c')+', so that minor, and with it <i>f</i>, lies in '
 '<i>L</i>(<i>T</i>) \u2286 <i>M</i>_{<i>rs</i>}.')

p('Nonmembership in <i>M</i>_{<i>ij</i>}. Evaluate the coordinate columns '
 '('+xa('i')+', '+ya('i')+') and ('+xb('j')+', '+yb('j')+') at (1, 0), the columns '
 '('+xa('j')+', '+ya('j')+') and ('+xb('i')+', '+yb('i')+') at (0, 1), and all remaining '
 'columns at 0. The linear generators of the L-part vanish, and the two block minors '
 'evaluate as 1\u00b70 \u2212 1\u00b70 = 0 and 0\u00b71 \u2212 0\u00b71 = 0, so the image of '
 '<i>M</i>_{<i>ij</i>} is zero. The image of the witness is')
eq('( 1\u00b71 \u2212 0\u00b70 )\u00b7( 0\u00b70 \u2212 1\u00b71 ) = \u22121,', None)
p('nonzero in every characteristic, characteristic two included. Hence <i>f</i> \u2209 '
 '<i>M</i>_{<i>ij</i>}, and Lemma 3.1 gives (<i>J</i>_{<i>G</i>} : <i>f</i>) = <i>M</i>_{<i>ij</i>}.')
p('This construction needs only two distinct indices; the full-side witnesses of '
 'Construction 8.2 are the ones requiring four distinct vertices, hence <i>n</i> \u2265 4.')

# ============== 9 THE MAIN THEOREM AND THE LOW-DEGREE EQUALITY ==================
h1('The main theorem and the low-degree equality')

env('Theorem', 'Theorem 9.1 (Theorem 1.1 restated).',
 'For every field <i>K</i>, every <i>n</i> \u2265 4, and every <i>T</i> \u2208 <i>C</i>(<i>G</i>), '
 '<i>v</i>_{<i>P</i>_{<i>T</i>}(<i>G</i>)}(<i>J</i>_{<i>G</i>}) = 4.')
proof('By Theorem 2.4, <i>P</i>_{<i>T</i>}(<i>G</i>) is one of the primes of (2). For the upper '
 'bound, take for that prime the witness of Constructions 8.1 to 8.4 (<i>P</i>_{0}: 8.1; '
 '<i>P</i>_{<i>X</i>} and <i>P</i>_{<i>Y</i>}: 8.2; <i>Q</i>_{<i>i</i>} and <i>R</i>_{<i>i</i>}: 8.3; '
 '<i>M</i>_{<i>ij</i>}: 8.4). Each witness is homogeneous of degree 4, lies in every other member '
 'of (2), and is outside its own prime; by Lemma 3.1 its exact colon is the prime, so '
 '<i>v</i> \u2264 4. The lower bound is Theorem 7.3.')

env('Corollary', 'Corollary 9.2 (the low-degree equality).',
 'For every prime <i>P</i>_{\u03c4} of (2) and every <i>d</i> \u2264 3,')
eq('(\u2229_{\u03bb \u2260 \u03c4} <i>P</i>_{\u03bb})_{<i>d</i>} = (<i>J</i>_{<i>G</i>})_{<i>d</i>},', None)
proof('For the nontrivial inclusion take a homogeneous <i>h</i> of degree <i>d</i> in the left '
 'side. Implication (3) for the prime <i>P</i>_{\u03c4}, proved in Sections 5 to 7, gives '
 '<i>h</i> \u2208 <i>P</i>_{\u03c4}; combined with membership in the other factors, <i>h</i> lies in '
 'every member of (2), i.e. in <i>J</i>_{<i>G</i>}. The reverse inclusion is immediate since '
 '<i>J</i>_{<i>G</i>} is contained in every <i>P</i>_{\u03bb}. By Remark 3.2 the left side is also '
 '(<i>J</i>_{<i>G</i>} : <i>P</i>_{\u03c4})_{<i>d</i>}.')

env('Remark', 'Remark 9.3.',
 'Corollary 9.2 packages the lower bounds in ideal-theoretic form and is an explicit target '
 'for independent re-verification during the formalization effort. We also record the '
 'bookkeeping used throughout: the zero polynomial is not a witness, since a proper prime is '
 'never the unit ideal; and each low-degree equality is a statement about homogeneous pieces, '
 'to be read through the multigrading of Section 4.')

# ============== 10 RELATION TO THE SOURCE AND PRIOR RESULTS =====================
h1('Relation to the source and prior results')

p('<b>The source.</b> Reference [3] proves <i>v</i>_{<i>P</i>_{∅}(<i>G</i>)}(<i>J</i>_{<i>G</i>}) = 4 (its Lemma 5.1, via the connected-domination identity for the empty prime in [2, Theorem 3.2] and γ_{<i>c</i>}(<i>G</i>) = 4), the bounds 3 ≤ <i>v</i>(<i>J</i>_{<i>G</i>}) ≤ 4 and <i>v</i>_{<i>P</i>_{<i>T</i>}(<i>G</i>)}(<i>J</i>_{<i>G</i>}) ≤ 4 (its Lemmas 5.4 and Proposition 5.2, respectively, the latter supplying the nonempty-cut quartic witnesses up to relabeling and coordinate symmetry), and poses the all-cuts statement as its Conjecture 5.6. Its Lemma 5.7 treats the mixed cuts <i>T</i> = <i>A</i> ∪ { *b*_{c} : *a*_{c} ∈ <i>A</i> } with |<i>A</i>| = <i>n</i> − 2 through the identity <i>v</i>_{<i>P</i>_{<i>T</i>}}(<i>J</i>_{<i>G</i>}) = α((<i>J</i>_{<i>G</i>} : <i>P</i>_{<i>T</i>})/<i>J</i>_{<i>G</i>}), used there and derived directly in Section 3 of this draft; its proof compares two representations modulo <i>J</i>_{<i>G</i>}, a step the support argument of Section 7 avoids. Two presentational defects of the published text are corrected here without changing the mathematics: the mixed-prime indexing is normalized to unordered pairs (Remark 2.5), and the Q-case of [3, Proposition 5.2] verifies its witness against the X-primes, a copied subscript slip whose intended statement is verified directly in Construction 8.3.')

p('<b>Two-component cuts over the complex numbers.</b> Reference [4] works over <i>C</i> and its localized results require a minimal cut in the sense of its Definition 2.3: the deleted set leaves exactly two connected components. Its Theorem 4.15 applies to the crown cuts <i>Q</i>_{<i>i</i>}, <i>R</i>_{<i>i</i>} and <i>M</i>_{<i>ij</i>}, whose complements have two components. Under [4, Definition 4.6], the chosen vertices in each surviving component must form a connected dominating set in that component and also dominate the subgraph obtained by adjoining the deleted set <i>T</i>. For <i>Q</i>_{<i>i</i>}, the star-side choice must contain *a*_{i} and at least two distinct leaves *b*_{j}, *b*_{k}: with only *b*_{j}, the deleted *a*_{j} is undominated, while two distinct leaves dominate every deleted X-vertex. The isolated *b*_{i} also dominates all deleted X-vertices, giving 3 + 1 = 4. For <i>M</i>_{<i>ij</i>}, both endpoints of each edge are required to dominate deleted vertices on both sides, giving 2 + 2 = 4. The <i>R</i>_{<i>i</i>} case is symmetric. The full-side cuts <i>P</i>_{<i>X</i>} and <i>P</i>_{<i>Y</i>} instead leave <i>n</i> ≥ 4 singleton components, outside the two-component hypothesis; the equality case in Theorem 3.5 of [4] requires radicality of <i>J</i>_{<i>G</i>} + <i>J</i>_{transversal}, not radicality of the colon itself. Identifying that sum with the colon is the missing equality step; degree information about a transversal alone does not supply it. No transfer across fields is stated there. Thus [4] does not supply the full-side or uniform positive-characteristic result.')

p('<b>Combinatorial bounds.</b> Reference [5] studies transversal bounds '
 '<i>v</i>_{<i>S</i>}^{<i>\u2212</i>}(<i>G</i>) \u2264 <i>v</i>_{<i>P</i>_{<i>S</i>}(<i>G</i>)}(<i>J</i>_{<i>G</i>}) \u2264 '
 '<i>v</i>_{<i>S</i>}^{<i>+</i>}(<i>G</i>). For the crown it yields <i>v</i>_{<i>X</i>}^{<i>\u2212</i>} = 3, '
 'uniformly for <i>n</i> \u2265 4: any two Y-vertices miss a hyperedge of the relevant outside-X '
 'cuts, while every three-element set meets each. Its equality criterion requires every '
 'surviving component to be noncomplete (hypothesis (H) there); for every nonempty crown cut '
 'some component is a singleton or a complete edge, so (H) fails and the gap 3-4 is not '
 'closed there either.')

p('<b>Closed-graph formulas.</b> Reference [9] computes local v-numbers for generalized '
 'binomial edge ideals; its strongest formula requires the graph to be connected and closed, '
 'in which setting maximal cliques carry interval labels. A crown with <i>n</i> \u2265 4 has an '
 'induced claw - '+A_('1')+' with three of its Y-neighbors - and an induced claw cannot sit '
 'inside interval-labeled cliques, since two of its leaves force a leaf-leaf edge; the '
 'formula therefore does not apply to crowns. Its remaining results (the empty prime, and the '
 'classification of values 1 and 2) do not bear on the full-side degree-three obstruction.')

p('<b>Summary of provenance.</b> The empty value is known ([3, Lemma 5.1] with [2]); the mixed value is known, in the present generality of the lower bound re-derived in Section 7 and, over <i>C</i>, by [4]; the one-deleted-side values are known over <i>C</i> by [4, Theorem 4.15], and Proposition 6.1 removes the field restriction by an elementary argument; the full-side lower bounds of Section 5 are, per the bounded comparison above, not supplied by the literature inspected, and they are what makes the uniform statement Theorem 1.1 possible. The nonempty-cut quartic witnesses are due to [3, Proposition 5.2], up to relabeling and coordinate symmetry; the empty-prime witness uses [3, Lemma 5.1] and [2, Proposition 3.6]. No claim of worldwide novelty, priority, or exhaustive coverage is made: the accompanying record keeps version, chronology and citing-coverage questions open as bounded, not complete. No publisher text is reproduced in this draft; only statements, values and bibliographic data appear, the latter checked against the retained sources.')

# ============== 11 STATUS, LIMITATIONS, REPRODUCIBILITY =========================
h1('Status, limitations, and reproducibility')

p('<b>Status.</b> This is an ordinary-proof research draft: Sections 2 to 9 contain a complete '
 'pen-and-paper proof of Theorem 1.1, and nothing in this paper is a formalization claim. A '
 'Lean formalization of Theorem 1.1 is in preparation in a separate work lane; at the time of '
 'writing it is incomplete, and no kernel-checked theorem, no replay, and no certificate '
 'exists. Acceptance, credit, and count updates are campaign-level decisions outside this '
 'manuscript; the recorded state is 52 of 60 accepted results with zero credit for this '
 'candidate.')

p('<b>Limitations.</b> The accompanying record verifies the statement and the ordinary '
 'mathematics, while keeping bounded residuals open: the published and prepublication sources '
 'were compared on the relevant sections only; two chronology questions concerning prior '
 'versions remain open; correction and citing coverage is bounded, not exhaustive; and the '
 'publisher bodies were read through ordinary authorized access, which is not a claim of open '
 'licensing. These limitations qualify the provenance remarks of Section 10; they do not '
 'enter the proof itself.')

p('<b>Reproducibility.</b> The PDF is typeset by the generator manuscript/generate_paper.py '
 '(ReportLab; Liberation Serif with Symbola fallback for math glyphs), rendered page by page '
 'with poppler-utils, and every rendered page was visually inspected before release; the '
 'per-page inspection record is kept with the artifact. The mathematical inputs are the '
 'frozen evidence lanes (root proof, independent review, primary comparison, source '
 'ideation, root qualification), all re-verified by SHA-256 against frozen-inputs.json, 129 '
 'files, before and after generation. The companion files REPRODUCE.md, PROOF-COVERAGE.json '
 'and artifact-hashes.json document the build, the section-by-section coverage of every '
 'proof obligation, and the artifact hashes.')

h1u('References')

bib(1, 'J. Herzog, T. Hibi, F. Hreinsd\u00f3ttir, T. Kahle, J. Rauh: Binomial edge ideals and '
 'conditional independence statements. Adv. Appl. Math. 45 (2010), no. 3, 317-333; '
 'preprint arXiv:0909.4717.')
bib(2, 'D. Jaramillo-Velez, L. Seccia: Connected domination in graphs and v-numbers of '
 'binomial edge ideals. Collect. Math. 75 (2024), no. 3, 771-793.')
bib(3, 'A. Kumar, J. Pomeroy, L. Tran: Binomial edge ideals of crown graphs. J. Algebraic '
 'Combin. 62 (2025), no. 3, article no. 51; doi:10.1007/s10801-025-01464-w; preprint '
 'arXiv:2507.03889.')
bib(4, 'E. Liwski: The V-number of binomial edge ideals: minimal cuts and cycle graphs. '
 'Collect. Math. (2026); doi:10.1007/s13348-026-00511-4. Preprint arXiv:2507.02161 (2025).')
bib(5, 'E. Liwski: Combinatorial bounds for the v-number of binomial edge ideals. Preprint '
 'arXiv:2610.18213 (2026).')
bib(6, 'MathDB problem 369163: The v-number conjecture for crown graphs. '
 'mathdb.com/p/369163; statement as retrieved 2026.')
bib(7, 'F. Mohammadi, L. Sharifan: Hilbert function of binomial edge ideals. Comm. Algebra '
 '42 (2014), no. 2, 688-703.')
bib(8, 'M. Ohtani: Graphs and ideals generated by some 2-minors. Comm. Algebra 39 (2011), '
 'no. 3, 905-917.')
bib(9, 'Y.-H. Shen, G. Zhu: The v-number of generalized binomial edge ideals of some graphs. '
 'Preprint arXiv:2603.29516 (2026).')

# ------------------------------- build -----------------------------------------
from reportlab.platypus.doctemplate import NextPageTemplate
story.insert(0, NextPageTemplate('Later'))

doc = BaseDocTemplate(
    OUT, pagesize=A4,
    leftMargin=22 * MM, rightMargin=22 * MM, topMargin=20 * MM, bottomMargin=20 * MM,
    title='Local v-numbers of binomial edge ideals of crown graphs (ordinary-proof draft)',
    subject='MathDB 369163 - research draft, Lean formalization pending',
    creator='manuscript/generate_paper.py',
)
fr1 = Frame(22 * MM, 18 * MM, A4[0] - 44 * MM, A4[1] - 40 * MM, id='first',
            leftPadding=0, rightPadding=0, topPadding=0, bottomPadding=0)
fr2 = Frame(22 * MM, 20 * MM, A4[0] - 44 * MM, A4[1] - 44 * MM, id='later',
            leftPadding=0, rightPadding=0, topPadding=0, bottomPadding=0)
doc.addPageTemplates([
    PageTemplate(id='First', frames=[fr1], onPage=on_page),
    PageTemplate(id='Later', frames=[fr2], onPage=on_page),
])
doc.build(story)
print('written', OUT)
