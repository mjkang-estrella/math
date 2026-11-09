"""Typeset paper/manuscript.src into paper/manuscript.pdf (standard library only).

Usage (from the lane directory):
  python3 -I scripts/build_pdf.py paper/manuscript.src outputs/graph-facts.json outputs/search OUTDIR
Writes OUTDIR/manuscript.pdf and OUTDIR/manuscript-resolved.txt (the text with generated tables,
used by scripts/check_numbers.py).  Embeds whole TrueType fonts (CIDFontType2, Identity-H) with
ToUnicode maps.  Tables are generated from the fresh outputs, never typed by hand.
"""
import sys
sys.dont_write_bytecode = True
import json, os, re, struct, zlib, math
from html.parser import HTMLParser

FONTDIR = "/usr/share/fonts/"
FONTFILES = {
    "R": FONTDIR + "liberation-serif-fonts/LiberationSerif-Regular.ttf",
    "I": FONTDIR + "liberation-serif-fonts/LiberationSerif-Italic.ttf",
    "B": FONTDIR + "liberation-serif-fonts/LiberationSerif-Bold.ttf",
    "BI": FONTDIR + "liberation-serif-fonts/LiberationSerif-BoldItalic.ttf",
    "T": FONTDIR + "liberation-mono-fonts/LiberationMono-Regular.ttf",
    "M": FONTDIR + "google-noto/NotoSansMath-Regular.ttf",
}
PSNAMES = {"R": "LiberationSerif", "I": "LiberationSerif-Italic", "B": "LiberationSerif-Bold",
           "BI": "LiberationSerif-BoldItalic", "T": "LiberationMono", "M": "NotoSansMath-Regular"}

PW, PH = 612.0, 792.0
ML, MR, MT, MB = 64.0, 64.0, 62.0, 60.0
TW = PW - ML - MR
BODY, LEAD = 10.3, 13.2


def u16(b, o): return struct.unpack_from(">H", b, o)[0]
def i16(b, o): return struct.unpack_from(">h", b, o)[0]


class TTF:
    def __init__(self, key, path):
        self.key, self.path = key, path
        b = self.raw = open(path, "rb").read()
        self.tab = {}
        for i in range(u16(b, 4)):
            t = b[12 + 16 * i:16 + 16 * i].decode("latin1")
            self.tab[t] = struct.unpack_from(">II", b, 20 + 16 * i)
        h = self.t("head")
        self.upm = u16(h, 18)
        self.bbox = [i16(h, 36), i16(h, 38), i16(h, 40), i16(h, 42)]
        hh = self.t("hhea")
        self.asc, self.desc, nh = i16(hh, 4), i16(hh, 6), u16(hh, 34)
        hm = self.t("hmtx")
        self.adv = [u16(hm, 4 * i) for i in range(nh)]
        os2 = self.t("OS/2")
        self.cap = i16(os2, 88) if u16(os2, 0) >= 2 and len(os2) > 90 else int(self.asc * 0.7)
        post = self.t("post")
        self.italic = struct.unpack_from(">i", post, 4)[0] / 65536.0
        self.cmap = self._cmap()
        self.used = {}

    def t(self, name):
        o, l = self.tab[name]
        return self.raw[o:o + l]

    def _cmap(self):
        cm = self.t("cmap")
        subs = []
        for k in range(u16(cm, 2)):
            pid, eid, so = struct.unpack_from(">HHI", cm, 4 + 8 * k)
            if u16(cm, so) == 4:
                subs.append(((0 if (pid, eid) == (3, 1) else 1), so))
        subs.sort()
        so = subs[0][1]
        segx2 = u16(cm, so + 6)
        seg = segx2 // 2
        mp = {}
        for j in range(seg):
            end = u16(cm, so + 14 + 2 * j)
            start = u16(cm, so + 16 + segx2 + 2 * j)
            delta = i16(cm, so + 16 + 2 * segx2 + 2 * j)
            roff_at = so + 16 + 3 * segx2 + 2 * j
            ro = u16(cm, roff_at)
            for c in range(start, end + 1):
                if c == 0xFFFF:
                    continue
                if ro == 0:
                    g = (c + delta) & 0xFFFF
                else:
                    g = u16(cm, roff_at + ro + 2 * (c - start))
                    if g:
                        g = (g + delta) & 0xFFFF
                if g:
                    mp[c] = g
        return mp

    def width_gid(self, g):
        return self.adv[g] if g < len(self.adv) else self.adv[-1]


FONTS = {k: TTF(k, p) for k, p in FONTFILES.items()}
FALLBACK = ["M", "R"]


def font_for(ch, style):
    for k in [style] + FALLBACK:
        if ord(ch) in FONTS[k].cmap:
            return FONTS[k]
    raise SystemExit("no glyph for %r U+%04X" % (ch, ord(ch)))


def pieces(text, style):
    """split text into maximal runs rendered with one font"""
    out = []
    for ch in text:
        if ch == " ":
            ch = " "
        f = font_for(ch, style)
        if out and out[-1][0] is f:
            out[-1][1].append(ch)
        else:
            out.append((f, [ch]))
    return [(f, "".join(cs)) for f, cs in out]


def text_width(text, style, size):
    w = 0.0
    for f, s in pieces(text, style):
        w += sum(f.width_gid(f.cmap[ord(c)]) for c in s) * size / f.upm
    return w


# ---------------- inline markup ---------------------------------------------------------------
class Inline(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.st = {"i": 0, "b": 0, "tt": 0, "sub": 0, "sup": 0}
        self.runs = []

    def handle_starttag(self, tag, attrs):
        self.st[tag] += 1

    def handle_endtag(self, tag):
        self.st[tag] -= 1

    def handle_data(self, d):
        s = self.st
        style = "T" if s["tt"] else ("BI" if s["b"] and s["i"] else "B" if s["b"] else "I" if s["i"] else "R")
        script = "sub" if s["sub"] else ("sup" if s["sup"] else None)
        self.runs.append((d, style, script))


def parse_inline(markup, base_style="R"):
    p = Inline()
    p.feed(markup)
    p.close()
    runs = []
    for d, st, sc in p.runs:
        if base_style != "R":
            if st == "R":
                st = base_style
            elif st == "I" and base_style == "B":
                st = "BI"
            elif st == "B" and base_style == "I":
                st = "BI"
        runs.append((d, st, sc))
    return runs


def plain(markup):
    return "".join(d for d, _, _ in parse_inline(markup))


# ---------------- line breaking -----------------------------------------------------------------
def words_of(runs, size):
    """list of words; a word is a list of segments (text, style, size, rise); glue between words"""
    words, cur = [], []
    for text, style, script in runs:
        sz, rise = (size * 0.86 if style == "T" else size), 0.0
        if script == "sub":
            sz, rise = size * 0.7, -0.17 * size
        elif script == "sup":
            sz, rise = size * 0.7, 0.36 * size
        parts = re.split(r"( |\n)", text)
        for prt in parts:
            if prt in (" ", "\n"):
                if cur:
                    words.append(cur); cur = []
            elif prt:
                cur.append((prt, style, sz, rise))
    if cur:
        words.append(cur)
    return words


def word_width(w):
    return sum(text_width(t, st, sz) for t, st, sz, _ in w)


def split_long(w, maxw):
    """force-split a word wider than maxw (e.g. hashes) into several words"""
    if word_width(w) <= maxw:
        return [w]
    out, cur, curw = [], [], 0.0
    for t, st, sz, rise in w:
        for ch in t:
            cw = text_width(ch, st, sz)
            if cur and curw + cw > maxw:
                out.append(cur); cur, curw = [], 0.0
            if cur and cur[-1][1:] == (st, sz, rise):
                cur[-1] = (cur[-1][0] + ch, st, sz, rise)
            else:
                cur.append((ch, st, sz, rise))
            curw += cw
    if cur:
        out.append(cur)
    return out


def break_lines(runs, width, size, first_indent=0.0):
    space = text_width(" ", "R", size)
    ws = []
    for w in words_of(runs, size):
        ws.extend(split_long(w, width - first_indent))
    lines, cur, curw = [], [], 0.0
    avail = width - first_indent
    for w in ws:
        ww = word_width(w)
        if cur and curw + space + ww > avail:
            lines.append((cur, curw, avail))
            cur, curw, avail = [], 0.0, width
        curw = curw + (space if cur else 0.0) + ww
        cur.append((w, ww))
    if cur:
        lines.append((cur, curw, avail))
    return lines, space


# ---------------- page drawing -------------------------------------------------------------------
class Page:
    def __init__(self):
        self.ops = []

    def text(self, x, y, s, style, size, rise=0.0):
        for f, part in pieces(s, style):
            hexs = ""
            for c in part:
                g = f.cmap[ord(c)]
                f.used[g] = c
                hexs += "%04X" % g
            self.ops.append("BT /F%s %.2f Tf %.2f %.2f Td %.2f Ts <%s> Tj ET" % (f.key, size, x, y, rise, hexs))
            x += sum(f.width_gid(f.cmap[ord(c)]) for c in part) * size / f.upm

    def line(self, x1, y1, x2, y2, w=0.5, gray=0.0, dash=None):
        d = "[%s] 0 d " % " ".join("%.1f" % v for v in dash) if dash else "[] 0 d "
        self.ops.append("%.2f w %.3f G %s%.2f %.2f m %.2f %.2f l S" % (w, gray, d, x1, y1, x2, y2))

    def rect(self, x, y, w, h, fill=None, stroke=0.0, lw=0.6, radius=0.0):
        if radius:
            r = radius; k = 0.5523 * r
            p = ("%.2f %.2f m %.2f %.2f l %.2f %.2f %.2f %.2f %.2f %.2f c %.2f %.2f l "
                 "%.2f %.2f %.2f %.2f %.2f %.2f c %.2f %.2f l %.2f %.2f %.2f %.2f %.2f %.2f c "
                 "%.2f %.2f l %.2f %.2f %.2f %.2f %.2f %.2f c h") % (
                x + r, y, x + w - r, y, x + w - r + k, y, x + w, y + r - k, x + w, y + r,
                x + w, y + h - r, x + w, y + h - r + k, x + w - r + k, y + h, x + w - r, y + h,
                x + r, y + h, x + r - k, y + h, x, y + h - r + k, x, y + h - r,
                x, y + r, x, y + r - k, x + r - k, y, x + r, y)
        else:
            p = "%.2f %.2f %.2f %.2f re" % (x, y, w, h)
        op = "B" if fill is not None and stroke is not None else ("f" if fill is not None else "S")
        pre = ""
        if fill is not None:
            pre += "%.3f g " % fill
        if stroke is not None:
            pre += "%.3f G %.2f w [] 0 d " % (stroke, lw)
        self.ops.append(pre + p + " " + op + " 0 g")

    def circle(self, cx, cy, r, fill=1.0, stroke=0.0, lw=0.7):
        k = 0.5523 * r
        p = ("%.2f %.2f m %.2f %.2f %.2f %.2f %.2f %.2f c %.2f %.2f %.2f %.2f %.2f %.2f c "
             "%.2f %.2f %.2f %.2f %.2f %.2f c %.2f %.2f %.2f %.2f %.2f %.2f c") % (
            cx + r, cy, cx + r, cy + k, cx + k, cy + r, cx, cy + r, cx - k, cy + r, cx - r, cy + k, cx - r, cy,
            cx - r, cy - k, cx - k, cy - r, cx, cy - r, cx + k, cy - r, cx + r, cy - k, cx + r, cy)
        self.ops.append("%.3f g %.3f G %.2f w [] 0 d %s B 0 g" % (fill, stroke, lw, p))

    def ctext(self, x, y, s, style, size):
        self.text(x - text_width(s, style, size) / 2, y, s, style, size)

    def rich(self, x, y, markup, size, align="left", width=None, style="R"):
        runs = parse_inline(markup, style)
        segs = [w for w in words_of(runs, size)]
        sp = text_width(" ", "R", size)
        total = sum(word_width(w) for w in segs) + sp * (len(segs) - 1)
        if align == "center":
            x = x - total / 2
        elif align == "right":
            x = x - total
        for w in segs:
            for t, st, sz, rise in w:
                self.text(x, y, t, st, sz, rise)
                x += text_width(t, st, sz)
            x += sp
        return total


def draw_lines(page, x, y, lines, space, size, lead, justify=True, first_indent=0.0):
    for k, (ws, natw, avail) in enumerate(lines):
        last = k == len(lines) - 1
        gap = space
        if justify and not last and len(ws) > 1:
            gap = space + (avail - natw) / (len(ws) - 1)
        xx = x + (first_indent if k == 0 else 0.0)
        for w, ww in ws:
            cx = xx
            for t, st, sz, rise in w:
                page.text(cx, y, t, st, sz, rise)
                cx += text_width(t, st, sz)
            xx += ww + gap
        y -= lead
    return y


# ---------------- document model ----------------------------------------------------------------
class Doc:
    def __init__(self):
        self.pages = [Page()]
        self.y = PH - MT
        self.pending = []

    @property
    def page(self):
        return self.pages[-1]

    def newpage(self):
        self.pages.append(Page())
        self.y = PH - MT
        while self.pending:
            fn = self.pending.pop(0)
            fn()

    def place_float(self, height, fn):
        """draw now if it fits and nothing is queued, else defer to the top of the next page"""
        if self.pending or self.y - height < MB:
            self.pending.append(fn)
        else:
            fn()

    def need(self, h):
        if self.y - h < MB:
            self.newpage()

    def space(self, h):
        self.y -= h

    def para(self, markup, size=BODY, lead=LEAD, indent=0.0, width=None, justify=True, style="R",
             first_indent=0.0, after=4.0, keep=2):
        width = width or (TW - indent)
        lines, space = break_lines(parse_inline(markup, style), width, size, first_indent)
        i = 0
        while i < len(lines):
            fit = int((self.y - MB) // lead)
            rest = len(lines) - i
            if fit < min(keep, rest) or (rest > fit and rest - fit < keep and fit < rest):
                if fit < min(keep, rest):
                    self.newpage(); continue
                fit = max(min(keep, rest), fit - (keep - (rest - fit)))
            chunk = lines[i:i + fit] if rest > fit else lines[i:]
            last_chunk = i + len(chunk) == len(lines)
            y0 = self.y - size
            draw_lines(self.page, ML + indent, y0, chunk if last_chunk else chunk, space, size, lead,
                       justify=justify, first_indent=first_indent if i == 0 else 0.0)
            if not last_chunk:
                # justify the last line of a page chunk as well
                pass
            self.y -= lead * len(chunk)
            i += len(chunk)
            if i < len(lines):
                self.newpage()
        self.y -= after

    def block_height(self, markup, size, lead, width, style="R"):
        lines, _ = break_lines(parse_inline(markup, style), width, size)
        return len(lines) * lead


# ---------------- tables -------------------------------------------------------------------------
def table_height(header, rows, cols, size=8.8, lead=10.8, caption=None, pad=4.0):
    widths = [c * TW for c in cols]
    total = 0.0
    for r_i, row in enumerate([header] + rows):
        n = max(len(break_lines(parse_inline(c, "B" if r_i == 0 else "R"), w - 2 * pad, size)[0])
                for c, w in zip(row, widths))
        total += n * lead + 3.0
    if caption:
        total += len(break_lines(parse_inline(caption), TW, 9.2)[0]) * 11.2 + 4
    return total + 8


def draw_table(doc, header, rows, cols, size=8.8, lead=10.8, caption=None, align=None, pad=4.0):
    widths = [c * TW for c in cols]
    align = align or ["left"] * len(cols)

    def cell_lines(markup, w, style="R"):
        ls, sp = break_lines(parse_inline(markup, style), w - 2 * pad, size)
        return ls, sp

    laid = []
    for r_i, row in enumerate([header] + rows):
        cells = [cell_lines(c, w, "B" if r_i == 0 else "R") for c, w in zip(row, widths)]
        h = max(len(ls) for ls, _ in cells) * lead + 3.0
        laid.append((cells, h))
    cap_h = 0.0
    if caption:
        cap_lines, cap_sp = break_lines(parse_inline(caption), TW, 9.2)
        cap_h = len(cap_lines) * 11.2 + 4
    total = sum(h for _, h in laid) + cap_h + 8
    doc.need(min(total, PH - MT - MB))
    pg = doc.page
    y = doc.y - 2
    pg.line(ML, y, ML + TW, y, w=0.8)
    for r_i, (cells, h) in enumerate(laid):
        if y - h < MB:
            doc.newpage(); pg = doc.page; y = doc.y - 2
            pg.line(ML, y, ML + TW, y, w=0.8)
        x = ML
        for (ls, sp), w, al in zip(cells, widths, align):
            yy = y - size - 1.5
            for ws, natw, avail in ls:
                if al == "center":
                    xx = x + (w - natw) / 2
                elif al == "right":
                    xx = x + w - pad - natw
                else:
                    xx = x + pad
                for word, ww in ws:
                    cx = xx
                    for t, st, sz, rise in word:
                        pg.text(cx, yy, t, st, sz, rise)
                        cx += text_width(t, st, sz)
                    xx += ww + sp
                yy -= lead
            x += w
        y -= h
        if r_i == 0:
            pg.line(ML, y + 1, ML + TW, y + 1, w=0.5)
    pg.line(ML, y, ML + TW, y, w=0.8)
    y -= 4
    if caption:
        draw_lines(pg, ML, y - 9.2, cap_lines, cap_sp, 9.2, 11.2, justify=True)
        y -= cap_h
    doc.y = y - 6


# ---------------- generated content ---------------------------------------------------------------
def setstr(xs):
    return "{" + ",".join(str(x) for x in xs) + "}"


def table_vertices(F):
    header = ["<i>v</i>", "deg", "<i>N</i>[<i>v</i>]", "<i>U</i>(<i>v</i>) = <i>V</i> − <i>N</i>[<i>v</i>]"]
    rows = []
    for v in range(9):
        rows.append([str(v), str(F["degrees"][str(v)]), setstr(F["closed_nbhd"][str(v)]),
                     setstr(F["complement_nbhd"][str(v)])])
    return header, rows, [0.08, 0.08, 0.42, 0.42], ["center", "center", "left", "left"]


def table_pairs(F):
    pc = F["pair_common_complement_nbhd"]
    header = ["<i>x</i> \\ <i>y</i>"] + [str(y) for y in range(1, 9)]
    rows = []
    for x in range(8):
        row = [str(x)]
        for y in range(1, 9):
            if y <= x:
                row.append("")
            else:
                u = pc["%d%d" % (x, y)]
                row.append("".join(str(t) for t in u) if u else "<b>∅</b>")
        rows.append(row)
    return header, rows, [0.12] + [0.11] * 8, ["center"] * 9


def table_nondom(F):
    items = F["triples_class_b_nondominating"]
    cells = ["%s: <i>U</i> = %s, <i>v</i> = %d" % (setstr([int(c) for c in d["T"]]), setstr(d["U(T)"]), d["witness"])
             for d in items]
    ncol = 3
    nrow = (len(cells) + ncol - 1) // ncol
    rows = []
    for r in range(nrow):
        rows.append([cells[c * nrow + r] if c * nrow + r < len(cells) else "" for c in range(ncol)])
    header = ["<i>T</i>: <i>U</i>(<i>T</i>), witness <i>v</i>"] * ncol
    return header, rows, [1 / 3.0] * 3, ["left"] * 3


def table_irsets(F):
    header = ["<i>i</i>", "<i>W<sub>i</sub></i>", "private neighbourhoods PN(<i>v</i>, <i>W<sub>i</sub></i>)",
              "independent", "to <i>W</i><sub><i>i</i>+1</sub>"]
    sw = F["swaps_along_path"]
    rows = []
    for i, d in enumerate(F["IR_sets_path_order"]):
        pn = ";  ".join("%s: %s" % (v, setstr(d["PN"][v])) for v in sorted(d["PN"]))
        nxt = "%d→%d (edge %d%d)" % (sw[i]["out"], sw[i]["in"], min(sw[i]["out"], sw[i]["in"]),
                                     max(sw[i]["out"], sw[i]["in"])) if i < 8 else "—"
        rows.append([str(i), setstr([int(c) for c in d["D"]]), pn, "yes" if d["independent"] else "no", nxt])
    return header, rows, [0.05, 0.13, 0.43, 0.13, 0.26], ["center", "left", "left", "center", "left"]


def table_search(S):
    small, m8, agg = S["small"], S["merge8"], S["agg9"]
    header = ["order <i>n</i>", "what was evaluated", "graphs evaluated",
              "IR-graph <i>P<sub>m</sub></i> (<i>m</i> ≥ 3) or <i>C<sub>m</sub></i> (<i>m</i> ≥ 5)"]
    rows = []
    for n in range(1, 8):
        c = small["class_counts"][str(n)]
        rows.append([str(n), "all isomorphism classes", "{:,}".format(c), "none"])
    rows.append(["8", "all isomorphism classes", "{:,}".format(m8["class_count_8"]), "none"])
    cls = {c["label"]: c for c in agg["iso_classes"]}
    hits = "; ".join("%s: %d labelled, %d edges%s" % (
        "<i>P</i><sub>%s</sub>" % k[1:], cls[k]["labelled_hits"], cls[k]["edges"],
        " (class of <i>G</i>)" if cls[k]["is_class_of_G"] else "") for k in sorted(cls))
    rows.append(["9", "all 256 one-vertex extensions of each order-8 class",
                 "{:,}".format(agg["labelled_graphs_evaluated"]),
                 "%d labelled hits in %d classes: %s" % (agg["n_hits"], agg["n_iso_classes"], hits)])
    return header, rows, [0.09, 0.27, 0.15, 0.49], ["center", "left", "right", "left"]


def table_lean(F):
    header = ["source notion", "Lean (namespace IR350452)"]
    rows = [
        ["<i>w</i> ∈ PN(<i>v</i>, <i>D</i>)",
         "<tt>IsPrivateNbr G D v w := (w = v ∨ G.Adj v w) ∧ ∀ u ∈ D, u ≠ v → ¬(w = u ∨ G.Adj u w)</tt>"],
        ["<i>D</i> irredundant", "<tt>Irredundant G D := ∀ v ∈ D, ∃ w, IsPrivateNbr G D v w</tt>"],
        ["IR(<i>G</i>)", "<tt>IR G := (univ.filter (Irredundant G)).sup card</tt>, with <tt>ir_upper</tt> and <tt>ir_attained</tt>"],
        ["IR(<i>G</i>)-set", "<tt>IRSet G D := Irredundant G D ∧ D.card = IR G</tt>"],
        ["<i>D</i> ∼ <i>D</i>′ (slide)", "<tt>Swap G A B := ∃ u ∈ A, ∃ v ∈ B, G.Adj u v ∧ B = insert v (A.erase u)</tt>"],
        ["<i>G</i>(IR)", "<tt>IRGraph G : SimpleGraph {D // IsIRSet G D}</tt>, <tt>Adj := Swap</tt>; symm by <tt>swap_symm</tt>, loopless by <tt>swap_irrefl</tt>"],
        ["<i>H</i> is an IR-graph", "<tt>IsIRGraph H := ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V), Nonempty (H ≃g IRGraph G)</tt>"],
        ["the conjecture", "<tt>Conjecture := (∀ n, 3 ≤ n → ¬IsIRGraph (pathGraph n)) ∧ (∀ n, 5 ≤ n → ¬IsIRGraph (cycleGraph n))</tt>"],
        ["Theorem 1", "<tt>G9</tt> (20-edge list on <tt>Fin 9</tt>), <tt>ir_G9 : IR G9 = 3</tt>, <tt>pathIso : pathGraph 9 ≃g IRGraph G9</tt>"],
        ["Corollary 2", "<tt>conjecture_false : ¬ Conjecture</tt>; control <tt>nonvacuity : IsIRGraph (pathGraph 2)</tt>"],
    ]
    return header, rows, [0.19, 0.81], ["left", "left"]


# ---------------- figures ------------------------------------------------------------------------
FIG_H = 196.0


def figure_height(caption):
    return FIG_H + len(break_lines(parse_inline(caption), TW, 9.2)[0]) * 11.2 + 10


def figure_graph(doc, F, caption):
    H = FIG_H
    cap_lines, cap_sp = break_lines(parse_inline(caption), TW, 9.2)
    doc.need(H + len(cap_lines) * 11.2 + 10)
    pg = doc.page
    top = doc.y
    # left panel: G, vertices 0..8 clockwise; parts centred at 90, -30 and 210 degrees
    cx, cy, R = ML + 100, top - 100, 78.0
    pos = {}
    for p, ang in enumerate([90.0, -30.0, 210.0]):
        for k, d in enumerate([21.0, 0.0, -21.0]):
            v = 3 * p + k
            a = math.radians(ang + d)
            pos[v] = (cx + R * math.cos(a), cy + R * math.sin(a))
    edges = [(int(e[0]), int(e[1])) for e in F["edges"]]
    deleted = [(0, 5), (0, 8), (1, 4), (2, 3), (2, 6), (3, 7), (5, 6)]
    for a, b in deleted:
        pg.line(*pos[a], *pos[b], w=0.6, gray=0.55, dash=[2.2, 2.2])
    for a, b in edges:
        pg.line(*pos[a], *pos[b], w=0.75, gray=0.0)
    for v, (x, y) in pos.items():
        pg.circle(x, y, 7.2, fill=1.0, stroke=0.0, lw=0.8)
        pg.ctext(x, y - 3.1, str(v), "R", 9.0)
    pg.ctext(cx, top - 6, "A = {0,1,2}", "I", 8.0)
    pg.text(ML + 150, top - 192, "B = {3,4,5}", "I", 8.0)
    pg.text(ML + 2, top - 192, "C = {6,7,8}", "I", 8.0)
    # right panel: the path, as a snake of three rows
    x0 = ML + 232
    xs = [x0, x0 + 88, x0 + 176]
    ys = [top - 34, top - 100, top - 166]
    order = [(0, 0), (0, 1), (0, 2), (1, 2), (1, 1), (1, 0), (2, 0), (2, 1), (2, 2)]
    sets = [d["D"] for d in F["IR_sets_path_order"]]
    indep = [d["independent"] for d in F["IR_sets_path_order"]]
    sw = F["swaps_along_path"]
    bw, bh = 54.0, 22.0
    centers = [(xs[c] + bw / 2, ys[r]) for r, c in order]
    for i in range(8):
        (xa, ya), (xb, yb) = centers[i], centers[i + 1]
        lab = "%d→%d" % (sw[i]["out"], sw[i]["in"])
        if ya == yb:
            pg.line(xa + bw / 2, ya, xb - bw / 2 if xb > xa else xb + bw / 2, yb, w=0.9)
            pg.ctext((xa + xb) / 2, ya + 4, lab, "R", 8.0)
        else:
            pg.line(xa, ya - bh / 2, xb, yb + bh / 2, w=0.9)
            pg.text(xa + 4, (ya + yb) / 2 - 3, lab, "R", 8.0)
    for i, (x, y) in enumerate(centers):
        pg.rect(x - bw / 2, y - bh / 2, bw, bh, fill=(0.86 if indep[i] else 1.0), stroke=0.0, lw=0.8, radius=4.0)
        pg.rich(x, y - 3.2, "<i>W</i><sub>%d</sub> = {%s}" % (i, ",".join(sets[i])), 8.6, align="center")
    doc.y = top - H
    draw_lines(pg, ML, doc.y - 9.2, cap_lines, cap_sp, 9.2, 11.2, justify=True)
    doc.y -= len(cap_lines) * 11.2 + 10


# ---------------- source parser -------------------------------------------------------------------
def parse_src(path):
    blocks, lines = [], [l.rstrip("\n") for l in open(path, encoding="utf-8")]
    i = 0
    para = []

    def flush():
        if para:
            blocks.append(("para", " ".join(x.strip() for x in para)))
            para.clear()

    while i < len(lines):
        l = lines[i]
        if l.startswith("%"):
            i += 1; continue
        if not l.strip():
            flush(); i += 1; continue
        if l.startswith("@title "):
            flush(); blocks.append(("title", l[7:])); i += 1; continue
        if l.startswith("## "):
            flush(); blocks.append(("h2", l[3:])); i += 1; continue
        if l.startswith("### "):
            flush(); blocks.append(("h3", l[4:])); i += 1; continue
        if l.startswith("- "):
            flush()
            item = [l[2:]]
            i += 1
            while i < len(lines) and lines[i].startswith("  ") and lines[i].strip():
                item.append(lines[i].strip()); i += 1
            blocks.append(("item", " ".join(item))); continue
        if l.strip() in ("@status", "@abstract", "@quote", "@center", "@refs"):
            flush()
            kind = l.strip()[1:]
            body = []
            i += 1
            while lines[i].strip() != "@end":
                body.append(lines[i]); i += 1
            i += 1
            blocks.append((kind, body)); continue
        if l.startswith("@autotable ") or l.startswith("@figure "):
            flush()
            kind, name = l.split()[0][1:], l.split()[1]
            cap = None
            if i + 1 < len(lines) and lines[i + 1].startswith("@caption "):
                cap = lines[i + 1][9:]; i += 1
            blocks.append((kind, (name, cap))); i += 1; continue
        para.append(l); i += 1
    flush()
    return blocks


def paras_of(body):
    out, cur = [], []
    for l in body:
        if not l.strip():
            if cur:
                out.append(" ".join(x.strip() for x in cur)); cur = []
        else:
            cur.append(l)
    if cur:
        out.append(" ".join(x.strip() for x in cur))
    return out


# ---------------- PDF writer -------------------------------------------------------------------------
def write_pdf(pages, path, title):
    objs = []

    def add(b):
        objs.append(b); return len(objs)

    def stream(data, extra=""):
        comp = zlib.compress(data, 9)
        return b"<< /Length %d /Filter /FlateDecode%s >>\nstream\n" % (len(comp), extra.encode()) + comp + b"\nendstream"

    font_refs = {}
    for k, f in FONTS.items():
        if not f.used:
            continue
        name = PSNAMES[k]
        ff = add(stream(f.raw, " /Length1 %d" % len(f.raw)))
        flags = 32 | (64 if f.italic else 0)
        sc = 1000.0 / f.upm
        fd = add(("<< /Type /FontDescriptor /FontName /%s /Flags %d /FontBBox [%d %d %d %d] /ItalicAngle %.1f "
                  "/Ascent %d /Descent %d /CapHeight %d /StemV 80 /FontFile2 %d 0 R >>" % (
                      name, flags, *(int(v * sc) for v in f.bbox), f.italic, int(f.asc * sc), int(f.desc * sc),
                      int(f.cap * sc), ff)).encode())
        gids = sorted(f.used)
        W = " ".join("%d [%d]" % (g, round(f.width_gid(g) * sc)) for g in gids)
        cid = add(("<< /Type /Font /Subtype /CIDFontType2 /BaseFont /%s /CIDSystemInfo << /Registry (Adobe) "
                   "/Ordering (Identity) /Supplement 0 >> /FontDescriptor %d 0 R /W [%s] /DW 1000 "
                   "/CIDToGIDMap /Identity >>" % (name, fd, W)).encode())
        cmap = ["/CIDInit /ProcSet findresource begin", "12 dict begin", "begincmap",
                "/CIDSystemInfo << /Registry (Adobe) /Ordering (UCS) /Supplement 0 >> def",
                "/CMapName /Adobe-Identity-UCS def", "/CMapType 2 def",
                "1 begincodespacerange", "<0000> <FFFF>", "endcodespacerange"]
        for s in range(0, len(gids), 100):
            chunk = gids[s:s + 100]
            cmap.append("%d beginbfchar" % len(chunk))
            for g in chunk:
                u = f.used[g].encode("utf-16-be").hex().upper()
                cmap.append("<%04X> <%s>" % (g, u))
            cmap.append("endbfchar")
        cmap += ["endcmap", "CMapName currentdict /CMap defineresource pop", "end", "end"]
        tu = add(stream("\n".join(cmap).encode()))
        font_refs[k] = add(("<< /Type /Font /Subtype /Type0 /BaseFont /%s /Encoding /Identity-H "
                            "/DescendantFonts [%d 0 R] /ToUnicode %d 0 R >>" % (name, cid, tu)).encode())
    fontdict = " ".join("/F%s %d 0 R" % (k, r) for k, r in font_refs.items())
    pages_id = len(objs) + 1 + 2 * len(pages)
    page_ids = []
    for pg in pages:
        c = add(stream("\n".join(pg.ops).encode()))
        page_ids.append(add(("<< /Type /Page /Parent %d 0 R /MediaBox [0 0 %d %d] /Resources << /Font << %s >> >> "
                             "/Contents %d 0 R >>" % (pages_id, PW, PH, fontdict, c)).encode()))
    assert add(("<< /Type /Pages /Kids [%s] /Count %d >>" % (" ".join("%d 0 R" % p for p in page_ids),
                                                            len(page_ids))).encode()) == pages_id
    info = add(("<< /Title <%s> /Producer (irpath-manuscript-r1 scripts/build_pdf.py) >>" %
                ("FEFF" + title.encode("utf-16-be").hex().upper())).encode())
    cat = add(("<< /Type /Catalog /Pages %d 0 R >>" % pages_id).encode())
    out = bytearray(b"%PDF-1.6\n%\xe2\xe3\xcf\xd3\n")
    offs = []
    for i, b in enumerate(objs, 1):
        offs.append(len(out))
        out += b"%d 0 obj\n" % i + b + b"\nendobj\n"
    xref = len(out)
    out += b"xref\n0 %d\n0000000000 65535 f \n" % (len(objs) + 1)
    for o in offs:
        out += b"%010d 00000 n \n" % o
    out += b"trailer\n<< /Size %d /Root %d 0 R /Info %d 0 R >>\nstartxref\n%d\n%%%%EOF\n" % (len(objs) + 1, cat, info, xref)
    with open(path, "xb") as fh:
        fh.write(out)
    return len(out)


# ---------------- main ---------------------------------------------------------------------------------
def main():
    src, facts, sdir, outdir = sys.argv[1:5]
    F = json.load(open(facts))
    S = {k: json.load(open(os.path.join(sdir, k + ".json"))) for k in ["small", "merge8", "agg9"]}
    tables = {"vertices": table_vertices(F), "pairs": table_pairs(F), "nondominating": table_nondom(F),
              "irsets": table_irsets(F), "search": table_search(S), "lean": table_lean(F)}
    blocks = parse_src(src)
    doc = Doc()
    resolved = []
    title = ""
    for kind, val in blocks:
        if kind == "title":
            title = plain(val)
            doc.space(8)
            lines, sp = break_lines(parse_inline(val, "B"), TW - 40, 15.5)
            for ws, natw, avail in lines:
                x = ML + (TW - natw) / 2
                for w, ww in ws:
                    cx = x
                    for t, st, sz, rise in w:
                        doc.page.text(cx, doc.y - 15.5, t, st, sz, rise); cx += text_width(t, st, sz)
                    x += ww + sp
                doc.y -= 19.5
            doc.space(4)
            resolved.append("# " + title)
        elif kind == "status":
            txt = " ".join(x.strip() for x in val)
            h = doc.block_height(txt, 8.8, 10.8, TW - 24)
            doc.page.rect(ML + 4, doc.y - h - 10, TW - 8, h + 8, fill=0.94, stroke=0.3, lw=0.6)
            doc.y -= 6
            doc.para(txt, size=8.8, lead=10.8, indent=12, width=TW - 24, after=8)
            resolved.append(plain(txt))
        elif kind == "abstract":
            txt = " ".join(x.strip() for x in val)
            doc.para("<b>Abstract.</b> " + txt, size=9.5, lead=12.0, indent=18, width=TW - 36, after=8)
            resolved.append("Abstract. " + plain(txt))
        elif kind == "h2":
            doc.need(17 + 3 * LEAD)
            doc.space(5)
            doc.page.text(ML, doc.y - 11.5, plain(val).replace("  ", "   "), "B", 11.5)
            doc.y -= 18
            resolved.append("## " + plain(val))
        elif kind == "h3":
            doc.need(14 + 2 * LEAD)
            doc.page.text(ML, doc.y - BODY, plain(val), "B", BODY)
            doc.y -= 15
            resolved.append("### " + plain(val))
        elif kind == "para":
            doc.para(val)
            resolved.append(plain(val))
        elif kind == "item":
            m = re.match(r"\((\w)\)\s*(.*)", val)
            lab, body = ("(%s)" % m.group(1), m.group(2)) if m else ("•", val)
            doc.need(2 * LEAD)
            doc.page.text(ML + 10, doc.y - BODY, lab, "R", BODY)
            doc.para(body, indent=30, width=TW - 30, after=2)
            resolved.append(lab + " " + plain(body))
        elif kind == "quote":
            for q in paras_of(val):
                doc.para(q, size=9.6, lead=12.0, indent=22, width=TW - 44, after=3)
                resolved.append("> " + plain(q))
            doc.space(3)
        elif kind == "center":
            for l in val:
                doc.need(LEAD)
                doc.page.rich(ML + TW / 2, doc.y - BODY, l.strip(), BODY, align="center")
                doc.y -= LEAD
                resolved.append(plain(l.strip()))
            doc.space(4)
        elif kind == "autotable":
            name, cap = val
            header, rows, cols, al = tables[name]
            size = 8.4 if name in ("lean", "search", "irsets") else 8.8
            h = table_height(header, rows, cols, size=size, lead=size + 2.0, caption=cap)
            doc.place_float(h, (lambda a=(header, rows, cols, size, cap, al):
                                draw_table(doc, a[0], a[1], a[2], size=a[3], lead=a[3] + 2.0,
                                           caption=a[4], align=a[5])))
            resolved.append("[%s]" % plain(cap or name))
            resolved.append(" | ".join(plain(h) for h in header))
            for r in rows:
                resolved.append(" | ".join(plain(c) for c in r))
        elif kind == "figure":
            name, cap = val
            doc.place_float(figure_height(cap), (lambda c=cap: figure_graph(doc, F, c)))
            resolved.append("[%s]" % plain(cap))
        elif kind == "refs":
            doc.need(17 + 3 * LEAD)
            doc.space(5)
            doc.page.text(ML, doc.y - 11.5, "References", "B", 11.5)
            doc.y -= 18
            resolved.append("## References")
            for l in val:
                m = re.match(r"\[([^\]]+)\]\s*(.*)", l.strip())
                doc.need(2 * 11.0)
                doc.page.text(ML, doc.y - 8.8, "[%s]" % m.group(1), "B", 8.8)
                doc.para(m.group(2), size=8.8, lead=11.0, indent=58, width=TW - 58, after=2.5, justify=False)
                resolved.append("[%s] %s" % (m.group(1), plain(m.group(2))))
    if doc.pending:
        doc.newpage()
    n = len(doc.pages)
    for k, pg in enumerate(doc.pages, 1):
        pg.ops.insert(0, "")
        hdr = "DRAFT · MathDB 350452 · not peer reviewed · prepared with AI assistance"
        pg.ctext(PW / 2, PH - 34, hdr, "I", 7.8)
        pg.line(ML, PH - 40, PW - MR, PH - 40, w=0.3, gray=0.4)
        pg.ctext(PW / 2, 32, "page %d of %d" % (k, n), "R", 8.0)
    os.makedirs(outdir, exist_ok=True)
    size = write_pdf(doc.pages, os.path.join(outdir, "manuscript.pdf"), title)
    with open(os.path.join(outdir, "manuscript-resolved.txt"), "x", encoding="utf-8") as fh:
        fh.write("\n\n".join(resolved) + "\n")
    print(json.dumps({"pages": n, "bytes": size, "fonts": {k: len(f.used) for k, f in FONTS.items()}}))


if __name__ == "__main__":
    main()
