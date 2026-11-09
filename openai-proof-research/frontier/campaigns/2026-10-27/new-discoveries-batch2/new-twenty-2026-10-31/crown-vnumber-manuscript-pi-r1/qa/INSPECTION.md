# Per-page visual inspection record

Renderer: `pdftoppm -png -r 100` (poppler-utils). Every page of the released PDF was
rendered and visually inspected. Iterations:

1. Build 1 (21:03 UTC): subscript fragments dropped ~0.5em plus an extra offset and
   read as belonging to the next line (reportlab 4.4.9 `<sub rise="...">` semantics:
   effective drop = fontSize + rise for absolute values). Fix: calibrated percentage
   rises (sub 20% drop, sup 38% raise, size 72%) in `mm()`; verified on isolated
   probes, then rebuilt.
2. Build 2: all pages re-rendered; full read-through of pages 1-10. Text fixes:
   Remark 2.5 wording (distinct deleted sets), gap notation 3...4 -> 3-en-dash 4.
3. Build 3: reference [9] pulled onto the references page by tightening bib leading
   (13.2 -> 12.4) and spaceAfter (3.5 -> 2.6); page count 10 -> 9. Re-render; pages
   1-9 re-inspected, no remaining layout or glyph defects:

- p1 title block, DRAFT status box, abstract, Sec 1 + Thm 1.1 display (1): OK
- p2 Notation 2.1, Defs 2.2/2.3, Thm 2.4 display (2), proof: OK
- p3 Rem 2.5/2.6, Sec 3 Lem 3.1 + proof, Rem 3.2, display (3), Sec 4 head: OK
- p4 Lems 4.1/4.2, Rem 4.3, Sec 5 Prop 5.1 start: OK
- p5 5.1 end, Prop 5.2, Rem 5.3, Sec 6 Prop 6.1, Cor 6.2: OK
- p6 Sec 7 Props 7.1/7.2, Thm 7.3; Sec 8 Constr 8.1, 8.2 start: OK
- p7 Constr 8.3 (incl. phi(f) display), 8.4 (incl. evaluation = -1), Sec 9 head: OK
- p8 Thm 9.1, Cor 9.2 + display, Rem 9.3, Sec 10: OK
- p9 Sec 11, References [1]-[9]: OK

No overfull boxes, no missing glyphs (Liberation Serif body; Symbola fallback for
the set-membership/union/empty-set/quadratic extender glyphs), no widow/orphan
defects observed.
