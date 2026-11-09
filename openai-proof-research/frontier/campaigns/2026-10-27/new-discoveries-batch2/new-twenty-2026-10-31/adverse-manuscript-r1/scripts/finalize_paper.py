from pathlib import Path
R=Path(__file__).resolve().parents[1];p=R/'paper/manuscript.py';s=p.read_text().replace('1, 3/4+1/4, 1/4+3/4, 1/4+1/2+1/4, 3/4+1/4, and 1/4+1/4+1/2','1, 3/4+1/4, 1/4+1/2+1/4, 1/4+1/4+1/2, 3/4+1/4, and 3/4+1/4').replace('Incidence Gram identity over ℚ and ℝ','Incidence Gram identity over rationals and reals');p.write_text(s)
p=R/'REPRODUCE.md';s=p.read_text().replace('ReportLab and DejaVu fonts','ReportLab, Liberation fonts and Symbola');p.write_text(s)
