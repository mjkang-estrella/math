from pathlib import Path
r=Path(__file__).resolve().parent
(r/"paper.tex").write_bytes((r/"paper-template.tex").read_bytes())
