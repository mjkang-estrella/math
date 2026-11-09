from pathlib import Path
p=Path(__file__).resolve().parents[1]/'scripts/render.py';s=p.read_text();s=s.replace("for block in page.strip().split('\\n\\n'):","for block in re.split(r'\\n\\n|(?m)(?<=\\n)(?=[^#\\n])', page.strip()) if False else page.strip().split('\\n\\n'):") if False else s
s=s.replace("for block in page.strip().split('\\n\\n'):","for block in re.split(r'\\n\\n|(?m:(?<=\\n)(?=[^#>\\n]))', page.strip()):")
# Only headings need splitting from immediately following paragraph. Simpler preprocessing.
s=s.replace("for block in re.split(r'\\n\\n|(?m:(?<=\\n)(?=[^#>\\n]))', page.strip()):","for block in re.sub(r'(?m)^(#{1,2} [^\\n]+)\\n(?!\\n)', r'\\1\\n\\n',page.strip()).split('\\n\\n'):")
p.write_text(s)
