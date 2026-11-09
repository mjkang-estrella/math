import pathlib, re, sys, html
# Usage: textify.py LANE_DIR  -> sources/*.html (non-abs) to sources/text/*.txt, using MathML alttext for math
D = pathlib.Path(sys.argv[1]).resolve()
T = D / 'sources' / 'text'
T.mkdir(exist_ok=True)
for p in sorted((D / 'sources').glob('*.html')):
    if p.name.endswith('-abs.html'):
        continue
    out = T / (p.stem + '.txt')
    if out.exists():
        continue
    s = p.read_text(errors='replace')
    s = re.sub(r'<script.*?</script>|<style.*?</style>', ' ', s, flags=re.S)
    s = re.sub(r'<math[^>]*alttext="([^"]*)"[^>]*>.*?</math>', lambda m: ' $' + m.group(1) + '$ ', s, flags=re.S)
    s = re.sub(r'<(p|div|h[1-6]|li|tr|br)[^>]*>', '\n', s)
    s = re.sub(r'<[^>]+>', '', s)
    s = html.unescape(s)
    s = re.sub(r'[ \t]+', ' ', s)
    s = re.sub(r'\n\s*\n+', '\n', s)
    out.write_text(s)
    print(p.name, len(s))
