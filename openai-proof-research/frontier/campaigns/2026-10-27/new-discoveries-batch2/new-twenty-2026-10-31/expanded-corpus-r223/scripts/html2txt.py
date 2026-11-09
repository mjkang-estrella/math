import sys, re, html, pathlib
# usage: html2txt.py IN1.body OUT1.txt [IN2 OUT2 ...]; replaces <math alttext="..."> by $...$ and strips tags
a = sys.argv[1:]
for inp, outp in zip(a[0::2], a[1::2]):
    src = pathlib.Path(inp).read_text(errors='replace')
    src = re.sub(r'<head>.*?</head>', '', src, flags=re.S)
    src = re.sub(r'<(script|style)[^>]*>.*?</\1>', '', src, flags=re.S)
    src = re.sub(r'<math[^>]*?alttext="([^"]*)"[^>]*>.*?</math>', lambda m: ' $' + m.group(1) + '$ ', src, flags=re.S)
    src = re.sub(r'<(br|p|div|h\d|li|tr|section|figcaption)[^>]*>', '\n', src)
    t = re.sub(r'<[^>]+>', '', src)
    t = html.unescape(t)
    t = re.sub(r'[ \t]+', ' ', t)
    t = re.sub(r'\n\s*\n+', '\n\n', t)
    out = pathlib.Path(outp)
    if out.exists():
        print('exists, skipped: ' + str(out))
        continue
    out.write_text(t)
    print(outp, len(t))
