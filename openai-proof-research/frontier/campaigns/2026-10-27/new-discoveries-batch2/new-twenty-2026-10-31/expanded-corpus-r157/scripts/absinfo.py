import sys,re,html,pathlib
for f in sorted(pathlib.Path(sys.argv[1]).glob('*.html')):
    s=f.read_text(errors='replace')
    vers=re.findall(r'<strong>\[(v\d+)\]</strong>\s*([^<]*?)\(', s)
    ab=re.search(r'<blockquote class="abstract[^"]*">(.*?)</blockquote>', s, re.S)
    ab=html.unescape(re.sub('<[^>]+>','',ab.group(1))).strip().replace('\n',' ') if ab else ''
    jr=re.search(r'<td class="tablecell jref">(.*?)</td>', s, re.S)
    cm=re.search(r'<td class="tablecell comments[^"]*">(.*?)</td>', s, re.S)
    print('==',f.stem,[(v,d.strip()) for v,d in vers],'| JREF:',html.unescape(re.sub('<[^>]+>','',jr.group(1))).strip() if jr else '-','| COMM:',html.unescape(re.sub('<[^>]+>','',cm.group(1))).strip() if cm else '-')
    print(ab[:int(sys.argv[2])])
