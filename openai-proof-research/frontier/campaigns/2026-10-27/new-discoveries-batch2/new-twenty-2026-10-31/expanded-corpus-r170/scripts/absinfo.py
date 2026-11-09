import re,sys,html,pathlib
for f in sorted(pathlib.Path(sys.argv[1]).glob('*-abs.html')):
    t=f.read_text(errors='replace')
    title=re.search(r'<h1 class="title mathjax">.*?</span>(.*?)</h1>',t,re.S)
    auth=re.findall(r'<a href="https://arxiv.org/search/\?searchtype=author[^"]*"[^>]*>(.*?)</a>',t)
    vers=re.findall(r'<strong>\[v(\d+)\]</strong>\s*(.*?)\s*\(',t,re.S)
    jr=re.search(r'<td class="tablecell jref">(.*?)</td>',t,re.S)
    cm=re.search(r'<td class="tablecell comments mathjax">(.*?)</td>',t,re.S)
    ab=re.search(r'<blockquote class="abstract mathjax">.*?</span>(.*?)</blockquote>',t,re.S)
    cl=lambda s: re.sub(r'\s+',' ',html.unescape(re.sub('<[^>]+>','',s))).strip() if s else ''
    print('##',f.name.split('-')[0],cl(title.group(1) if title else ''))
    print('  authors:',', '.join(cl(a) for a in auth[:8]))
    print('  versions:',[(v,cl(d)) for v,d in vers])
    print('  jref:',cl(jr.group(1) if jr else ''),'| comments:',cl(cm.group(1) if cm else '')[:150])
    print('  abs:',cl(ab.group(1) if ab else '')[:700])
