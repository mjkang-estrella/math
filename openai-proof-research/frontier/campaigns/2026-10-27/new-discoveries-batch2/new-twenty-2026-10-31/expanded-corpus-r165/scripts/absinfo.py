import re,sys,html,glob,os
for f in sorted(glob.glob(os.path.join(sys.argv[1],'*-abs.html'))):
    t=open(f,encoding='utf-8',errors='replace').read()
    title=re.search(r'<h1 class="title mathjax">.*?</span>(.*?)</h1>',t,re.S)
    au=re.search(r'<div class="authors">(.*?)</div>',t,re.S)
    vers=re.findall(r'<strong>\[(v\d+)\]</strong>\s*(.*?)\s*\(',t,re.S)
    ab=re.search(r'<blockquote class="abstract mathjax">(.*?)</blockquote>',t,re.S)
    jr=re.search(r'<td class="tablecell jref">(.*?)</td>',t,re.S)
    cm=re.search(r'<td class="tablecell comments mathjax">(.*?)</td>',t,re.S)
    cl=lambda s: re.sub(r'\s+',' ',html.unescape(re.sub('<[^>]+>','',s))).strip() if s else ''
    print('##',os.path.basename(f)); print(' T:',cl(title.group(1) if title else '')); print(' A:',cl(au.group(1) if au else '')[:200])
    print(' V:',[(v,re.sub(r'\s+',' ',d)) for v,d in vers]); print(' J:',cl(jr.group(1) if jr else ''),'| C:',cl(cm.group(1) if cm else ''))
    print(' AB:',cl(ab.group(1) if ab else '')[:900])
