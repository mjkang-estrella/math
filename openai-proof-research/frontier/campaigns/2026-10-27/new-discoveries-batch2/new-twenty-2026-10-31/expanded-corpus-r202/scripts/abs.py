import sys,re,html,pathlib
for f in sys.argv[1:]:
    s=pathlib.Path(f).read_text(errors='replace')
    t=re.search(r'<h1 class="title mathjax">(.*?)</h1>',s,re.S)
    a=re.search(r'<blockquote class="abstract mathjax">(.*?)</blockquote>',s,re.S)
    au=re.search(r'<div class="authors">(.*?)</div>',s,re.S)
    sub=re.search(r'<div class="submission-history">(.*?)</div>',s,re.S)
    jr=re.search(r'<td class="tablecell jref">(.*?)</td>',s,re.S)
    cm=re.search(r'<td class="tablecell comments mathjax">(.*?)</td>',s,re.S)
    clean=lambda x: re.sub(r'\s+',' ',html.unescape(re.sub('<[^>]+>','',x.group(1)))).strip() if x else ''
    print('=====',f); print('T:',clean(t)); print('AU:',clean(au)); print('J:',clean(jr)); print('C:',clean(cm)); print('H:',clean(sub)[-400:]); print('A:',clean(a)[:1500])
