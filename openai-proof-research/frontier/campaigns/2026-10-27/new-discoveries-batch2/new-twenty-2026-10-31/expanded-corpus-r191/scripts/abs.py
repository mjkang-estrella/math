import sys,re,html
for p in sys.argv[1:]:
    t=open(p,errors='replace').read()
    m=re.search(r'<meta name="citation_title" content="([^"]*)"',t)
    a=re.findall(r'<meta name="citation_author" content="([^"]*)"',t)
    ab=re.search(r'<blockquote class="abstract[^>]*>(.*?)</blockquote>',t,re.S)
    sub=re.search(r'<div class="submission-history">(.*?)</div>',t,re.S)
    cm=re.search(r'<td class="tablecell comments[^>]*>(.*?)</td>',t,re.S)
    jr=re.search(r'<td class="tablecell jref[^>]*>(.*?)</td>',t,re.S)
    f=lambda s: re.sub(r'\s+',' ',html.unescape(re.sub('<[^>]+>',' ',s))).strip()
    print('==',p); print('TITLE',m and m.group(1)); print('AUTH',a)
    if ab: print('ABS',f(ab.group(1))[:2500])
    if sub: print('HIST',f(sub.group(1))[:800])
    if cm: print('COMMENTS',f(cm.group(1)))
    if jr: print('JREF',f(jr.group(1)))
    if not ab:
        body=f(re.sub(r'<script.*?</script>|<style.*?</style>','',t,flags=re.S))
        k=body.lower().find('abstract'); print('TEXT',body[max(0,k-1200):k+2500])
