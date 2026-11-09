import sys,re,html,glob,os
for f in sorted(glob.glob(os.path.join(sys.argv[1],'*.html'))):
    t=open(f,encoding='utf-8',errors='replace').read()
    title=re.search(r'<meta name="citation_title" content="([^"]*)"',t)
    auth=re.findall(r'<meta name="citation_author" content="([^"]*)"',t)
    vers=re.findall(r'<strong>\[(v\d+)\]</strong>\s*([^<]*)',t)
    jref=re.search(r'<td class="tablecell jref">(.*?)</td>',t,re.S)
    com=re.search(r'<td class="tablecell comments[^"]*">(.*?)</td>',t,re.S)
    print(os.path.basename(f),'|',html.unescape(title.group(1)) if title else '?')
    print('   authors:','; '.join(auth))
    print('   versions:',[(v,d.strip()[:40]) for v,d in vers])
    if jref: print('   jref:',re.sub('<[^>]+>','',jref.group(1)).strip())
    if com: print('   comments:',re.sub('<[^>]+>','',com.group(1)).strip()[:200])
