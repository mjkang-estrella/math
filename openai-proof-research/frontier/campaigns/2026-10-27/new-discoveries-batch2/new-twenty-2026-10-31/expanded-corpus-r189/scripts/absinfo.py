import sys,re,html,pathlib
for p in sys.argv[1:]:
    t=pathlib.Path(p).read_text(errors='replace')
    g=lambda pat: html.unescape(re.sub(r'<[^>]+>','',(re.search(pat,t,re.S) or [None,''])[1])).strip()
    title=g(r'<meta name="citation_title" content="([^"]*)"')
    auth=re.findall(r'<meta name="citation_author" content="([^"]*)"',t)
    vers=re.findall(r'<strong>\[(v\d+)\]</strong>\s*([^<]*)',t)
    jref=g(r'<td class="tablecell jref">(.*?)</td>')
    doi=g(r'<td class="tablecell doi">(.*?)</td>')
    com=g(r'<td class="tablecell comments[^"]*">(.*?)</td>')
    ab=g(r'<meta name="citation_abstract" content="([^"]*)"') or g(r'<blockquote class="abstract[^"]*">(.*?)</blockquote>')
    print('##',pathlib.Path(p).name,'|',title,'|',';'.join(auth))
    print('  versions:',[(v,d.strip()[:40]) for v,d in vers]); print('  jref:',jref,'| doi:',doi,'| comments:',com[:150])
    print('  abstract:',' '.join(ab.split())[:700])
