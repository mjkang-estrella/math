import pathlib,re,json,html
D=pathlib.Path(__file__).resolve().parents[1]
out={}
for p in sorted((D/'sources').glob('*.abs.html')):
    t=p.read_text(errors='replace')
    a=p.name[:-9]
    title=re.search(r'<meta name="citation_title" content="([^"]*)"',t)
    auth=re.findall(r'<meta name="citation_author" content="([^"]*)"',t)
    vers=re.findall(r'<strong><a href="/abs/[^"]*v(\d+)"[^>]*>\[v\d+\]</a></strong>\s*([^<]*)|<strong>\[v(\d+)\]</strong>\s*([^<]*)',t)
    vv=[(x[0] or x[2], html.unescape((x[1] or x[3]).strip())) for x in vers]
    com=re.search(r'<td class="tablecell comments[^"]*">(.*?)</td>',t,re.S)
    jref=re.search(r'<td class="tablecell jref">(.*?)</td>',t,re.S)
    out[a]={'title':html.unescape(title.group(1)) if title else None,'authors':auth,'versions':vv,'comments':re.sub('<[^>]+>','',com.group(1)).strip() if com else None,'jref':re.sub('<[^>]+>','',jref.group(1)).strip() if jref else None}
(D/'outputs/arxiv-versions.json').write_text(json.dumps(out,indent=1)+'\n')
for a,o in out.items(): print(a,o['title'],'|',', '.join(o['authors']),'|',o['versions'],'|',o['comments'],'|',o['jref'])
