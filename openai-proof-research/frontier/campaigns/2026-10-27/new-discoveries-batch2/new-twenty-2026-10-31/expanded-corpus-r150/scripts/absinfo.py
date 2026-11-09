import re,sys,pathlib,html,json
D=pathlib.Path(__file__).resolve().parents[1]
out={}
for p in sorted((D/'sources').glob('abs-*.body')):
    t=p.read_text(errors='replace')
    title=re.search(r'<h1 class="title mathjax"><span class="descriptor">Title:</span>(.*?)</h1>',t,re.S)
    auth=re.findall(r'<a href="https://arxiv.org/a/[^"]*"[^>]*>(.*?)</a>|<a href="/search/\?searchtype=author[^"]*"[^>]*>(.*?)</a>',t)
    vers=re.findall(r'<strong>\[(v\d+)\]</strong>\s*(.*?)\s*<',t)
    com=re.search(r'<td class="tablecell comments mathjax">(.*?)</td>',t,re.S)
    jref=re.search(r'<td class="tablecell jref">(.*?)</td>',t,re.S)
    doi=re.search(r'data-doi="([^"]*)"',t)
    a=[html.unescape(x or y) for x,y in auth]
    rec={'title':html.unescape(re.sub(r'\s+',' ',title.group(1)).strip()) if title else None,'authors':a,'versions':vers,'comments':html.unescape(re.sub('<[^>]+>','',com.group(1)).strip()) if com else None,'journal_ref':html.unescape(jref.group(1).strip()) if jref else None}
    out[p.stem[4:]]=rec
    print(p.stem[4:],rec['title'],'|',', '.join(a),'|',[v[0]+' '+v[1][:16] for v in vers],'|',rec['comments'],'|',rec['journal_ref'])
(D/'outputs/arxiv-abs-info.json').write_text(json.dumps(out,indent=1)+'\n')
