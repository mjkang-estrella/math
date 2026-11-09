import pathlib,re,json,html,sys
D=pathlib.Path(__file__).resolve().parents[1]
out={}
for p in sorted((D/'sources/abs').glob('*.abs.html')):
 s=p.read_text(errors='replace'); a=p.name[:-9]
 title=re.search(r'<h1 class="title mathjax">.*?</span>(.*?)</h1>',s,re.S)
 auth=re.findall(r'<a href="https://arxiv.org/search/\?searchtype=author[^"]*"[^>]*>(.*?)</a>',s)
 vers=re.findall(r'<strong>\[(v\d+)\]</strong>\s*(.*?)\s*\(',s,re.S)
 jref=re.search(r'<td class="tablecell jref">(.*?)</td>',s,re.S)
 comm=re.search(r'<td class="tablecell comments mathjax">(.*?)</td>',s,re.S)
 absr=re.search(r'<blockquote class="abstract mathjax">\s*<span class="descriptor">Abstract:</span>(.*?)</blockquote>',s,re.S)
 clean=lambda t: re.sub(r'\s+',' ',html.unescape(re.sub('<[^>]+>','',t))).strip() if t else None
 out[a]=dict(title=clean(title.group(1)) if title else None,authors=[clean(x) for x in auth],versions=[(v,clean(d)) for v,d in vers],journal_ref=clean(jref.group(1)) if jref else None,comments=clean(comm.group(1)) if comm else None,abstract=clean(absr.group(1)) if absr else None)
(D/'outputs/arxiv-abs-info.json').write_text(json.dumps(out,indent=1,ensure_ascii=False)+'\n')
for a,o in out.items(): print(a,'|',o['title'],'|',', '.join(o['authors']),'|',o['versions'],'|J:',o['journal_ref'],'|C:',o['comments'])
