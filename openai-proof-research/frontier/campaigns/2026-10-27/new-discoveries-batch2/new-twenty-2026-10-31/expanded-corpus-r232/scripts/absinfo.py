import pathlib, re, json, sys, html
# Usage: absinfo.py LANE_DIR  -> versions, title, authors, abstract, journal ref for each abs page
D = pathlib.Path(sys.argv[1]).resolve()
out = {}
for p in sorted((D / 'sources').glob('*-abs.html')):
    s = p.read_text(errors='replace')
    aid = p.name[:-9]
    t = re.search(r'<h1 class="title mathjax">.*?</span>(.*?)</h1>', s, re.S)
    au = re.findall(r'<a href="https://arxiv.org/search/\?searchtype=author[^"]*"[^>]*>(.*?)</a>', s)
    ab = re.search(r'<blockquote class="abstract mathjax">.*?</span>(.*?)</blockquote>', s, re.S)
    vs = re.findall(r'<strong>\[(v\d+)\]</strong>\s*(.*?)\s*\(', s, re.S)
    jr = re.search(r'<td class="tablecell jref">(.*?)</td>', s, re.S)
    cm = re.search(r'<td class="tablecell comments mathjax">(.*?)</td>', s, re.S)
    clean = lambda z: html.unescape(re.sub(r'<[^>]+>', '', z)).strip() if z else None
    out[aid] = {'title': clean(t.group(1)) if t else None, 'authors': [clean(a) for a in au],
                'versions': [(v, clean(d)) for v, d in vs], 'journal_ref': clean(jr.group(1)) if jr else None,
                'comments': clean(cm.group(1)) if cm else None,
                'abstract': ' '.join(clean(ab.group(1)).split()) if ab else None}
(D / 'outputs/versions.json').write_text(json.dumps(out, indent=2, ensure_ascii=False) + '\n')
for k, v in out.items():
    print(k, '|', v['title'], '|', '; '.join(v['authors']), '|', v['versions'], '|', v['journal_ref'], '|', v['comments'])
    print('   ', v['abstract'][:900] if v['abstract'] else None)
