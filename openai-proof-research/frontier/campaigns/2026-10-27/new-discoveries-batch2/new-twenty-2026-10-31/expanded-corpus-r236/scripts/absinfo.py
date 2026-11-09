"""Summarize sources/*-abs.html: title, authors, versions, comments, journal ref, abstract (first 700 chars).
Usage: absinfo.py LANE_DIR OUT_JSON"""
import sys, pathlib, re, html, json
D = pathlib.Path(sys.argv[1]).resolve()
out = {}
for p in sorted((D / 'sources').glob('*-abs.html')):
    s = p.read_text(errors='replace')
    g = lambda pat: (lambda m: html.unescape(re.sub(r'<[^>]+>', '', m.group(1))).strip() if m else None)(re.search(pat, s, re.S))
    title = g(r'<h1 class="title mathjax">(.*?)</h1>')
    authors = g(r'<div class="authors">(.*?)</div>')
    abstract = g(r'<blockquote class="abstract mathjax">(.*?)</blockquote>')
    comments = g(r'<td class="tablecell comments mathjax">(.*?)</td>')
    jref = g(r'<td class="tablecell jref">(.*?)</td>')
    doi = g(r'<td class="tablecell doi">(.*?)</td>')
    sh = re.search(r'<div class="submission-history">(.*?)</div>', s, re.S)
    vers = [re.sub(r'\s+', ' ', html.unescape(re.sub(r'<[^>]+>', '', a + ' ' + b))).strip()
            for a, b in re.findall(r'<strong>(.*?)</strong>(.*?)<br/>', sh.group(1), re.S)] if sh else []
    out[p.stem.replace('-abs', '')] = dict(title=title, authors=authors, versions=vers, comments=comments, jref=jref, doi=doi,
                                          abstract=(abstract or '')[:900])
pathlib.Path(sys.argv[2]).write_text(json.dumps(out, indent=1, ensure_ascii=False) + '\n')
for k, v in out.items():
    print('##', k, '|', v['title'], '|', v['authors'])
    print('   versions:', ' ; '.join(x.replace('\n', ' ')[:60] for x in v['versions']))
    print('   comments:', v['comments'], '| jref:', v['jref'], '| doi:', v['doi'])
    print('   ', re.sub(r'\s+', ' ', v['abstract'])[:600])
