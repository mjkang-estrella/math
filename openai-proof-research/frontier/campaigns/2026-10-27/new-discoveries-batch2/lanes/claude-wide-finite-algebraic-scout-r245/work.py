"""Guarded lane tool: retrieval with freeze, extraction, history screening.

Run only as:
  OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 \
  python3 <helper_guard.py> python3 -I work.py <cmd> ...
Commands:
  query <arxiv-api-search> <name>      arXiv API search, frozen XML + listing
  get <name> <url>                      fetch one URL into primary/ + frozen/
  batch <arxiv-id>...                   fetch arXiv PDFs (max 3 concurrent)
  extract <frozen-name>...              pdftotext -layout, source hash checked
  read <frozen-txt> [words...]          print windows around question words
  history <term>...                     screen lane reports/ledger/NEXT for terms
  seen                                  collect every arXiv id cited in campaign
"""
import pathlib, sys, json, hashlib, urllib.request, urllib.parse, datetime, subprocess, re, concurrent.futures

L = pathlib.Path(__file__).resolve().parent
BATCH = L.parent.parent
CAMPAIGNS = BATCH.parent.parent
# Routes that were denied in earlier lanes; never retried here.
DENIED = ('api.github.com', 'raw.githubusercontent.com', 'codeload.github.com',
          'sciencedirect.com', 'google.com/sorry', '.diff', '.patch')


def h(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def fetch(pair):
    name, url = pair
    row = {'name': name, 'url': url, 'utc': now()}
    if any(d in url for d in DENIED):
        row['error'] = 'refused locally: denied route'
    else:
        p = L / 'primary' / name
        try:
            req = urllib.request.Request(url, headers={'User-Agent': 'MathematicalResearch/1.0 (bounded scouting)'})
            with urllib.request.urlopen(req, timeout=25) as r:
                data = r.read(15000000)
                row.update(status=r.status, final_url=r.url)
            p.write_bytes(data)
            row.update(sha256=h(p), bytes=len(data))
            q = L / 'frozen' / name
            q.write_bytes(data)
            assert h(q) == h(p) == hashlib.sha256(data).hexdigest()
            row['copy'] = str(q.relative_to(L))
        except Exception as e:  # preserve failures, including 403/429
            row['error'] = repr(e)[:300]
    with (L / 'http.jsonl').open('a') as f:
        f.write(json.dumps(row) + '\n')
    return row


def entries(xmlpath):
    import xml.etree.ElementTree as E
    ns = {'a': 'http://www.w3.org/2005/Atom'}
    root = E.parse(xmlpath)
    out = []
    for x in root.findall('a:entry', ns):
        cats = [c.get('term') for c in x.findall('a:category', ns)]
        out.append((x.findtext('a:id', namespaces=ns).split('/abs/')[-1],
                    ' '.join(x.findtext('a:title', namespaces=ns).split()),
                    x.findtext('a:published', namespaces=ns)[:10], ','.join(cats[:3])))
    return out


def seen_ids():
    p = L / 'administrative' / 'seen-arxiv-ids.json'
    return set(json.loads(p.read_text())['ids']) if p.exists() else set()


cmd = sys.argv[1]
if cmd == 'query':
    q, name = sys.argv[2], sys.argv[3]
    n = sys.argv[4] if len(sys.argv) > 4 else '25'
    r = fetch((name + '.xml', 'https://export.arxiv.org/api/query?search_query=' + urllib.parse.quote(q)
               + '&max_results=' + n + '&sortBy=submittedDate&sortOrder=descending'))
    print({k: r.get(k) for k in ('status', 'sha256', 'error')})
    if 'copy' in r:
        S = seen_ids()
        for i, t, d, c in entries(L / r['copy']):
            base = re.sub(r'v\d+$', '', i)
            print(('SEEN ' if base in S else '     ') + i, d, c, '|', t[:110])
elif cmd == 'get':
    print(fetch((sys.argv[2], sys.argv[3])))
elif cmd == 'batch':
    with concurrent.futures.ThreadPoolExecutor(max_workers=3) as ex:
        for r in ex.map(fetch, [(n + '.pdf', 'https://arxiv.org/pdf/' + n) for n in sys.argv[2:]]):
            print({k: r.get(k) for k in ('name', 'status', 'bytes', 'sha256', 'error')})
elif cmd == 'extract':
    for n in sys.argv[2:]:
        p = L / 'frozen' / n
        before = h(p)
        orig = L / 'primary' / n
        assert h(orig) == before, 'frozen copy differs from original'
        q = L / 'frozen' / (n + '.txt')
        subprocess.run(['pdftotext', '-layout', str(p), str(q)], check=True, timeout=60)
        assert h(p) == before and h(orig) == before
        with (L / 'extractions.jsonl').open('a') as f:
            f.write(json.dumps({'pdf': n, 'sha256': before, 'text': q.name, 'text_sha256': h(q), 'utc': now()}) + '\n')
        print(n, before[:16], 'ok')
elif cmd == 'read':
    n = sys.argv[2]
    words = sys.argv[3:] or ['conjectur', 'open problem', 'question', 'we ask', 'open question']
    lines = (L / 'frozen' / n).read_text(errors='replace').splitlines()
    last = -100
    for i, line in enumerate(lines):
        if any(w in line.lower() for w in words) and i > last + 14:
            print('\n@@', i + 1)
            print('\n'.join(lines[max(0, i - 3):i + 14]))
            last = i
elif cmd == 'history':
    terms = sys.argv[2:]
    rows, hits = [], []
    cands = [BATCH / 'ledger.json', BATCH / 'NEXT.md', BATCH / 'prior-campaign-context.json', BATCH / 'tasks.json']
    for d in sorted((BATCH / 'lanes').iterdir()):
        if d.is_dir() and d != L:
            for p in d.iterdir():
                if p.is_file() and p.name.lower() in ('scouting.md', 'summary.md', 'discovery.md', 'status.md', 'proof.md'):
                    cands.append(p)
    for p in cands:
        if not p.exists() or p.stat().st_size > 400000:
            continue
        data = p.read_bytes()
        before = hashlib.sha256(data).hexdigest()
        rows.append({'path': str(p.relative_to(CAMPAIGNS)), 'sha256': before})
        t = data.decode(errors='replace').lower()
        found = [s for s in terms if s.lower() in t]
        if found:
            hits.append({'path': str(p.relative_to(CAMPAIGNS)), 'terms': found,
                         'excerpts': [data.decode(errors='replace')[max(0, t.find(s.lower()) - 150):t.find(s.lower()) + 250] for s in found]})
    out = L / 'administrative' / ('history-' + hashlib.sha256(' '.join(terms).encode()).hexdigest()[:10] + '.json')
    out.write_text(json.dumps({'utc': now(), 'terms': terms, 'references': len(rows), 'hits': hits}, indent=1))
    for x in hits:
        print('HIT', x['path'], x['terms'])
        for e in x['excerpts']:
            print('   ', ' '.join(e.split())[:380])
    print('screened', len(rows), '->', out.name)
elif cmd == 'seen':
    ids, refs = set(), 0
    pat = re.compile(rb'(?<![\d.])((?:0[7-9]|1\d|2\d)(?:0[1-9]|1[0-2])\.\d{4,5})(?:v\d+)?(?![\d])')
    for root in [CAMPAIGNS, CAMPAIGNS.parent / 'iterations', CAMPAIGNS.parent / 'scouts',
                 CAMPAIGNS.parent / 'findings', CAMPAIGNS.parent / 'reviews', CAMPAIGNS.parent / 'experiments']:
        if not root.exists():
            continue
        for p in root.rglob('*'):
            if L in p.parents or not p.is_file() or p.suffix.lower() not in ('.md', '.json', '.jsonl', '.txt', '.tex') or p.stat().st_size > 3000000:
                continue
            if p.suffix == '.txt' and 'frozen' in p.parts:
                continue  # extracted paper bodies cite many unrelated references
            refs += 1
            for m in pat.findall(p.read_bytes()):
                ids.add(m.decode())
    (L / 'administrative' / 'seen-arxiv-ids.json').write_text(json.dumps({'utc': now(), 'files_scanned': refs, 'ids': sorted(ids)}))
    print(refs, 'files', len(ids), 'ids')
