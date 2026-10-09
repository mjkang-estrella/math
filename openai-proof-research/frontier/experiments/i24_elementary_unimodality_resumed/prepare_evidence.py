"""Complete contracts using immutable inherited bytes; never repair the old tree."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[3]
OLD = ROOT/'frontier/sources/i24_elementary_unimodality'
NEW = ROOT/'frontier/sources/i24_elementary_unimodality_resumed'


def sha(b):
    return hashlib.sha256(b).hexdigest()


def put(name, value):
    (NEW/name).write_text(json.dumps(value, indent=2, ensure_ascii=False)+'\n')


def slice_record(path, first, last, label, purpose):
    lines = path.read_text().split('\n')
    text = '\n'.join(lines[first-1:last])
    return {'path': str(path.relative_to(ROOT)), 'first_line': first, 'last_line': last,
            'label': label, 'purpose': purpose, 'text': text,
            'slice_sha256': sha(text.encode()), 'file_sha256': sha(path.read_bytes())}


def passage(path, start, stop, label, purpose):
    text = path.read_text()
    begin = text.index(start)
    try:
        end = text.index(stop, begin+len(start)) if stop else len(text)
    except ValueError as exc:
        raise ValueError((label, stop)) from exc
    return slice_record(path, text.count('\n', 0, begin)+1,
                        text.count('\n', 0, end)+1, label, purpose)


def main():
    manifest = json.loads((OLD/'pinned-manifest.json').read_text())
    treefile = OLD/'inputs/sources/preprints-tree.json'
    tree = json.loads(treefile.read_text())
    assert not tree['truncated']
    blobs = {r['path']: r for r in tree['tree']}
    records = []
    for row in manifest['files']:
        path = OLD/'pinned'/row['path']
        b = path.read_bytes()
        git = hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        assert sha(b) == row['sha256'] and git == row['git_blob'] == blobs[row['path']]['sha']
        records.append({**row, 'local_path': str(path.relative_to(ROOT))})
    put('pinned-references.json', {'pin': manifest['pin'], 'complete_tree': str(treefile.relative_to(ROOT)),
                                  'manuscript_directories': 749, 'files': records})
    contracts, reads = [], []
    for row in records:
        path = ROOT/row['local_path']
        if '/build/sections/' not in str(path):
            continue
        elementary = 'Elementary-Positivity' in str(path)
        if not elementary and path.name != 'introduction.tex':
            continue
        text = path.read_text()
        pattern = r'\\begin\{(theorem|lemma|proposition|corollary|example)\}.*?\\end\{\1\}'
        for m in re.finditer(pattern, text, re.S):
            labels = re.findall(r'\\label\{([^}]+)\}', m.group())
            first = text.count('\n', 0, m.start())+1
            last = text.count('\n', 0, m.end())+1
            contracts.append(slice_record(path, first, last, ','.join(labels) or 'unlabelled '+m.group(1),
                                           'source input or boundary of its stated scope'))
        boundaries = [0]+[m.start() for m in re.finditer(r'\\subsection\{', text)]+[len(text)]
        for a, b in zip(boundaries, boundaries[1:]):
            if a == b:
                continue
            first = text.count('\n', 0, a)+1
            last = text.count('\n', 0, b)+1
            reads.append(slice_record(path, first, last, path.name,
                                      'read source construction/proof' if elementary else
                                      'read identification contract; no application to graph histories established'))
    put('source-contracts.json', contracts)
    put('read-locators.json', {'passages': reads, 'not_claimed_read_or_applied':
                              [r['local_path'] for r in records if 'Hikita' in r['path']
                               and r['path'].endswith('.tex') and not r['path'].endswith('/introduction.tex')]})
    lit = OLD/'literature'
    specifications = [
        ('sw-v2.txt', 'Conjecture 1.3.', '   Conjecture 1.3 applies', 'SW Conjecture 1.3', 'exact target'),
        ('dm-v3-pdf.txt', 'Conjecture 1.4.', '1.3. Dequantization.', 'DM Conjecture 1.4/Theorem 1.5', 'general conjecture versus acyclic theorem'),
        ('dm-v3-pdf.txt', '   We say that a polynomial p(t)', '2See e.g.', 'DM section 2.1', 'Lefschetz, pre-Lefschetz, and bar are different properties'),
        ('dm-v3-pdf.txt', 'Theorem 2.15. Let', 'Remark 2.16.', 'DM Theorem 2.15', 'positivity, bar and pre-Lefschetz only'),
        ('dm-v3-pdf.txt', 'Conjecture 2.17.', 'Theorem 2.19.', 'DM Conjecture 2.17/Theorem 2.18', 'unproved general wall property, acyclic wall theorem'),
        ('dm-v3-pdf.txt', 'Lemma 3.5. Let', '   The next lemma plays', 'DM Lemma 3.5 and proof', 'centered character packets and exterior/symmetric powers already known'),
        ('dm-v3-pdf.txt', 'Proposition 3.12. Suppose', '3.3.4. An application', 'DM Proposition 3.12/Conjecture 3.13/Theorem 3.14', 'bar transport and exact nondegenerate acyclic hypotheses'),
        ('dm-v3-pdf.txt', '6.2.5. Positivity.', 'Theorem 6.15', 'DM section 6.2.5 warning', 'no generic hard Lefschetz for nonproper cyclic-quiver moduli'),
        ('tom-v2-pdf.txt', 'Corollary 4.18.', 'Corollary 4.20.', 'Tom Corollary 4.18', 'almost-K-chain positive formula'),
        ('tom-v2-pdf.txt', 'Corollary 4.20.', '5. Further directions', 'Tom Corollary 4.20 and proof', 'known almost-K-chain unimodality with common centers'),
        ('icm-v1.txt', 'Example 3.11.', '3.4. Why', 'Davison survey Conjecture 3.12', '2026 survey still states two-wall Lefschetz as conjecture'),
        ('cho-huh.txt', 'Theorem 3.3. Let', 'Example 3.4.', 'Cho-Huh Theorem 3.3', 'positivity scope distinct from unimodality'),
        ('cho-huh.txt', 'Theorem 4.2. Let', 'Proof. If we let', 'Cho-Huh Theorem 4.2', 'known explicit family unimodality'),
        ('huh-nam-yoo.txt', 'Theorem 4.9.', '5. Schur expansion', 'Huh-Nam-Yoo Theorem 4.9', 'known melting-lollipop family'),
        ('abreu-nigro-v2.txt', 'Proposition 3.6.', '   We finish this section', 'Abreu-Nigro Proposition 3.6 and proof', 'all abelian graphs and common-center mechanism already known'),
        ('abreu-nigro-v2.txt', 'Conjecture 5.3.', '   In the Schur basis', 'Abreu-Nigro Conjecture 5.3', 'stronger log-concavity conjecture'),
        ('log-concavity-v2.txt', 'Theorem 1.1 (Main theorem).', '  The proof reduces', 'Kafidov v2 Theorem 1.1', 'rank-at-most-three abelian log-concavity; stronger retained version'),
        ('log-concavity-v2.txt', 'Theorem 1.2 (Counterexample).', 'Novelty and scope.', 'Kafidov v2 Theorem 1.2', 'counterexample is explicitly unimodal'),
    ]
    primary = []
    for filename, start, stop, label, purpose in specifications:
        primary.append(passage(lit/filename, start, stop, label, purpose))
    # Exact submission metadata from the inherited primary version pages.
    for path in sorted(lit.glob('*-abs.txt')):
        primary.append(passage(path, 'Submission history', 'Full-text links:', path.stem+' version history',
                               'version and date recorded by primary archive'))
    put('primary-contracts.json', primary)
    # Preserve raw retrieval provenance rather than rerunning its searches.
    put('literature-references.json', {'inherited_manifest': str((lit/'manifest.json').relative_to(ROOT)),
         'retrievals': json.loads((lit/'manifest.json').read_text()),
         'strongest_retained_versions': {'dm': 'v3', 'sw': 'v2', 'tom': 'v2', 'icm': 'v1',
          'cho-huh': 'v2', 'huh-nam-yoo': 'v1', 'abreu-nigro': 'v2', 'log-concavity': 'v2'},
         'unavailable_source': 'icm-davison publisher endpoint returned 403; icm-v1 arXiv full text is used',
         'superseded': 'log-concavity-v1 retained only as historical evidence'})
    put('queries.json', {'corpus_search': str((OLD/'corpus-search.json').relative_to(ROOT)),
         'inherited_web_search_results': str((lit/'web-search-results.json').relative_to(ROOT)),
         'original_web_query_strings': None,
         'provenance_limit': 'Old evidence retains initial/followup result text, not the exact web query payloads. They are not reconstructed or invented.',
         'resumed_search_queries': [],
         'resumed_direct_web_opens': ['https://arxiv.org/abs/1910.12915', 'https://arxiv.org/abs/2607.20595'],
         'reason_for_direct_checks': 'verify general-Lefschetz theorem status and strongest retained log-concavity version; no new literature search',
         'observed_versions': ['1910.12915v3, last revised 15 June 2021', '2607.20595v2, last revised 1 August 2026']})
    print(json.dumps({'pinned_sources': len(records), 'source_contracts': len(contracts),
                      'read_passages': len(reads), 'primary_contracts': len(primary)}))


if __name__ == '__main__':
    main()
