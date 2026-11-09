import json, datetime
L = '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/claude-richardson-prior-substantive-r2'
http = [json.loads(l) for l in open(L + '/http.jsonl')]
prov = {
    'review_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'counts_snapshot': {'additional': 9, 'total': 39, 'next': 40},
    'decision': 'EXCLUDE recommended (routine classical corollary); SOURCE PASS; MATH PASS; SUBSTANTIVE FAIL; novelty bounded, no prior publication asserted',
    'decisive_bodies': {
        'Berg': {'url': 'https://arxiv.org/pdf/math/0609283', 'sha256': '2813148b9e7d1c56a3971ef8a529a3921d0b27d80afa7f0b6a796740fc180b8c',
                 'inherited_retrieval_utc': '2026-10-30T07:03:10.827310+00:00',
                 'versions': 'v1 2006-09-11; v2 2010-08-05; journal Arab J. Math. Sci. 17 (2011) 75-88 (VoR unread: ScienceDirect denied)',
                 'locations': 'Section 4 eqs (39)-(41), Theorem 4.2 and displayed inverse-entry formula; extracted lines 838-894 and 1635-1697 (derived/berg-own-extract.txt)'},
        'Richardson2001': {'url': 'https://www.fq.math.ca/Scanned/39-3/richardson.pdf', 'sha256': '09eebfb07b263e5dd20e935f114888e31433266f572966dbf0ede2afaf233d4e',
                           'versions': 'arXiv math/9905079v1 1999-05-12; FQ 39(3) 2001 268-275', 'locations': 'Section 5 Conj 5.1, Thms 5.1-5.3; Section 6 Conj 6.1'},
        'Richardson2020': {'url': 'https://arxiv.org/pdf/2005.08939', 'versions': 'v1 2020-05-18; v2 2020-07-19; v3 2020-08-25 (body v3)', 'locations': 'Intro, Sec 2, Thms 7.1-7.2, refs'},
        'CiglerTyson_r216_pointer': {'url': 'https://arxiv.org/pdf/1807.08330v2', 'sha256': '3e5a6d566f56a76cd825c8e54fcba5d6ab4e3f7d32ac1bcdf2ae1b70616fa6e6',
                                    'note': 'distinct determinant topic; screened only'},
    },
    'textbook_unread_bodies': ['Szego, Orthogonal Polynomials, Thm 3.2.2 (Christoffel-Darboux)', 'Chihara 1978, Thm I.4.5'],
    'fresh_http_receipts': http,
    'stopped_hosts_this_lane': json.load(open(L + '/stopped-hosts.json')),
    'inherited_denials_respected': ['GitHub API/raw/codeload/diff/patch', 'ScienceDirect', 'Google challenge routes'],
    'limits': ['No authenticated current public proof registry', 'Bounded metadata/citer screens only',
               'No exhaustive historical or worldwide priority clearance', 'No Lean or manuscript'],
    'bindings': ['input-bindings.json', 'reference-bindings-supplement.json', 'reference-bindings-r216.json'],
    'manifest_exclusions': ['manifest.json', 'verification-receipt.json'],
}
json.dump(prov, open(L + '/provenance.json', 'w'), indent=1)
print('provenance written', len(http), 'receipts')
