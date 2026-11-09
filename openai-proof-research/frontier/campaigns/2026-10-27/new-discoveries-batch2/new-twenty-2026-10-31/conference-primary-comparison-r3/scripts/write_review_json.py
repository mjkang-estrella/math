import json, hashlib, os, datetime, glob
def h(p): return hashlib.sha256(open(p, 'rb').read()).hexdigest()
fa = json.load(open('receipts/frozen-after.json')); fb = json.load(open('receipts/frozen-before.json'))
arts = sorted([p for p in glob.glob('**/*', recursive=True) if os.path.isfile(p) and not p.startswith('web-untrusted/') and p not in ('review.json', 'review-artifacts-sha256.json')])
r = {
 "utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
 "lane": "conference-primary-comparison-r3", "reviewer": "Claude Opus 5.5 (claude-opus-5-5)", "mathdb_id": 324342,
 "accepted_credit": 0, "campaign_count_unchanged": "3/20 beyond 39 (adjudication-r2 '2/20' stale)",
 "not_reopened": ["qualified significance PASS (root)", "technical Lean PASS 90 main + 26 control", "root wording corrections"],
 "endpoint": {"name": "ConferenceMDS.conjecture5_false", "file": "conference-mds-resume-r4/lean/ConferenceMDS324342.lean",
   "sha256": "49a2c41fe5743745a5bd2a42f8fecce348bd69d65624023aa99affeb984fa111", "formal_claim": "rank10 row code over F19 of one order-20 conference matrix has a nonzero word of weight 9; d<=9<11",
   "not_formal": ["exact d=9", "180/6180 word counts", "minimality of p=19", "two-class order-20 dichotomy"]},
 "gap_verdicts": {
   "TIT2013_journal_math": {"verdict": "RESOLVED_PASS", "method": "local Ghostscript -dSAFER render of frozen author-posted IEEE typeset copy (IT13.pdf a7b49ca6...); page tree rebuilt on a copy; orphan content stream obj129 wrapped as p.6715",
      "sections_read": ["p.6712 masthead/dates/DOI", "p.6715 Theorem 2, Theorem 4, Conjecture 1, Paley n<=23 remark, GG [17] sentence", "p.6722 Sec V open problem 2 and references [17]"],
      "exact_text": {"Theorem4": "If W is a conference matrix of order n = p+1, where p is a prime, then its rank over Z_p (also F_p) is (p+1)/2.",
                     "Conjecture1": "If C is a code of length p+1 constructed from a generator matrix which is a conference matrix then C is a maximum distance separable (MDS) code of dimension (p+1)/2 and minimum Hamming distance (p+3)/2.",
                     "OpenProblem2": "Is the code of length p+1, p prime, obtained from a conference matrix of order p+1 an MDS code?"},
      "comparison": "parameters, quantifier scope identical to arXiv v1/v2 Conj5 and ISIT Conj1; differences only label, spelled-out MDS, one-word grammar in open problem 2; v1 Theorem4 typo n=p-1 only in v1; no Paley restriction in any version",
      "journal_date": "2013 (published online 2013-06-12; current version 2013-09-11); 2015 is upload directory only",
      "limit": "author-posted typeset copy, not publisher retrieval; header/DOI/dates match Crossref"},
   "ArasuGulliver2001_body": {"verdict": "UNRESOLVED_exact_gap_retained_HOLD_under_root_standard",
      "missing": "AG Section 2 Propositions 2.1-2.2 and tables (body unread)",
      "routes": ["OpenAlex live: closed, no repository fulltext", "CORE Scholar math/563: metadata only; ezproxy not used", "Crossref: only similarity-checking xplorestaging link (not lawful public route; not fetched)", "fatcat: timeout, not retried", "scholar.archive.org: PoW challenge, not solved", "Gulliver UVic pages: no publication PDFs", "arXiv API: no copy", "2 web searches: no copy", "citing works: ScienceDirect 403 (stopped), HAL Anubis challenge (not solved), CiteSeerX 429 (not retried), arXiv 2009.06609 read (no relevant statement)", "Gaborit tables: GF(2..7) only"],
      "narrowing": ["Armario-Frau 1311.2637 Sec1.2/2.C/3: AG method [alpha I, beta I + W] alpha,beta!=0 alpha^2+beta^2+k=0 mod p; AG tabulated data symmetric conference matrices orders 6,14; search limit length 40; cites [2, Prop 2.1 and 2.2] for conference matrices", "arithmetic p=k=19: -1 nonsquare; no alpha!=0 with alpha^2+19=0; no alpha,beta!=0 with alpha^2+beta^2+19=0 (work/ag_arith.json)", "abstract: all weighing matrices order<=13 only"],
      "residual_risk": "unread remark/table about length-n row code of W when p|k, specifically an order-20 F19 distance <11 or a not-necessarily-MDS statement",
      "weak_circumstantial_only": ["EVY 2012-13 posed question as open citing Gulliver-coauthored GG", "Harada-Munemasa 2011 uses length-n row codes mod p|k without citing AG"]},
   "GrasslGulliver2008_body": {"verdict": "UNRESOLVED_low_risk_disclosed", "routes": ["OpenAlex live closed", "Crossref metadata", "fatcat timeout", "scholar.archive challenge", "web search no copy", "OpenAlex citing query 429 not retried"],
      "new_primary_datum": "all four EVY versions cite GG only for construction of codes with these parameters (self-dual MDS of length q+1, q prime power): existence/Paley side"},
   "live_registries": {"openai_math": {"head": "4eaee87548250b2682affda7d05d947c05554bae", "commit_date": "2026-10-30T00:35:35Z", "checked_utc": "2026-11-01T13:10:25Z", "changed": False, "tree_truncated": True, "entries": 55173, "path_hits_relevant": 0},
      "omega_trureturing": {"prior_head": "9abc86d1d73c7f0588782acc67b741a40b79e350", "head": "e9b39e568e8e0b68788ec0f007bc0107069db513", "head_commit_date": "2026-11-01T13:06:17Z", "compare_files": 15, "compare_relevant": 0,
         "subtrees": {"Problems": [ "48b275809bb6647c93389f2a24085be354ad9f49", 1629], "D5": ["9fad7f87aadd4c27bff67675970ad8b472c19c90", 13297], "Library": ["208e9ca152327d7789e431b88111c902e757b810", 2598]},
         "body_read": {"path": "D5/S3/Quantum/Fermionic/ConferenceMatrices.lean", "sha256": "88f05537b5ac7955", "added": "697fa44da2 2026-10-10", "relevance": "unrelated: recursive skew conference family order 2^(r+1), no codes/prime field/order 20"}},
      "mathdb": "known only to 04:46 UTC; inherited 403 respected, not retried", "limit": "path screens plus one body; not full-body clearance"},
   "citing_bodies": {"cumulative_bodies_read": ["2303.16879", "2207.08031", "1412.5797", "2202.10005", "1611.00435", "2404.12868", "1306.5350"], "finding": "none mention conference-matrix codes/MDS beyond EVY reference", "remaining": "title-only", "web_searches": 2, "public_refutation_found": False}
 },
 "primary_scope_bridges": ["MathDB 324342 literal == TIT Conj1 in every parameter; 'Let p be a prime' from Theorem 4/open problem 2 context", "journal 'code constructed from generator matrix' with Theorem 4 F_p rank and Theorem 2 Lambda(W) reduction == F_p row span (rowCode, latticeCode_eq_rowCode)", "MDS and distance clauses refuted by d<=9 at p=19; dimension clause (Theorem 4) true"],
 "novelty_recommendation": {"fidelity": "PASS including journal version", "prior_art_bounded": "no public resolution found", "material_gap": "Arasu-Gulliver 2001 body only (narrowed, not cleared); novelty HOLD remains under root's current standard",
   "if_root_applies_388087_precedent": "bounded novelty PASS; no prior statement found; AG 2001 body unread (closed access), constructions as described incapable of producing the F19 order-20 code", "GG2008": "low-risk disclosed gap"},
 "frozen_checks": {"inputs": "frozen-inputs.json", "files": 140, "before": {"utc": fb["utc"], "match": fb["match"], "mismatch": len(fb["mismatch"]), "missing": len(fb["missing"])},
   "after": {"utc": fa["utc"], "match": fa["match"], "mismatch": len(fa["mismatch"]), "missing": len(fa["missing"])}},
 "http": {"receipts": "receipts/http-receipts.jsonl", "requests": sum(1 for _ in open('receipts/http-receipts.jsonl')), "status_counts": {"200": 29, "200_challenge_pages": 3, "403": 1, "429": 2, "timeout_000": 2}, "retries": 0},
 "renders": {"IT13-repaired.pdf": h('work/it13-rebuild/IT13-repaired.pdf'), "p6715.pdf": h('work/it13-rebuild/p6715.pdf'), "p6715.png": h('work/it13-rebuild/p6715.png'), "q04.png(p6722)": h('work/it13-rebuild/q04.png')},
 "conduct": {"child_agents": 0, "git": False, "shared_or_author_edits": False, "external_messages": False, "uploads": False, "browser_tabs": False, "lean_replay": False, "paper_build": False, "cpu": "taskset -c 0, ulimit -v <=2GB, timeouts <=300s", "background_jobs_left": 0},
}
json.dump(r, open('review.json', 'w'), indent=1)
json.dump({p: h(p) for p in arts + ['review.json']}, open('review-artifacts-sha256.json', 'w'), indent=1)
print('ok', len(arts))
