import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1]
p=D/'sources/interweaving-2025-report.pdf.receipt.json';o=json.loads(p.read_text());o.update(body_validation='HTTP 200 body is Incapsula HTML challenge, not PDF; no retry. Scientific report content only from indexed web excerpt.');p.write_text(json.dumps(o,indent=2))
p=D/'SUMMARY.md';s=p.read_text();s=s.replace('Source access limits: the chemistry PDF route returned 403 and was not retried or bypassed.','Source access limits: the chemistry PDF route returned 403 and was not retried or bypassed. The NUS report URL returned an HTTP 200 Incapsula challenge, identified by body inspection and not retried; only an indexed excerpt was read.')
s=s.replace('See outputs/search-notes.md and outputs/registry-screen.json.','See outputs/search-notes.md and outputs/registry-screen.json. The initial historical regex screen had an invalid unescaped title; it was corrected by exact ID/title filtering and a successful no-ignore re-scan (logs/history-full-r2.log), which found only the launch note, a copied ledger and unrelated numerical counts.')
p.write_text(s)
p=D/'scripts/report.py';s=p.read_text().replace("'historical_check':'history-bounded.txt;","'historical_check':'history-bounded.txt and corrected no-ignore logs/history-full-r2.log;");p.write_text(s)
