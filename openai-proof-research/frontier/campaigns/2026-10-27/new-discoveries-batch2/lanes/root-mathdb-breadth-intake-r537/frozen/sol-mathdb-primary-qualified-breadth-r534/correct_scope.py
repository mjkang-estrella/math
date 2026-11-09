from pathlib import Path
D=Path(__file__).parent
for name in ['write_results.py','dispositions.json']:
 p=D/name;t=p.read_text().replace('Its max=n/N0 near-unimodality statement','Its cumulative max<=n/N0 near-unimodality statement');p.write_text(t)
p=D/'source-coverage.md';t=p.read_text().replace('definitions of maximum-n atoms','definitions of cumulative maximum-at-most-n atoms').replace('; cumulative versus exact-maximum counting also differs.','. Both sources count cumulative maxima; there is no counting-convention objection.').replace('lines 803–920.','lines 200–252, 575–661 and 803–920.');p.write_text(t)
p=D/'failures.md';t=p.read_text()+'\nCorrection before final seal: the first drafted source-coverage note incorrectly suggested a cumulative-versus-exact-maximum discrepancy for 2412.05857v1. Explicit definition lines 256–262 and 325–334 show cumulative max<=n, matching the target convention. The incorrect objection was removed; the remaining near-unimodality versus full-unimodality scope gap remains.\n';p.write_text(t)
