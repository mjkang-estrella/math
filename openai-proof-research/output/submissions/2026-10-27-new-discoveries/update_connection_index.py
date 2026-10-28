"""Build an honest index of confirmed problem-level posts and pending work."""
import json
from pathlib import Path

root = Path(__file__).resolve().parent
path = root / 'problem-connections.json'
data = json.loads(path.read_text())
papers = data['papers']
connected = sum(bool(p.get('connections')) for p in papers)
entries = sum(len(p.get('connections', [])) for p in papers)
complete = connected == 30 and all(
    set(p['problem_ids']) <= {c['problem_id'] for c in p.get('connections', [])}
    for p in papers)
data['status'] = 'ALL_30_CONNECTED' if complete else 'IN_PROGRESS'
data['connected_papers'] = connected
data['verified_solution_entries'] = entries
data['created_exact_question_records'] = sum(bool(p.get('created_problem')) for p in papers)
path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n')
lines = ['# MathDB problem connections', '',
         f'{connected}/30 papers have verified problem-level solution entries ({entries} entries).', '',
         'Labels describe the actual scope. A posted solution is not a MathDB endorsement or automatic Lean verification. Negative-order Vendi results, the maximal-index classification for d>=5, and the graph-only spectral theorem are partial progress on their broader records. The classical-means exponent-range claim is labelled counterexample, with the full corrected classification in the paper. The DeTemple refutation concerns part (ii) only.', '',
         'Six precise question records were added where no exact existing match was found in bounded site searches. Four are separate questions from the same sources as nearby records; one records the general-coefficient C*-Bieberbach conjectures; the Smale record explicitly formulates the stronger finite-constant question, rather than claiming a first refutation of the old constant-one conjecture. This creates no additional discovery credits.', '',
         '| # | Paper | Problem-level entry | Scope label |',
         '|---|---|---|---|']
for paper in papers:
    links = paper.get('connections', [])
    entry = ', '.join(f'[{c["problem_id"]}]({c["url"]})' for c in links)
    if not entry:
        if paper.get('created_problem'):
            entry = f'[Question created]({paper["created_problem"]["url"]}); solution pending'
        else:
            entry = 'Pending'
    lines.append(f'| {paper["number"]} | [{paper["title"]}]({paper["paper_url"]}) | {entry} | {paper["label"]} |')
if not complete:
    lines += ['', 'Remaining papers: ' + ', '.join(str(p['number']) for p in papers if not p.get('connections')) + '.', '',
              'Resume from problem-connections.json and verify existing solution links before posting. Do not recreate any of the six new question records.']
(root / 'PROBLEM-CONNECTION-INDEX.md').write_text('\n'.join(lines) + '\n')
print(json.dumps({k: data[k] for k in ['status', 'connected_papers', 'verified_solution_entries', 'created_exact_question_records']}))
