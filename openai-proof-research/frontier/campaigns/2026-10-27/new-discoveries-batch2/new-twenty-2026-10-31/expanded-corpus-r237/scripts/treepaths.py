from pathlib import Path
import json,runpy
L=Path(__file__).resolve().parents[1];d=json.loads((L/'sources/lean-pool-tree.json').read_text());print('truncated',d.get('truncated'))
for r in d['tree']:
 if r['path'].endswith('projects.yml'):print(r['path'])
for k in ['openai','omega']:
 d=json.loads((L/f'sources/{k}-head.json').read_text());print(k,d['sha'])
