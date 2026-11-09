"""Focused registry grep for a candidate. usage: registry_focus.py LANEDIR regex"""
import json, sys, pathlib, re
L = pathlib.Path(sys.argv[1]); rx = re.compile(sys.argv[2], re.I)
srcs = {'leanpool-tree': [x['path'] for x in json.loads((L/'sources/leanpool-tree.json').read_text())['tree']],
        'leanpool-projects.yml': (L/'sources/leanpool-projects.yml').read_text(errors='replace').splitlines(),
        'omega-problems': [x['path'] for x in json.loads((L/'sources/omega-problems.json').read_text())['tree']],
        'omega-d5': [x['path'] for x in json.loads((L/'sources/omega-d5.json').read_text())['tree']],
        'omega-reg': [x['path'] for x in json.loads((L/'sources/omega-reg.json').read_text())['tree']],
        'openai-head-files': [f['filename'] for f in json.loads((L/'sources/openai-head.json').read_text()).get('files', [])]}
for k, v in srcs.items():
    h = [(i+1, s.strip()) for i, s in enumerate(v) if rx.search(s)]
    print(f'== {k}: {len(v)} entries, {len(h)} hits'); [print('  ', x) for x in h[:40]]
