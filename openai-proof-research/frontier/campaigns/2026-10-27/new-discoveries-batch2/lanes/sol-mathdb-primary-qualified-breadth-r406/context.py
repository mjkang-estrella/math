import pathlib,json
L=pathlib.Path(__file__).parent;B=L.parent
for f in ['root-mathdb-accepted-exclusions-r304/accepted-exclusions.json','root-mathdb-accepted-exclusions-r304/historical-dispositions.json','root-mathdb-cayley-review-intake-r363/disposition.json','root-mathdb-breadth-intake-r405/frozen/sol-mathdb-primary-qualified-breadth-r402/FAILURES.md']:
 p=B/f;v=json.loads(p.read_text()) if p.suffix=='.json' else p.read_text();print(f, str(v)[:17000])
