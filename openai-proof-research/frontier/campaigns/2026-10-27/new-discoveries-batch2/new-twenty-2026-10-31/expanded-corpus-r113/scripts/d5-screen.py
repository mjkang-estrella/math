import pathlib,json,re
D=pathlib.Path(__file__).resolve().parents[1];o=json.loads((D/'sources/omega-D5.json').read_text());pat=re.compile(r'pinwheel|folding|wreath|cylindric|Schubert|Duval|rational.base|formality|Johnson|partition|stack.sort',re.I)
hits=[x['path'] for x in o['tree'] if pat.search(x['path'])];print('\n'.join(hits));(D/'outputs/d5-topic-paths.json').write_text(json.dumps(hits,indent=2))
