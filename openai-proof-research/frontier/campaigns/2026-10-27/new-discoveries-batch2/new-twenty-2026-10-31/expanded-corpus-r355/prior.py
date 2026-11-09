exec(compile((__import__('pathlib').Path(__file__).parent/'research.py').read_text(),'research.py','exec'))
for name in json.loads((P/'historical-results-allowlist.json').read_bytes()):
 if '/rigid-cube-manuscript-r1/results.json' in name:
  o=json.loads(pathlib.Path(name).read_bytes()); print(json.dumps(o)[:8500])
  js('rigid-cube-scoped-history.json',{'path':name,'data':o})
