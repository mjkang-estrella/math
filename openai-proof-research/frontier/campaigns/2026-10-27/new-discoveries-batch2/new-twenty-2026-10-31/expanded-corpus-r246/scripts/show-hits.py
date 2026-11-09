import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1]
for x in json.loads((D/'outputs/registry-screen.json').read_text())['lean_pool_index_hits']:print(x['file'],x['line'],x['text'][:900])
