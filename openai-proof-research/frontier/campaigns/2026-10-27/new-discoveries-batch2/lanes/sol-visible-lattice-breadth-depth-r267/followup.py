exec((__import__('pathlib').Path(__file__).parent/'bootstrap.py').read_text().split("for name in ['ledger.json'")[0])
for name in ['history-hits.json','history-reused.json','semantic-history.json']:
 bind(L.parent/'sol-wide-cross-family-mechanisms-r263'/name,'frozen')
bind(L.parent/'sol-wide-new-source-mechanisms-r266'/'SUMMARY.md','frozen')
(L/'history-bindings.json').write_text(json.dumps(items,indent=2))
print('Bound history and overlap summary')
