import json,pathlib
D=pathlib.Path(__file__).resolve().parents[1];t=json.loads((D/'sources/openai-root/body').read_text());p=next(v for v in t['tree'] if v['path']=='preprints');(D/'fetch-preprints.json').write_text(json.dumps([(p['url']+'?recursive=1','openai-preprints')]))
