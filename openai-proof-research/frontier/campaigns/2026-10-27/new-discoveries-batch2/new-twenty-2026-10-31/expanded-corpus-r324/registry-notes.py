for name in json.loads((P/'historical-results-allowlist.json').read_text()):
 if not any(s in name for s in ['expanded-corpus-r32/results.json','expanded-corpus-r320/results.json','expanded-corpus-r321/results.json','expanded-corpus-r322/results.json','expanded-corpus-r323/results.json']):continue
 t=pathlib.Path(name).read_text()
 for term in ['LeanPool','registry','projects.yml']:
  pos=t.find(term)
  if pos>=0:print(name,t[max(0,pos-200):pos+1500])
