import pathlib
p=pathlib.Path(__file__).resolve();s=(p.parent/'randic-pure.py').read_text().replace('range(3,16)','range(3,17)').replace("L/'randic-results.json'","L/'randic16-results.json'");exec(compile(s,str(p),'exec'))
