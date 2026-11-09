import pathlib
p=pathlib.Path(__file__).resolve();s=(p.parent/'laver.py').read_text().replace('range(9)','range(10)').replace("L/'laver-results.json'","L/'laver9-results.json'");exec(compile(s,str(p),'exec'))
