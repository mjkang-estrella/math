import pathlib,sys
L=pathlib.Path(__file__).resolve().parents[1]
s=(L/'scripts/search_hyper.py').read_text().replace("edges=[sum(1<<v for v in e) for e in itertools.combinations(range(n),3)]", "edges=[sum(1<<v for v in e) for r in range(3,min(n,6)+1) for e in itertools.combinations(range(n),r)]").replace("[4,5,6]", "[4,5]").replace("12000", "20000")
(L/'scripts/search_hyper_mixed.py').write_text(s)
