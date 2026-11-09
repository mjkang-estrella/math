import pathlib
L=pathlib.Path(__file__).resolve().parents[1]
s=(L/'scripts/search_chains.py').read_text().replace('range(2,maxn+1)', 'range(maxn,maxn+1)').replace('range(1,n+1)', 'range(2,n+1)')
(L/'scripts/search_chains_focus.py').write_text(s)
