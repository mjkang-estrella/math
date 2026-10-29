exec((__import__('pathlib').Path(__file__).parent/'refresh.py').read_text().split('coverage={}')[0])
log=json.loads((b/'http-log.json').read_text())
h=json.loads((b/'coverage.json').read_text())['omega']['head']
get('omega-arrangement.md',f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{h}/Problems/javaheri-2026-cyclic-arrangement-conjecture-refutation.md')
get('omega-arrangement.lean',f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{h}/D5/S0/Certificates/Polynomials/JavaheriArrangementDimensionRefutation.lean')
get('omega-arrangement-history.json','https://api.github.com/repos/the-omega-institute/trureturing/commits?path=Problems/javaheri-2026-cyclic-arrangement-conjecture-refutation.md&per_page=100')
