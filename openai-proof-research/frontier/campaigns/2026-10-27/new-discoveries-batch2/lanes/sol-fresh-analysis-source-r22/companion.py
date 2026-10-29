exec((__import__('pathlib').Path(__file__).parent/'refresh.py').read_text().split('coverage={}')[0])
log=json.loads((b/'http-log.json').read_text());blocked.update(['api.github.com','www.tandfonline.com'])
get('kamano-source.tar','https://arxiv.org/src/2406.10604v1')
get('kamano-abs.html','https://arxiv.org/abs/2406.10604')
