exec((__import__('pathlib').Path(__file__).parent/'refresh.py').read_text().split('coverage={}')[0])
log=json.loads((b/'http-log.json').read_text());blocked.add('api.github.com')
get('kamano.html','https://www.tandfonline.com/doi/full/10.1080/10652469.2026.2652429')
# read only primary body; failures are kept
