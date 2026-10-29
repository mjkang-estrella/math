exec((__import__('pathlib').Path(__file__).parent/'refresh.py').read_text().split('coverage={}')[0])
log=json.loads((b/'http-log.json').read_text())
get('arrangement-source.tar','https://arxiv.org/src/2610.33653v1')
get('arrangement-2006.pdf','https://emis.dsd.sztaki.hu/journals/JIPAM/images/126_06_JIPAM/126_06_www.pdf')
