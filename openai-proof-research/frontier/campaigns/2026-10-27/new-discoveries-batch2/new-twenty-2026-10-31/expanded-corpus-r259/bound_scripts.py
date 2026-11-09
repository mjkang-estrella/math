import pathlib
L=pathlib.Path(__file__).resolve().parent
for name in ['sources.py','fetch_more.py','fetch_targets.py','fetch_registry.py']:
 p=L/name;s=p.read_text();p.write_text('import signal\nsignal.alarm(140)\n'+s)
