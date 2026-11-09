import runpy,sys
from pathlib import Path
m=runpy.run_path(str(Path(__file__).with_name('fetch.py')))
for key,url in zip(sys.argv[1::2],sys.argv[2::2]):print(m['get']((key,url)),flush=True)
