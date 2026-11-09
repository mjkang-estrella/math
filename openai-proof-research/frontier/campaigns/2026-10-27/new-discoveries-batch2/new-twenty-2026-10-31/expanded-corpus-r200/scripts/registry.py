import pathlib,json,sys,subprocess,urllib.parse,time
D=pathlib.Path(__file__).resolve().parents[1]
qs=['"Kotlar" "lean"','"1512.02499" "lean"','"Matsui" "ASEP" "lean"','"Roberts" "Yamanouchi" "lean"','"Romik" "percolation" "lean"','"Lapointe" "Pinto" "lean"','"Levine" "Pegden" "tiling" "lean"','"Macdonald" "bijection" "lean"']
(D/'outputs/github-queries.json').write_text(json.dumps(qs,indent=2))
for q in qs:
 if any(json.loads(p.read_text()).get('status') in [403,429] and 'api.github.com' in json.loads(p.read_text())['url'] for p in (D/'sources').glob('*/receipt.json')):print('STOP denied GitHub route');break
 subprocess.run([sys.executable,'-I',str(D/'scripts/fetch.py'),'https://api.github.com/search/repositories?q='+urllib.parse.quote(q)],check=True);time.sleep(7)
