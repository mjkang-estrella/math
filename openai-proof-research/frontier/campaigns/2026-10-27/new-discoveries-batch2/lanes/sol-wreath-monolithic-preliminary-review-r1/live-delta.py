exec(open(__file__.replace('live-delta.py','live-fetch.py')).read().split('items=')[0])
# Reuse only the fetch function definition, without executing its main loop.
ns={};src=(O/'live-fetch.py').read_text();exec(src[src.index('def get('):src.index('with concurrent.futures.ThreadPoolExecutor')],globals())
head=json.loads((O/'live/omega.json').read_text())['sha']; old='bc2b123b706970b673cf734e1323d60f3cc1a435'
items=[('root.json',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{head}'),('delta.json',f'https://api.github.com/repos/the-omega-institute/trureturing/compare/{old}...{head}')]
rows=[get(i) for i in items];(O/'live-delta-http.json').write_text(json.dumps(rows,indent=2))
root=json.loads((O/'live/root.json').read_text()); delta=json.loads((O/'live/delta.json').read_text())
print('HEAD',head,'entries',[(x['path'],x['sha']) for x in root['tree'] if x['path'] in ['D5','Problems']]);print('DELTA',delta.get('total_commits'),[(x['filename'],x['status']) for x in delta.get('files',[])])
