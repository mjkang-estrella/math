V=json.loads((P/'provenance.json').read_text());done=['367681','367511','368306','367336']
urls=['https://arxiv.org/html/'+v['parsed']['source_url'].split('/')[-1] for k,v in V.items() if k not in done]
sys.argv=['job.py','fetch.py']+urls[int(sys.argv[2]):int(sys.argv[2])+8]
exec(compile((P/'fetch.py').read_text(),'fetch.py','exec'))
