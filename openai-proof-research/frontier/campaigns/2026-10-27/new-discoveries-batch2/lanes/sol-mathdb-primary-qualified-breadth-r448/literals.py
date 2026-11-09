import pathlib,json
O=pathlib.Path(__file__).parent
s='\n\n'.join(str(r['mathdb_id'])+' | '+r['title']+'\n'+r['statement']+'\n'+r['source_name']+' | '+r['source_url'] for r in json.loads((O/'records.json').read_text()))
(O/'literal-reading.txt').write_text(s+'\n');print(s)
