from retrieve import *
for cat in ['math.NT','math.RA']:
 for j in json.loads((L/(cat+'-entries.json')).read_text()):print(j['id'].split('/')[-1],j['title'])
