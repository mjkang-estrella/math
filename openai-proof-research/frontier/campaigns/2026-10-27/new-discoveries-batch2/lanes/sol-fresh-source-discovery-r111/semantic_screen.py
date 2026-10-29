import re,json,gzip
from pathlib import Path
lane=Path(__file__).parent
pat=re.compile(rb'2510[.]09206|entropy increment|entropy.*increment|truncated.exponential|reverse.entropy.power|Zhen.{0,15}Fu|Jiange.{0,15}Li',re.I)
n=0
source=lane/'required-content.jsonl'
with (lane/'semantic-hits.jsonl').open('wb') as out,(source.open('rb') if source.exists() else gzip.open(str(source)+'.gz','rb')) as f:
 for line in f:
  if pat.search(line):out.write(line);n+=1
print(json.dumps({'matching_content_rows':n,'note':'regex leads inspected; no semantic absence certification'}))
