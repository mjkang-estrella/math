from pathlib import Path
import re,json
D=Path(__file__).resolve().parents[1]
words=['all','All','through','checkpoint','length','degree','source','Theorem','Corollary','Proposition','Lemma','Conjecture','Theorems','Table','Tables','Figure','Figures','Chapter','Section','seconds','CPU','wall','affinity','RSS','address space','cap','Target','n','m','t','p','j','i']
# Only fixed natural-language labels immediately followed by numbers; do not touch paths, hashes or mathematical identifiers.
def clean(s):
 for w in words:
  if len(w)>1:s=re.sub(r'\b'+re.escape(w)+r'(?=\d)',w+' ',s)
 s=re.sub(r'(?<=\d)(?=(?:positive|primitive|million|terminal|entries|intersection|Parikh|P1|P2|GiB|s\b))',' ',s)
 return s
for f in [D/'SUMMARY.md',D/'outputs/RESEARCH-NOTES.md',D/'outputs/PARTITION-ATTEMPT.md',D/'outputs/SEGRE-BRIDGES.md']:f.write_text(clean(f.read_text()))
r=json.loads((D/'results.json').read_text())
for o in r.values():
 for k in ['review_depth','mathematical_attempts_and_coverage','remaining_lemmas_or_limits']:o[k]=clean(o[k])
(D/'results.json').write_text(json.dumps(r,indent=2,ensure_ascii=False)+'\n')
