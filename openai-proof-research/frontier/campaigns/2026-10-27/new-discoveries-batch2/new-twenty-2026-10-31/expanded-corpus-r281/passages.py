from pathlib import Path
import json,re
p=Path(__file__).resolve().parent; rs=json.loads((p/'body-receipts.json').read_text())
patterns={'1101.2357':'local|containing.*v|induced cycle','0905.0012':'conjecture|symmetric product|Banach','1112.2801':'reasonably|Conjecture|Ramsey','0201040':'Conjecture|indeterminacy|pure point','0201013':'Conjecture 2|semi.magic hypercube','1007.4287':'endvertex|end.vertex|open question','0608131':'j.*k|Problem|Conjecture','2506.14253':'a, b, c|Question|three real','2308.14019':'Example|counterexample|conjecture','2108.06599':'Conjecture|weakly dominates|reflective tree','1609.03727':'Conjecture|tree|Figure','0801.4393':'Conjecture|universal','2507.20706':'Excedance and antiexcedance|elements Xa|elements X|commute \(for fixed','2410.04559':'simultaneous|efficient|ready|Problem','2002.03542':'polytopes\?|Question 6|open convex|open polytope','0905.4822':'Lemma 1|Lemma 2|Banach|Proof','0908.2988':'Theorem 1.4|Corollary 6.3|universal','1803.00730':'Example 2.21|Example 2.22|Example 2.23','mstd_density':'Theorem 1.3|Theorem 1.4|Proposition|j.*k|Conjecture','1806.03426':'Theorem|Problem 1|Problem 2|NP.complete','0712.0663':'Theorem 2.1|Conjecture|partition','Rolling.pdf':'Theorem|fully labeled|free cells'}
allout=[]
for r in rs:
 if 'text_file' not in r:continue
 key=next((k for k in patterns if k in r['url']),None)
 if not key:continue
 lines=(p/r['text_file']).read_text().splitlines(); indices=[i for i,l in enumerate(lines) if re.search(patterns[key],l,re.I)]
 # bounded targeted passage extraction; no claim of full body review
 covered=set(); chunks=[]
 for i in indices:
  if i in covered:continue
  a=max(0,i-4); b=min(len(lines),i+17);covered.update(range(a,b));chunks.append('\n'.join(f'{j+1}: {lines[j]}' for j in range(a,b)))
 s='\nURL '+r['url']+' FILE '+r['text_file']+'\n'+'\n...\n'.join(chunks)
 allout.append(s)
(p/'target-passages-all-versions.txt').write_text('\n'.join(allout)+'\n')
# print latest / key targets initially
for s in allout:
 if any(k in s.splitlines()[1] for k in ['2308.14019','0905.4822','mstd_density','1806.03426','2507.20706']):print(s[:21000])
