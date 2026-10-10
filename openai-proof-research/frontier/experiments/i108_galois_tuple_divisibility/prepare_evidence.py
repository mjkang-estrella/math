"""Preparation only. Writes only the assigned I108 source directory; never seals."""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i108_galois_tuple_divisibility'
OLD=ROOT/'frontier/sources/i104_modular_representation_discovery'
def digest(b):return hashlib.sha256(b).hexdigest()
def write(name,obj):(S/name).write_text(json.dumps(obj,ensure_ascii=False,indent=2)+'\n')
def main():
 assert not (S/'seal.json').exists()
 oldseal=json.loads((OLD/'seal.json').read_text())
 paths=set(oldseal['owned_inventory'])
 paths.update(x['path'] for x in json.loads((OLD/'immutable-references.json').read_text()))
 paths.add('frontier/iterations/iteration104-modular-representation-discovery-task.json')
 assert not any('i106' in p or 'i107' in p for p in paths)
 write('immutable-references.json',[{'path':p,'sha256':digest((ROOT/p).read_bytes())} for p in sorted(paths)])
 domain=json.loads((ROOT/'frontier/sources/i88_nonlinear_banach_discovery/search-domain.json').read_text())
 bylocal={x['local']:x for x in domain}
 passages=[]
 def passage(local,first=1,last=None,purpose='complete relevant proof operation'):
  raw=(ROOT/local).read_bytes();txt=raw.decode('utf-8',errors='replace');lines=txt.splitlines();last=last or len(lines)
  row={'local':local,'sha256':digest(raw),'first':first,'last':last,'splitlines_count':len(lines),'lf_split_count':len(txt.split('\n')),'first_line':lines[first-1],'last_line':lines[last-1],'passage_sha256':digest(('\n'.join(lines[first-1:last])+'\n').encode()),'purpose':purpose}
  if local in bylocal:
   x=bylocal[local];row.update({k:x[k] for k in ['path','git_sha','original_local','original_sha256']});row['url']='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path']
  passages.append(row)
 P='frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/'
 A=P+'The-Blockwise-Alperin-Weight-Conjecture-September-23-2026/build/sections/'
 for f in ['group.tex','twist.tex','differentials.tex','valuations.tex','specialization.tex','consequences.tex']:passage(A+f)
 D=P+'Donovans-Conjecture-over-Algebraic-Closures-of-Prime-Fields-September-24-2026/build/sections/'
 passage(D+'08_periodicity.tex')
 I=P+'Integral-Donovan-Finiteness-over-Witt-Vectors-September-25-2026/build/sections/'
 for f in ['03_rigidity.tex','04_comparison.tex','05_sylow.tex','07_assembly.tex']:passage(I+f)
 E='frontier/sources/i104_modular_representation_discovery/external/'
 passage(E+'huang-yilmaz-author.pdf.txt',purpose='entire author manuscript; universal chain and minimal-field functorial comparison')
 passage(E+'ffz-blockwise-v2.pdf.txt',1,430,'definitions, statements and H-triple hypotheses')
 passage(E+'ffz-blockwise-v2.pdf.txt',1660,2175,'induction and final construction through proof ending; imported earlier triple results attributed to authors')
 passage(E+'huang-category-v3.pdf.txt',purpose='entire v3; category and block maps, central extension and equivariant assembly through final proof')
 passage('frontier/sources/i108_galois_tuple_divisibility/external/bby-v1.pdf.txt',purpose='entire stronger functorial companion through proof ending')
 write('passages.json',{'line_convention':'decoded UTF-8 errors=replace; str.splitlines one-based; hash joins selected lines with LF and appends final LF','passages':passages})
 write('extraction-scope.json',{'pdfs':['frontier/sources/i108_galois_tuple_divisibility/external/bby-v1.pdf'],'inherited_pdf_texts':'hash-check only; no repeated extraction of 776 mapped PDFs or inherited primary PDFs'})
 prompt=(S/'original-i108-prompt.txt').read_text()
 report=prompt.split('--- ORIGINAL REPORT ---\n',1)[1].split('\n--- FINAL PARENT RESPONSE ---',1)[0].strip()+'\n'
 (S/'original-i104-report-from-prompt.md').write_text(report)
 write('original-evidence.json',{'transport':'Two T3 tool response envelopes serialized as received tool values; user text concatenated and encoded UTF-8 with one added terminal LF (the envelopes retain the exact emitted text), not a claim of raw network transport bytes','embedded_report_matches_original_snapshot':report.encode()==(S/'snapshots/frontier/iterations/i104-modular-representation-discovery.md').read_bytes(),'original_report_sha256':digest(report.encode()),'original_seal_sha256':digest((OLD/'seal.json').read_bytes()),'four_drifting_live_ledgers':['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']})
 write('failures.json',[
  {'kind':'read-output-truncation','detail':'Initial combined catalogue/ancestor filename inventory and four-ledger read were truncated; no full semantic reading of them claimed. Ancestor filenames outside repo were listed, not opened or bound.'},
  {'kind':'invalid-tool-parameter','error':'Mcp error: -32602: Invalid parameters for tool \'t3_thread_read\': Expected a value less than or equal to 50000 at ["maxCharsPerItem"]','resolution':'Read original prompt in two pages of at most 50000 characters; both tool envelopes retained.'},
  {'kind':'source-path-typo','detail':'Read of twists.tex exited 2; actual twist.tex subsequently read through its ending.'},
  {'kind':'read-output-truncation','detail':'Some combined source/literature/report dumps exceeded the output budget; relied-on proof ranges were read in bounded follow-ups. Lexical matches are not semantic reading.'},
  {'kind':'reference-path-probe','detail':'A schema-inspection probe found no frontier/sources/i88_augmented_catalogue/search-domain.json. Used actual immutable reference frontier/sources/i88_nonlinear_banach_discovery/search-domain.json; no source bytes changed.'},
  {'kind':'inherited-failures','detail':'Original I104 t=7 exploratory misidentification and initial Counter-based verifier failure remain immutable dependencies. They are not passing results.'},
  {'kind':'preseal-checker-failure','record':'validation-attempt-1.json','error':'Original brief mismatch','resolution':'Checker stripped a retained separator newline. Corrected checker extraction to retain the original separator and added LF; original frozen bytes unchanged.'}
 ])
 print(json.dumps({'references':len(paths),'passages':len(passages),'embedded_report_exact':report.encode()==(S/'snapshots/frontier/iterations/i104-modular-representation-discovery.md').read_bytes()}))
if __name__=='__main__':main()
