"""Development-only evidence preparation. Refuses to run after the single final seal."""
from pathlib import Path
import json,hashlib,re,runpy,difflib
ROOT=Path(__file__).resolve().parents[3]
S='frontier/sources/i131_soft_summary_stability';E='frontier/experiments/i131_soft_summary_stability'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def sha(b):return hashlib.sha256(b).hexdigest()
def row(p):
 b=(ROOT/p).read_bytes();return dict(path=p,bytes=len(b),sha256=sha(b))
def write(p,v):(ROOT/p).write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n')
def main():
 assert not (ROOT/S/'seal.json').exists()
 mapped={d['local']:d for d in json.loads((ROOT/'frontier/sources/i113_online_optimization_discovery/search-domain.json').read_text())}
 passages=[]
 def passage(p,start=1,end=None,scope='complete passage'):
  d=row(p);ls=(ROOT/p).read_text().splitlines();end=end or len(ls)
  assert 1<=start<=end<=len(ls)
  d.update(start=start,end=end,total_lines=len(ls),line_convention='splitlines',passage_sha256=sha('\n'.join(ls[start-1:end]).encode()),scope=scope)
  if p in mapped:d.update(source_path=mapped[p]['path'],url='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+mapped[p]['path'])
  passages.append(d)
 passage(S+'/decoded-iteration128-task.txt',scope='all decoded brief and other fields, before original audit')
 for tail in ['iteration125-dini-singular-packing','iteration122-variational-free-boundary-discovery','iteration119-one-loss-online-selection']:
  passage('frontier/sources/i128_statistical_learning_discovery/decoded-'+tail+'-task.txt',scope='all recursively required decoded briefs, reports, finalized parent records, objections and other fields; escaped duplicate output byte-bound')
 for p in [S+'/snapshots/AGENTS.md',S+'/snapshots/sources__upstream.json',S+'/snapshots/frontier__iterations__i128-statistical-learning-discovery.md',S+'/snapshots/frontier__experiments__i128-parent-verification.json']:
  passage(p,scope='complete original context')
 passage('sources/CONTENTS.md',2920,2945,'family119 actual catalogue; not substituted for source contracts')
 passage(S+'/snapshots/frontier__iterations__README.md',1518,1528,'complete I128/I131 ledger entries')
 base='frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/Sharp-binary-information-contraction-on-the-discrete-cube-September-24-2026/build/'
 for tail in ['main.tex','sections/scalar.tex','sections/canonical.tex','sections/capacity.tex','sections/reserve.tex','sections/thinning.tex','sections/upgrade.tex','sections/flow.tex','references.bib']:
  passage(base+tail,scope='complete stipulated source operation through file ending, not a truth audit')
 passage('frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/Hellinger-contraction-with-arbitrary-Boolean-output-bias-September-24-2026/build/main.tex',scope='complete main contract and mechanism summary; included proof section files not claimed newly reread')
 passage(S+'/external/chen-v2-html.txt',2384,2690,'actual v2 unrestricted induction and semigroup through conclusion, plus following recalled inputs')
 passage(S+'/external/chen-v1-v2-text.diff',scope='complete same-extractor text diff, including changed introduction, discussion, references, and absence of changed appendix mathematical text')
 passage(S+'/external/ky-v1-html.txt',scope='complete current Boolean stability mathematical text including proof and appendix endings')
 for a,b in [(416,477),(602,673),(1063,1294),(2068,2243)]:passage(S+'/external/ky-companion-html.txt',a,b,'complete relied-upon compression, hypercontractivity, profile-clock or soft influence/martingale/spectral operation through proof ending')
 passage(S+'/external/yu-local-html.txt',574,700,'local Boolean statements, reduction and hypercontractivity contract through local theorem')
 passage(S+'/external/yu-local-html.txt',1509,1660,'complete relevant Appendix B asymptotic proof, followed by partial Appendix C not relied upon')
 for p in ['frontier/experiments/i128_statistical_learning_discovery/verify.py','frontier/experiments/i128_statistical_learning_discovery/prepare_evidence.py']:
  passage(p,scope='complete inherited evidence implementation reviewed for single replay and diagnostic deferral')
 write(S+'/read-manifest.json',dict(passages=passages,convention='UTF8 splitlines; selected lines joined by LF, no appended newline; full file hash separately. Inherited LF/PDF conventions unchanged.',limits='exact passages, not universal or corpus-wide semantic coverage'))
 refs={d['path']:row(d['path']) for d in passages if not d['path'].startswith(S+'/')}
 for p in ['frontier/sources/i113_online_optimization_discovery/search-domain.json','frontier/sources/i128_statistical_learning_discovery/external/chen-proof-html.html']:refs[p]=row(p)
 write(S+'/reading-references.json',[refs[p] for p in sorted(refs)])
 selected={d['path']:mapped[d['path']] for d in passages if d['path'] in mapped}
 write(S+'/selected-inventory.json',[selected[p] for p in sorted(selected)])
 contracts=[]
 for d in passages:
  if 'source_path' not in d:continue
  ls=(ROOT/d['path']).read_text().splitlines()
  for i in range(d['start'],d['end']+1):
   for m in re.finditer(r'\\label\{[^}]+\}',ls[i-1]):contracts.append(dict(path=d['path'],line=i,needle=m.group(),text=ls[i-1]))
 write(S+'/source-contracts.json',contracts)
 def lex(paths,expression):
  hits=[]
  for p in paths:
   for i,line in enumerate((ROOT/p).read_text().splitlines(),1):
    ms=list(re.finditer(expression,line,re.I))
    if ms:hits.append(dict(path=p,line=i,text=line,occurrences=[dict(start=m.start(),end=m.end(),text=m.group()) for m in ms]))
  return dict(paths=paths,expression=expression,hits=hits,scope='exact lexical evidence only, not semantic coverage')
 write(S+'/focused-lexical.json',lex(sorted(selected),r'stabil|randomiz|arbitrary|common.{0,2}budget|canonical|thinning|reserve|production|induct|equality|rigid'))
 snapshots=json.loads((ROOT/S/'snapshots.json').read_text())
 write(S+'/ledger-overlap.json',lex([d['snapshot'] for d in snapshots if d['drift']],r'I128|I131|S128|I125|I122|eight|Dini C|physical P112|thermal B|pinned A'))
 ext=json.loads((ROOT/S/'external-manifest.json').read_text())
 for d in ext:
  assert row(d['path'])['sha256']==d['sha256']
  if '/abs/' in d['url']:d['versions']=re.findall(r'\[v[0-9]+\]',(ROOT/d['path']).read_text())
  else:
   d['text']=row(str(Path(d['path']).with_suffix('.txt')))
   d['text']['convention']='extract_html.py HTMLParser, math alttext, nonempty whitespace-collapsed block lines; UTF8 LF with final LF'
 write(S+'/external-manifest.json',ext)
 extract=runpy.run_path(str(ROOT/E/'extract_html.py'))['extract']
 old='frontier/sources/i128_statistical_learning_discovery/external/chen-proof-html.html'
 v1=extract((ROOT/old).read_text());v2=(ROOT/S/'external/chen-v2-html.txt').read_text()
 delta='\n'.join(difflib.unified_diff(v1.splitlines(),v2.splitlines(),fromfile=old,tofile='Chen-v2'))
 actual=(ROOT/S/'external/chen-v1-v2-text.diff').read_text()
 assert actual in [delta,delta+'\n']
 write(S+'/comparison-bindings.json',dict(old=row(old),new=row(S+'/external/chen-v2-html.html'),extractor=row(E+'/extract_html.py'),diff=row(S+'/external/chen-v1-v2-text.diff'),diff_final_newline=actual.endswith('\n'),algorithm='LF join of difflib.unified_diff on extracted splitlines, default n=3/lineterm, fromfile old path and tofile Chen-v2',scope='complete extracted mathematical text diff, not raw HTML or TeX identity'))
 history=[
  dict(event='initial source command used parent cwd',status='failed FileNotFoundError',resolution='reissued with explicit repository cwd'),
  dict(event='broad initial recursive/context search',status='truncated display',resolution='required files decoded and read in explicit completed ranges'),
  dict(event='decoded I125 lines1-310 combined display',status='truncated',resolution='missing lines85-142 reread; all1-643 subsequently complete'),
  dict(event='combined I122 receipt and I119 opening display',status='truncated opening of I119',resolution='I119 lines1-47 reread; remaining1-884 and I1221-525 completed'),
  dict(event='large live-ledger matching display',status='truncated',resolution='complete relevant I128/I131 entries and selected summary sentences read; full ledgers are frozen and lexical records exact, not all semantically read'),
  dict(event='web open actual Chen v2 HTML',status='Internal Error',resolution='urllib direct versioned retrieval status200; actual bytes and text bound'),
  dict(event='web broad literature queries',status='returned largely irrelevant matches',resolution='no inference from title absence; primary versioned operations read'),
  dict(event='first exploration execution',status='ModuleNotFoundError: No module named numpy; subsequent empty-output JSONDecodeError',resolution='rewritten standard-library implementation; successful195-instance output separately bound'),
  dict(event='inherited failures/truncated reads and PDF conventions',status='preserved by reference',resolution='I128 and recursive seals/read records unchanged; original I125 canonical-order FAIL remains distinct'),
 ]
 write(S+'/read-history.json',dict(events=history,completed_ranges_record='read-manifest.json',no_claim='Failed/truncated displays are not complete readings. No active I129/I130 dependency.'))
 print(json.dumps(dict(passages=len(passages),contracts=len(contracts),reading_references=len(refs),external=len(ext))))
if __name__=='__main__':main()
