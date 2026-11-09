"""Root reporting-only final revision of the 382297 draft paper: status lines, audit paragraph, two references, and three explicit remark corrections. No Lean or new proof."""
import os,resource,subprocess
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,ast
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
M=P/'transitive-bunkbed-manuscript-deepseek-r1';F=P/'transitive-bunkbed-root-final-r1';assert not F.exists()
mex=manifest(M,'MANIFEST.json',190,'seal_manifest','terminal_noncircular_self_exclusions');frozen(M,28);mrec=receipts(M,{})
assert sha(M/'TASK.txt')==read(ROOT/'bunkbed-manuscript-r1-ready.json')['task_sha256']
src=(M/'source/bunkbed-transitive-tournaments.roff').read_text()
audit="Independent audit. A separate reviewer extracted the 33 modules from a sealed archive, matched their hashes, and compiled and kernel-checked all of them from an empty build. The reviewer read every module and found no sorry, added axiom, unsafe code or metaprogramming, and no hypothesis carrying the conclusion. A walk of the 6913 constants in the transitive closure of the endpoint found only the three axioms above and no unsafe or partial constant. The statement was compared with Hollom's definitions and the MathDB record. Lean control modules confirm the exact counts 1 and 2 at n = 1, the counts 7 and 9 out of 16 for a case at n = 2, that the reversed inequality is false for some instance, and that both vertical directions share one token. Four cosmetic or low-severity defects were reported, none affecting validity or fidelity. The relabeling of an abstract transitive tournament to the vertex set {0,...,n-1} is not formalized and is trivial. Upstream Lean and mathlib were trusted rather than rebuilt, and the mathlib checkout was confirmed to be at the stated revision. The reviewer was an AI system distinct from those that produced the proof, and this is not a human referee report."
edits=[("kind:status",".tl 'Bunkbed for transitive tournaments - credit 0''%'",".tl 'Bunkbed for transitive tournaments''%'"),
("kind:status","Draft manuscript. Credit 0; campaign 57 of 80 unchanged. Independent audit unpaid; root alone decides acceptance.","Draft manuscript; not peer reviewed."),
("kind:status","No acceptance, peer review, priority or worldwide novelty is claimed.\n","No peer review, priority or worldwide novelty is claimed.\n"),
("kind:status","No acceptance, peer review, priority or worldwide novelty is claimed; independent audit and acceptance are unpaid and belong to root.","No peer review, priority or worldwide novelty is claimed."),
("kind:citation","The conjecture was introduced by Kasteleyn in 1985 and is now known to be false in general.","The conjecture was introduced by Kasteleyn in 1985 and is now known to be false in general (Gladkov, Pak and Zimin)."),
("kind:math-precision","First, arcs strictly increase the index, so no path returns","First, horizontal arcs strictly increase the index and vertical arcs keep it, so no path returns"),
("kind:math-correction","g(j)(a,b) = (1 - Z(j)) (q(j)^b - q(j)^a) / 2.","g(j)(a,b) = (1 - Z(j)) (q(j)^b - q(j)^a)."),
("kind:math-correction","and the initial law is unchanged.","and the initial state is (1,1) if u is in T and (1,0) otherwise."),
("kind:audit","[INDEPENDENT AUDIT STATUS: to be completed by root]",audit),
("kind:references","[3] Peter van Hintum and Piet Lammers, The bunkbed conjecture on the complete graph, arXiv:1803.07647v4 (27 March 2021).","[3] Peter van Hintum and Piet Lammers, The bunkbed conjecture on the complete graph, arXiv:1803.07647v4 (27 March 2021).\n.br\n.sp 0.2v\n[4] David Aldous and James Allen Fill, Reversible Markov Chains and Random Walks on Graphs, Chapter 12, Section 12.1.8.\n.br\n.sp 0.2v\n[5] Nikita Gladkov, Igor Pak and Aleksandr Zimin, The bunkbed conjecture is false, Proceedings of the National Academy of Sciences 122 (2025), no. 24.")]
new=src;log=[]
for kind,a,b in edits:
 assert new.count(a)==1,a;new=new.replace(a,b);log.append(dict(kind=kind.split(':')[1],before=a,after=b))
assert 'credit 0' not in new.lower() and 'unpaid' not in new and 'campaign' not in new.lower() and 'INDEPENDENT AUDIT STATUS' not in new
for d in ['source','output/pdf','qa/tmp','evidence']:(F/d).mkdir(parents=True,exist_ok=True)
rf=F/'source/bunkbed-transitive-tournaments.roff';rf.write_text(new)
ps=F/'qa/tmp/doc.ps';pdf=F/'output/pdf/bunkbed-transitive-tournaments.pdf'
r=subprocess.run(['groff','-Tps',str(rf)],capture_output=True);assert r.returncode==0 and not r.stderr.strip(),r.stderr;ps.write_bytes(r.stdout)
r2=subprocess.run(['ps2pdf',str(ps),str(pdf)],capture_output=True);assert r2.returncode==0,r2.stderr
r3=subprocess.run(['pdftoppm','-r','150','-png',str(pdf),str(F/'qa/page')],capture_output=True);assert r3.returncode==0,r3.stderr
r4=subprocess.run(['pdfinfo',str(pdf)],capture_output=True,text=True);pages=int([l for l in r4.stdout.splitlines() if l.startswith('Pages:')][0].split()[1]);assert 4<=pages<=6,pages
ps.unlink();(F/'qa/tmp').rmdir()
save(F/'qa/ROOT-CORRECTIONS.json',dict(utc=now,source_manuscript=str(M),source_manuscript_manifest_sha256=sha(M/'MANIFEST.json'),scope='Reporting-only root revision: status lines, audit paragraph, two references, one wording precision and two corrections inside the non-load-bearing Remark 4.1. The main proof of Theorem 2.1 and all Lean statements are unchanged.',remark_correction_basis='For a fixed post set Z(j) is deterministic, so E[U-V]=(1-Z)(q^b-q^a) with no factor 1/2, and the initial state is deterministic; both agree with the second qualification PROOF.md.',corrections=log,pages=pages))
print(json.dumps(dict(manuscript_manifest=190,frozen=28,edits=len(log),pages=pages,pdf_sha256=sha(pdf))))
