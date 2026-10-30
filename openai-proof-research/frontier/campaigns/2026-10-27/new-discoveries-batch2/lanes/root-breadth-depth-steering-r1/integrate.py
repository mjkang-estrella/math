from pathlib import Path
import json,subprocess
P=Path(__file__).resolve().parent;B=P.parents[1];repo=B.parents[4]
l=json.loads((B/'ledger.json').read_text());assert l['accepted_count']==9 and l['total_accepted_count']==39
intro='Latest user steering: explore widely alongside solving; speed takes priority over repetitive handback paperwork. Existing r213/r214 now broad scouts, r215 focused solver. Two complementary scouting shortlists feed sustained full-scope attacks. Use compact rejects and verified immutable references; acceptance standards unchanged. See root-breadth-depth-steering-r1 and updated AGENTS.md. Counts 9 additional / 39 total, next 40.\n\n'
n=(B/'NEXT.md').read_text();heading='# Current continuation — 29 October 2026\n';assert heading in n
if intro not in n:(B/'NEXT.md').write_text(n.replace(heading,heading+'\n'+intro,1))
paths=[B/'AGENTS.md',B/'NEXT.md']+[p for p in P.iterdir() if p.is_file() and p.name!='commit-paths.txt']
ps=P/'commit-paths.txt';ps.write_text(''.join(str(p.relative_to(repo))+'\n' for p in sorted(paths)))
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(ps)],cwd=repo,check=True)
subprocess.run(git+['commit','-m','Shift research to broad scouting alongside focused solving','--pathspec-from-file='+str(ps)],cwd=repo,check=True,stdout=subprocess.DEVNULL)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
