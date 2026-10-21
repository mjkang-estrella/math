from pathlib import Path
import fnmatch
OWN='frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r132'
ROUND_PATTERNS=[
 '*structural*r165*','*analytic*r160*','*structural*r166*','*analytic*r161*','*structural*r167*','*analytic*r162*','*structural*r161*','*t126s161*','*t360s147*',
 '*arithmetic*r131*','*arithmetic*r130*','*arithmetic*r129*','*arithmetic*r128*','*arithmetic*r127*','*arithmetic*r126*','*arithmetic*r125*','*arithmetic*r124*','*arithmetic*r123*','*arithmetic*r122*','*arithmetic*r121*','*arithmetic*r120*','*arithmetic*r119*','*arithmetic*r118*','*arithmetic*r117*','*arithmetic*r116*','*arithmetic*r115*','*arithmetic*r114*',
 '*analytic*r159*','*analytic*r158*','*analytic*r157*','*analytic*r156*','*analytic*r155*','*analytic*r154*','*analytic*r153*','*analytic*r152*','*analytic*r151*','*analytic*r150*','*analytic*r149*','*analytic*r148*','*analytic*r147*','*analytic*r146*','*analytic*r145*','*analytic*r144*','*analytic*r143*','*analytic*r142*',
 '*structural*r164*','*structural*r163*','*structural*r162*','*structural*r160*','*structural*r159*','*structural*r158*','*structural*r157*','*structural*r156*','*structural*r155*','*structural*r154*','*structural*r153*','*structural*r152*','*structural*r151*','*structural*r150*',
 '*h138-*','*t185r144-*','*t177c143-*','*t373e135-*','*k369r134-*','*t088p133-*']
# Deliberately coarse full-relative-path substring exclusions; casefold BEFORE all tests.
ADMIN=('corpus','source','primary','history-derivative','search','inventory','fixture','control','extract','render','vendor','build','copy','copied','frozen','role','formal','manuscript','release','parent','private','input','upstream','shortlist','context','fetched','scratch','preprint','catalogue','catalog','receipt','brief','intake','bundle','recovery','manifest','authentication','task','work','family-title','literature','venv','site-packages','packet','payload','archive','cache','download','external','third-party','hits','index','navigation','audit','log','provenance','evidence','ledger','helper','readme','direct.tex','pinned-','scan','snapshot','submissions','retention','retrieve','record_evidence','validation','invocation','checkpoint-output','journal','status','progress','final','report','handoff','disposition','integrity','checkpoint','contribution','proof-role','ten-findings','twenty-findings','sawin-2018','tao-teravainen','acquire','checks','verify','seal_once','exact_moments','tools','scripts','verification','prepare','metadata','contracts','bind_passages','replay','stderr','author-completion','reading-limit','history-scout','new-ten','terminal-summary','summary','history-focused','history','review','proof-r','check','freeze','rights','dependencies','node_modules','.git','sharedtasks','dispatch','integration','reproduce','reproduction','resume','launch','scout','reading','failure','outcome','completion','retrieval','seal','diagnostic')
def denied(relative):
 s=Path(relative).as_posix().casefold()
 if s==OWN or s.startswith(OWN+'/'): return True
 if any(fnmatch.fnmatchcase(s,p) for p in ROUND_PATTERNS): return True
 if any(p in s for p in ADMIN): return True
 if 'screen-' in s or __import__('re').search(r'screen\d+',s): return True
 return False
if __name__=='__main__':
 samples=['x/STRUCTURAL-X-R165/foo.tex','x/role-arithmetic-r132/a.md','x/T126S161.md','x/parent-ANALYTIC-r162.md','x/STRUCTURAL-r161-author/foo','x/README.tex','x/nested/NEW-TEN.md','x/Foo-HiStOrY/a','x/SCREEN123.json','x/compound-SCREEN-037-copy.json','x/compound-SCREEN037.json','x/t360s147-compound.md',OWN+'/notes/a.md']
 # r132 excluded through own root; unrelated r132 strings are not protected peers.
 samples.remove('x/role-arithmetic-r132/a.md')
 assert all(denied(s) for s in samples)
 assert not denied('frontier/campaigns/2026-01-01/proposal-a/notes/volume.tex')
 print('Synthetic exclusion tests passed; no protected path was opened for testing.')
