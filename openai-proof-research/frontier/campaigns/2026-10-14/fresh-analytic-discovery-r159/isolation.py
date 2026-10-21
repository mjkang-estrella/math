"""Prospective history selector. All guards precede descent and byte reads."""
from pathlib import Path
import fnmatch,re
ROOT=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
OWN='frontier/campaigns/2026-10-14/fresh-analytic-discovery-r159'
ROUND_GLOBS=[
 '*arithmetic*r130*','*structural*r164*','*arithmetic*r131*','*structural*r165*','*arithmetic*r132*','*structural*r166*','*structural*r161*','*t126s161*','*t360s147*',
 '*analytic*r158*','*analytic*r157*','*analytic*r156*','*analytic*r155*','*analytic*r154*','*analytic*r153*','*analytic*r152*','*analytic*r151*','*analytic*r150*','*analytic*r149*','*analytic*r148*','*analytic*r147*','*analytic*r146*','*analytic*r145*','*analytic*r144*','*analytic*r143*','*analytic*r142*','*analytic*r141*','*analytic*r140*',
 '*structural*r163*','*structural*r162*','*structural*r160*','*structural*r159*','*structural*r158*','*structural*r157*','*structural*r156*','*structural*r155*','*structural*r154*','*structural*r153*','*structural*r152*','*structural*r151*','*structural*r150*','*structural*r149*','*structural*r148*',
 '*arithmetic*r129*','*arithmetic*r128*','*arithmetic*r127*','*arithmetic*r126*','*arithmetic*r125*','*arithmetic*r124*','*arithmetic*r123*','*arithmetic*r122*','*arithmetic*r121*','*arithmetic*r120*','*arithmetic*r119*','*arithmetic*r118*','*arithmetic*r117*','*arithmetic*r116*','*arithmetic*r115*','*arithmetic*r114*','*arithmetic*r113*',
 '*h138-*','*t185r144-*','*t177c143-*','*t373e135-*','*k369r134-*','*t088p133-*']
GUARDS=('sawin-2018','tao-teravainen','replay','verify','verification','prepare','metadata','contracts','bind_passages','author-completion','stderr','reading-limit','reading-and','reading_and','reading.md','150-technical-lemmas','cap-author','r74-cap-construction-astra','r74-structural-construction-astra','corpus','source','primary','history','search','inventory','fixture','control','extract','render','vendor','build','copy','copied','frozen','role','formal','manuscript','release','parent','private','input','upstream','shortlist','context','fetched','scratch','preprint','catalogue','catalog','receipt','brief','intake','bundle','recovery','manifest','authentication','task','work','family-title','literature','venv','site-packages','packet','payload','archive','cache','download','external','third-party','hits','index','navigation','audit','log','provenance','evidence','ledger','helper','readme','direct.tex','pinned-','scan','snapshot','submission','retention','retrieve','record_evidence','validation','invocation','checkpoint','journal','status','progress','final','report','handoff','disposition','integrity','contribution','proof-role','ten-findings','twenty-findings','new-ten','terminal-summary','summary','dispatch','integration','reproduce','reproduction','resume','launch','scout','review','check','freeze','rights','named-primary','dependency','dependencies','node_modules','__pycache__')
def excluded(relative):
 s=relative.as_posix().casefold()
 if s==OWN or s.startswith(OWN+'/'):return True
 if any(fnmatch.fnmatchcase(s,g) for g in ROUND_GLOBS):return True
 if '.git' in s.split('/'):return True
 if any(g in s for g in GUARDS):return True
 if re.search(r'(?:^|/)screen(?:-|\d)',s) or re.search(r'proof-r\d',s):return True
 return False

def tests():
 examples=['x/ARITHMETIC-brief-r130/z','flat-STRUCTURAL-x-r165.md','x/T126S161.md','x/README.md','x/MY-JOURNAL.JSON','x/reVIEW/z','x/NEW-TEN/a','x/compound-history/a','x/TEN-FINDINGS/a','x/screen123/a','x/terminal-SUMMARY.json','x/PROOF-r999/a',OWN+'/a']
 for x in examples:assert excluded(Path(x)),x
 assert not excluded(Path('frontier/campaigns/2026-10-14/old-ergodic/DERIVATION.tex'))
 return len(examples)
if __name__=='__main__':print('synthetic-only predicate tests:',tests())
