import re,sys,pathlib
KW=r"Golomb|Sidon|derangement|Trail.?Trap|edge.geography|tangram|anagram|abelian.square|bunkbed|sparse.paving|Schubert|Pythagorean|partition.regular|confusion|signed.graph|frustration|isoperimetric|Hamming.cube|Cayley.permutation|Stanley.Yan|log.concave.matroid|cut.complex|shellab|Kohnert|Griggs|chain.decomposition|substitution.matri|metamour|2.distance.graph|overpartition|C_?5.colou?ring|minimal.obstruction|Pokrovskiy|Rz.?.zewski|Goedgebeur|induced.path|P_?t.free|Liebeck|Nikolov|Shalev"
AX=r"2404\.11704|2404\.13424|2404\.17432|2405\.05195|2406\.01790|2406\.05384|2407\.03819|2407\.08360|2407\.09796|2407\.12674|2407\.19583|2407\.19608|2408\.07646|2408\.07800|2408\.13127|2408\.17082|2409\.02306|2409\.02929|2409\.14409"
ID=r"(?<![0-9a-f])(362785|362816|362880|363028|363373|363445|363809|363910|363938|363994|364116|364120|364351|364355|364471|364559|364626|364642|364883|364884)(?![0-9a-f])"
for f in sys.argv[1:]:
    t=pathlib.Path(f).read_text(errors='replace')
    for name,pat in (('KW',KW),('ARXIV',AX),('ID',ID)):
        for m in re.finditer(pat,t,re.I):
            print(name,'|',pathlib.Path(f).name,'|',m.group(0),'|',t[max(0,m.start()-70):m.end()+70].replace('\n',' '))
