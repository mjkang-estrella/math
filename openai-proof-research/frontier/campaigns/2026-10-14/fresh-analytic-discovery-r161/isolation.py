"""Prospective coarse admission filter. Never reads bodies to test exclusions."""
import fnmatch, pathlib, re
ROOT=pathlib.Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r161')
PATTERNS='''*arithmetic*r132* *structural*r166* *arithmetic*r133* *structural*r167* *arithmetic*r134* *structural*r168* *structural*r161* *t126s161* *t360s147*
*analytic*r160* *analytic*r159* *analytic*r158* *analytic*r157* *analytic*r156* *analytic*r155* *analytic*r154* *analytic*r153* *analytic*r152* *analytic*r151* *analytic*r150* *analytic*r149* *analytic*r148* *analytic*r147* *analytic*r146* *analytic*r145* *analytic*r144*
*structural*r165* *structural*r164* *structural*r163* *structural*r162* *structural*r160* *structural*r159* *structural*r158* *structural*r157* *structural*r156* *structural*r155* *structural*r154* *structural*r153* *structural*r152* *structural*r151*
*arithmetic*r131* *arithmetic*r130* *arithmetic*r129* *arithmetic*r128* *arithmetic*r127* *arithmetic*r126* *arithmetic*r125* *arithmetic*r124* *arithmetic*r123* *arithmetic*r122* *arithmetic*r121* *arithmetic*r120* *arithmetic*r119* *arithmetic*r118* *arithmetic*r117* *arithmetic*r116*
*h138-* *t185r144-* *t177c143-* *t373e135-* *k369r134-* *t088p133-* *history[0-9]* *further-history-* *screen-* *screen[0-9]* *proof-r[0-9]* *check-*'''.split()
# Intentionally broad substring guards over the FULL CASEFOLDED relative path.
GUARDS='''corpus source primary history derivative search inventory fixture control extract render vendor build copy copied frozen role formal manuscript release parent private input upstream shortlist context fetched scratch preprint catalogue catalog receipt brief intake bundle recovery manifest authentication task work family-title literature venv site-packages packet payload archive cache download external third-party hits index navigation audit log provenance evidence ledger helper readme direct.tex pinned- scan snapshot submissions retention retrieve record_evidence validation invocation checkpoint-output journal status progress final report handoff disposition integrity checkpoint contribution proof-role ten-findings twenty-findings sawin-2018 tao-teravainen acquire checks verify seal_once exact_moments tools scripts verification prepare metadata contracts bind_passages replay stderr author-completion reading-limit verifier fetch-family seal-family isolation reading-and-failures history-scout fetch seal reading retrieval completion canonical-bindings capture.py bind.py .git dependencies new-ten terminal-summary summary.json summary review freeze rights sharedtasks dispatch integration reproduce reproduction resume launch scout'''.split()
def excluded(relative):
    s=pathlib.PurePath(relative).as_posix().casefold()
    if s == ROOT.as_posix().casefold() or s.startswith(ROOT.as_posix().casefold()+'/'):
        return True
    if any(fnmatch.fnmatchcase(s,p) for p in PATTERNS): return True
    return any(g in s for g in GUARDS)
def synthetic_test():
    denied=['x/ARITHMETIC-r132/a.md','x/FLAT-structural-r167-BRIEF.md','x/STRUCTURAL-r161-parent.md','x/T126S161.md','x/t360s147/a','x/README.md','x/NEW-TEN.md','x/TEN-FINDINGS/a','x/Twenty-Findings.md','x/SharedTasks/a','x/SUMMARY/a','x/DiSpAtCh/a','x/RePrOdUcTiOn/a','x/ScOuT/a','x/History42/a','x/proof-r19/a','x/screen123.json',str(ROOT/'notes/a.md')]
    assert all(excluded(s) for s in denied)
    assert not excluded('frontier/campaigns/2026-10-01/fresh-analytic-discovery-r100/DERIVATION.tex')
    return {'synthetic_denials':len(denied),'literal_patterns':PATTERNS,'full_path_casefold':True,'limits':'Coarse substring omissions and opaque aliases remain; no perfect classification or exhaustive certificate.'}
if __name__=='__main__':
    import json
    print(json.dumps(synthetic_test(),indent=2))
