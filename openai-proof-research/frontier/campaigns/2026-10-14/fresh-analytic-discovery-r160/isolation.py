from pathlib import Path
import fnmatch
OWN = "frontier/campaigns/2026-10-14/fresh-analytic-discovery-r160"
PATTERNS = ["*arithmetic*r131*", "*structural*r165*", "*arithmetic*r132*", "*structural*r166*", "*arithmetic*r133*", "*structural*r167*", "*structural*r161*", "*t126s161*", "*t360s147*",
    "*analytic*r141*",
    "*analytic*r142*",
    "*analytic*r143*",
    "*analytic*r144*",
    "*analytic*r145*",
    "*analytic*r146*",
    "*analytic*r147*",
    "*analytic*r148*",
    "*analytic*r149*",
    "*analytic*r150*",
    "*analytic*r151*",
    "*analytic*r152*",
    "*analytic*r153*",
    "*analytic*r154*",
    "*analytic*r155*",
    "*analytic*r156*",
    "*analytic*r157*",
    "*analytic*r158*",
    "*analytic*r159*",
    "*structural*r149*",
    "*structural*r150*",
    "*structural*r151*",
    "*structural*r152*",
    "*structural*r153*",
    "*structural*r154*",
    "*structural*r155*",
    "*structural*r156*",
    "*structural*r157*",
    "*structural*r158*",
    "*structural*r159*",
    "*structural*r160*",
    "*structural*r161*",
    "*structural*r162*",
    "*structural*r163*",
    "*structural*r164*",
    "*arithmetic*r114*",
    "*arithmetic*r115*",
    "*arithmetic*r116*",
    "*arithmetic*r117*",
    "*arithmetic*r118*",
    "*arithmetic*r119*",
    "*arithmetic*r120*",
    "*arithmetic*r121*",
    "*arithmetic*r122*",
    "*arithmetic*r123*",
    "*arithmetic*r124*",
    "*arithmetic*r125*",
    "*arithmetic*r126*",
    "*arithmetic*r127*",
    "*arithmetic*r128*",
    "*arithmetic*r129*",
    "*arithmetic*r130*",
    "*h138-*", "*t185r144-*", "*t177c143-*", "*t373e135-*", "*k369r134-*", "*t088p133-*", "*screen-*", "*screen[0-9][0-9][0-9]*"]
# Conservative path-substring omissions; opaque aliases remain a limit.
GUARDS = tuple("""corpus source primary history derivative search inventory fixture control extract render vendor build copy copied frozen role formal manuscript release parent private input upstream shortlist context fetched scratch preprint catalogue catalog receipt brief intake bundle recovery manifest authentication task work family-title literature venv site-packages packet payload archive cache download external third-party hits index navigation audit log provenance evidence ledger helper readme direct.tex pinned- scan snapshot submissions retention retrieve record_evidence validation invocation checkpoint-output journal status progress final report handoff disposition integrity checkpoint contribution proof-role ten-findings twenty-findings new-ten terminal-summary summary.json sawin-2018 tao-teravainen verify verification prepare metadata contracts bind_passages replay stderr author-completion reading-limit history-scout .git dependencies sharedtasks summary seal fetch retrieval isolation reading-and-failures dispatch integration reproduce reproduction resume launch scout review proof-r check freeze rights""".split())
def excluded(relative):
    s=relative.as_posix().casefold()
    if s == OWN or s.startswith(OWN + "/"):
        return True
    if any(fnmatch.fnmatchcase(s,p) for p in PATTERNS):
        return True
    return any(g in s for g in GUARDS)
def self_test():
    protected=["A/FRESH-ARITHMETIC-R131/x", "FLAT-STRUCTURAL-R167-BRIEF.md", "a/T126S161-copy.tex", "a/t360s147.md", "a/README", "a/New-Ten/x", "a/TEN-FINDINGS/x", "a/Twenty-Findings/x", "a/sharedTASKS/x", "a/SUMMARY/x", "a/DISPATCH/x", "a/inTEGRATION/x", "a/REPRODUCTION/x", "a/resuME/x", "a/LAUNCH/x", "a/SCOUT/x", "a/SaWiN-2018/a", "a/SCREEN-abc/x", "a/SCREEN123/x", OWN+"/a"]
    assert all(excluded(Path(p)) for p in protected)
    assert not excluded(Path("frontier/campaigns/2026-01-01/idea/derivation.tex"))
    return len(protected)
