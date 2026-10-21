"""Prospective r128 history guard. Deliberately coarse omissions; not clearance."""
import os, fnmatch
from pathlib import Path
ROOT=Path.cwd()
OWN=ROOT/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r128'
PATTERNS=['*analytic*r156*', '*analytic*r157*', '*structural*r161*', '*t126s161*', '*structural*r162*', '*t360s147*', '*arithmetic*r110*', '*arithmetic*r111*', '*arithmetic*r112*', '*arithmetic*r113*', '*arithmetic*r114*', '*arithmetic*r115*', '*arithmetic*r116*', '*arithmetic*r117*', '*arithmetic*r118*', '*arithmetic*r119*', '*arithmetic*r120*', '*arithmetic*r121*', '*arithmetic*r122*', '*arithmetic*r123*', '*arithmetic*r124*', '*arithmetic*r125*', '*arithmetic*r126*', '*arithmetic*r127*', '*analytic*r138*', '*analytic*r139*', '*analytic*r140*', '*analytic*r141*', '*analytic*r142*', '*analytic*r143*', '*analytic*r144*', '*analytic*r145*', '*analytic*r146*', '*analytic*r147*', '*analytic*r148*', '*analytic*r149*', '*analytic*r150*', '*analytic*r151*', '*analytic*r152*', '*analytic*r153*', '*analytic*r154*', '*analytic*r155*', '*structural*r146*', '*structural*r147*', '*structural*r148*', '*structural*r149*', '*structural*r150*', '*structural*r151*', '*structural*r152*', '*structural*r153*', '*structural*r154*', '*structural*r155*', '*structural*r156*', '*structural*r157*', '*structural*r158*', '*structural*r159*', '*structural*r160*', '*h138-*', '*t185r144-*', '*t177c143-*', '*t373e135-*', '*k369r134-*', '*t088p133-*']
CATEGORIES=['corpus', 'source', 'primary', 'history', 'seal', 'identities', 'verify', 'verification', 'history-derivative', 'search', 'inventory', 'fixture', 'control', 'extract', 'render', 'vendor', 'build', 'copy', 'copied', 'frozen', 'role', 'formal', 'manuscript', 'release', 'parent', 'private', 'input', 'upstream', 'shortlist', 'context', 'fetched', 'scratch', 'preprint', 'catalogue', 'catalog', 'receipt', 'brief', 'intake', 'bundle', 'recovery', 'manifest', 'authentication', 'task', 'work', 'family-title', 'literature', 'venv', 'site-packages', 'packet', 'payload', 'archive', 'cache', 'download', 'external', 'third-party', 'hits', 'index', 'navigation', 'audit', 'log', 'provenance', 'evidence', 'ledger', 'helper', 'readme', 'direct.tex', 'pinned-', 'scan', 'snapshot', 'submissions', 'retention', 'retrieve', 'record_evidence', 'validation', 'invocation', 'checkpoint-output']
ADMIN=['.git', 'dependencies', 'node_modules', 'new-ten', 'terminal-summary', 'summary.json', 'tasks.json', 'ten-findings', 'twenty-findings', 'second-history-screen', 'history-screen', 'history-broad-geometry', 'prepare.py', 'journal', 'status', 'progress', 'final', 'report', 'handoff', 'disposition', 'integrity', 'checkpoint']
def excluded(p):
    rel=p.relative_to(ROOT).as_posix().lower()
    if p==OWN or OWN in p.parents: return True
    if any(fnmatch.fnmatchcase(rel,x) for x in PATTERNS): return True
    # Prefix/substrings deliberately cover plural and compound aliases.
    if any(x in part for part in rel.split('/') for x in CATEGORIES+ADMIN): return True
    return False
def files():
    for base, ds, fs in os.walk(ROOT, topdown=True, followlinks=False):
        b=Path(base)
        if b==ROOT:
            ds[:]=[d for d in ds if d in {'frontier','experiments','proposals','scouts','notes','findings','iterations','campaigns'}]
            fs=[]
        ds[:]=sorted(d for d in ds if not (b/d).is_symlink() and not excluded(b/d))
        for f in sorted(fs):
            p=b/f
            if not p.is_symlink() and not excluded(p): yield p
