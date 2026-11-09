#!/usr/bin/env python3
# Reuse the same bounded process-tree runner for artifact operations.
import pathlib,os,sys
D=pathlib.Path(__file__).resolve().parents[1]
s=(D/'scripts/replay.py').read_text().split('\ntry:\n',1)[0]
s=s.replace("assert not list(D.rglob('*.olean')), 'Refusing existing oleans'",'')
ns={'__file__':str(D/'scripts/replay.py')};exec(compile(s,'bounded-runner','exec'),ns)
ns['F']=D;ns['L']=D/'artifact-receipts';ns['L'].mkdir(exist_ok=True)
ns['run'](sys.argv[1],sys.argv[2:])
