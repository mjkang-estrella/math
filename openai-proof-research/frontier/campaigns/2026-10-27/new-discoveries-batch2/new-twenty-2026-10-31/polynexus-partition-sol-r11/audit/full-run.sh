#!/bin/bash
set -eu
source env.sh
UPSTREAM=${LEAN_PATH#*:}
UPSTREAM=${UPSTREAM#*:}
UPSTREAM=${UPSTREAM#*:}
export LEAN_PATH="$PWD/cleanroom/build:$UPSTREAM"
python3 -I -B runner.py full_audit_0 -- "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true audit/Full0.lean
python3 -I -B runner.py full_audit_1 -- "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true audit/Full1.lean
python3 -I -B runner.py full_audit_2 -- "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true audit/Full2.lean
python3 -I -B runner.py full_audit_3 -- "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true audit/Full3.lean
python3 -I -B runner.py full_audit_4 -- "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true audit/Full4.lean
python3 -I -B runner.py full_audit_5 -- "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true audit/Full5.lean
python3 -I -B runner.py full_audit_6 -- "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true audit/Full6.lean
python3 -I -B runner.py full_audit_7 -- "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true audit/Full7.lean
python3 -I -B runner.py full_audit_8 -- "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true audit/Full8.lean
python3 -I -B runner.py full_audit_9 -- "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true audit/Full9.lean
python3 -I -B runner.py full_audit_10 -- "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true audit/Full10.lean
python3 -I -B runner.py full_audit_11 -- "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true audit/Full11.lean
python3 -I -B runner.py full_audit_12 -- "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true audit/Full12.lean
python3 -I -B runner.py full_audit_13 -- "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true audit/Full13.lean
python3 -I -B runner.py full_audit_14 -- "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true audit/Full14.lean
python3 -I -B runner.py full_audit_15 -- "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true audit/Full15.lean
