#!/bin/bash
# timing: enumeration-only vs full, p=13 chunk sample
cd "$(dirname "$0")/.."
time (scripts/seating 13 0 20 | tail -1)
