#!/bin/bash
set -eu
cd "$(dirname "$0")/.."
for m in StackSortBasic StackSortMap StackSortSplit StackSortEquivariance StackSortAnalysis StackSortMaximum StackSortCertificate StackSortControls StackSortSmall StackSortFinal StackSortAudit; do
 scripts/run.sh leanchecker "$m"
done
