#!/bin/bash
set -eu
for m in CodeLoopFactor CodeLoopCount CodeLoopSets CodeLoopGeom CodeLoopCodes CodeLoopSpace CodeLoopWeight CodeLoopLoop CodeLoopClasses CodeLoopIntersections CodeLoopRepresentations CodeLoopSigns CodeLoopLiteral CodeLoopFin50; do
  bash checker.sh "$m"
done
