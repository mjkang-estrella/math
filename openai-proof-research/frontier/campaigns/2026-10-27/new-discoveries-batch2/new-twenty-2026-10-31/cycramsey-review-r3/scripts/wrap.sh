#!/bin/bash
# Resource wrapper: 2 CPUs, CPU 120 s, wall 140 s, address space 500 MB, MALLOC_ARENA_MAX=2.
export MALLOC_ARENA_MAX=2
exec timeout -k 5 140 taskset -c 0,1 prlimit --cpu=120 --as=524288000 -- "$@"
