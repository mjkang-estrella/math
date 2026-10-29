# Separable derangement enumerator

This directory contains a C program to count separable derangements. It is
based on the recurrences in [this preprint](./paper.pdf) by Dougherty-Bliss,
Galvan, Polley, and Shuster.

The original implementation of these recurrences was done by hand in Maple, but
this C implementation was almost entirely done by GPT-5.6 Sol.

## Build

Required tools and libraries:

- a A compiler;
- Make
- FLINT and GMP;
- OpenMP.

Build the executable by downloading the repository, moving into it, and running
`make`. The result is `build/sepder`.

## Run

The main interface is the command line program `build/sepder`. It is run as
follows:

```sh
build/sepder 20
```

This prints the number of separable derangements from length 0 to length 20,
one line at a time. Additional options are as follows:

```text
--diagnostics  print n, s[n], a[n,0], and b[n] as TSV
--progress     report rate-limited progress on stderr
```

These can also be seen by passing the flag `-h`.

## Test

```sh
make test
make test-terms
```

The test suite checks the published terms through `n=18`, compares every
internal diagonal coefficient through `n=8` with independent brute-force
enumeration, and checks the CLI. The separate `test-terms` target computes
through `n=999` and compares its output with the first 1,000 lines of
`data/terms.txt`, a file that was precomputed and believed to be correct. (This
is mostly to check for any regressions when a change is made.)
