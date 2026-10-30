# Full proof outline

There exist prime inputs p=677 and q=401 for which the source construction yields at least 38 distinct prime outputs, disproving both N≤10 and N≤13.

The input residues are 317 and 41, and both frequencies equal 1. Thus the two primality conditions become Prime(360-r) and Prime(720+r). Thirty-eight explicit residues satisfy the bounds and both primality conditions. Their output values 720+r are distinct. Each output prime itself witnesses that r is a prime residue class modulo 360. Finset inclusion and injectivity prove at least 38 distinct outputs.

All algebra, finite membership tests, and source bridges are proved in the module. See `main.tex` for the detailed argument.
