# Record 396552 bounded check (Fibonacci word).
# For the coloring family c(U) = (first letter of U, |U| mod k): a monochromatic factorization of
# color class (l, j) exists iff there is an infinite boundary sequence 0=p0<p1<... with
# W[p_i]=l and p_{i+1}-p_i == j (mod k). Any substring of W is a factor of W, so every step
# p->q with q>p, q=p+j (mod k) is legal. Reachability sweep on a prefix of length N.
N = 1_000_000
a, b = "0", "01"          # standard Fibonacci word, letter '0' has gap set {1,2}
while len(b) < N+10:
    a, b = b, b+a
word = b[:N]
print("Fibonacci word prefix length:", len(word))
for k in range(2,7):
    for l in "01":
        for j in range(k):
            maxE=[-1]*k
            if word[0]==l: maxE[0]=0
            reach_max=-1
            for q in range(len(word)):
                p = maxE[(q-j)%k]
                if p>=0 and p<q and word[q]==l and q>maxE[q%k]:
                    maxE[q%k]=q
                    if q>reach_max: reach_max=q
            print(f"k={k} first={l} len%{k}={j}: furthest mono-c boundary = {reach_max}")
