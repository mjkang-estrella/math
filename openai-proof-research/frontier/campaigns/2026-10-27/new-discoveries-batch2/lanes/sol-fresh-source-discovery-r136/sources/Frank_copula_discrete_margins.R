################################################################################
#         A probabilistic framework using the d-variate Frank copula           #
#                    as a multivariate latent variable                         #
#                for modeling correlated ordinal variables                     #
################################################################################
library(copula)
library(GenOrd)
library(mvtnorm)
library(Matrix)
library(nloptr)
# Function computing the Total Variation distance
TVdist <- function(p, q)
{
 1/2*sum(abs(p-q))
}
#
# COMPARISON between GAUSS and FRANK COPULAS
# sharing the same value of Spearman's rank correlation (0.5).
# Frank copula with parameter theta
theta <- 3.5
fc <- frankCopula(theta, dim = 2)
theta <- iRho(fc, 0.5) # find the theta value inducing the rank correlation
theta
fc <- frankCopula(theta, dim = 2)
# Gauss copula with parameter rho
gc <- normalCopula(0.5, dim = 2)
rho <- iRho(gc, 0.5) # find the rho value inducing the rank correlation
rho
gc <- normalCopula(rho, dim = 2)
# Grid
u <- seq(0.001, 0.999, length.out = 100)
grid.f <- expand.grid(u1 = u, u2 = u)
grid.g <- expand.grid(u1 = u, u2 = u)
# Density
grid.f$density <- dCopula(as.matrix(grid.f), fc)
grid.g$density <- dCopula(as.matrix(grid.g), gc)
# Contour plot
op <- par()
par(mai=c(0.75,0.75,0.3,0.1), mgp=c(2.5,1,0), mfrow=c(1,2))
contour(
  u, u,
  matrix(grid.f$density, nrow = length(u)),
  xlab = expression(U[1]),
  ylab = expression(U[2]),main="Frank copula",
)
contour(
  u, u,
  matrix(grid.g$density, nrow = length(u)),
  xlab = expression(U[1]),
  ylab = expression(U[2]), levels=c(0.5,1,1.5,2,2.5,3),main="Gauss copula"
)
# -> FIGURE 2
par(mfrow=c(1,1))
#
############################################
# graph of Spearman's rho for Frank copula #
############################################
op <- par()
par(mai=c(0.75,0.75,0.1,0.1), mgp=c(2.5,1,0))
plot(
  function(theta) sapply(theta, function(t) rho(frankCopula(t))),
  xlim = c(-20, 20),
  ylim = c(-1,1),
  xlab = expression(theta),
  ylab = expression(rho[S])
)
abline(h=c(-1,0,1),v=0,lty=3)
# -> FIGURE 1
# approximation provided by Genest (1987)
plot(function(theta) (1-theta*exp(-theta/2)-exp(-theta))*(exp(-theta/2)-1)^(-2),
     col="red",xlim=c(-20,20),add=TRUE)
par(op)
#
# Function computing a bivariate probability table from a d-variate probability table
#
biv_table <- function(P, i, j) {
  # 1<=i,j>=d are the indexes of the two variables of interest
  d <- length(dim(P))
  margin <- c(i, j)
  apply(P, margin, sum)
}
#
# (Multivariate) Frank cdf (closed form)
#
frank_cdf <- function(Umat, theta) {
  d <- ncol(Umat)
  if (theta==0) {
    return(apply(Umat, 1, prod))
  }
  if (is.infinite(theta) && theta > 0) {
    return(apply(Umat, 1, min))
  }
  if (is.infinite(theta) && theta < 0 && d==2) {
    return(pmax(rowSums(Umat) - (d - 1), 0))
  }
  a <- expm1(-theta)              # exp(-theta) - 1
  P <- expm1(-theta * Umat)       # exp(-theta*u) - 1
  prodP <- apply(P, 1, prod)
  inside_minus_1 <- prodP / (a^(d - 1))
   -(1 / theta) * log1p(inside_minus_1)
}
################################################################################
#             Computation of *implied* pmf and *correlation matrix*            #
#                obtained by discretizing a d-variate Frank copula             #
#                               with parameter theta                           #
#                    by assigning a list of d discrete margins                 #
#                              in any dimension d>=2                           #
################################################################################
contord.F <- function(margins, theta, corr=TRUE)
{
  eps <- 1e-60 # tolerance for probabilities
  # dimension
  d <- length(margins)
  # K contains the length of the d margins
  K <- vapply(margins, length, integer(1))  # number of categories K_j

  # marginal cdf with initial 0
  Flist <- lapply(margins, cumsum)
  Flist <- lapply(Flist, function(x) c(0, x))  # length K_j + 1

  # grid of all cells: prod(K) x d
  idx <- as.matrix(expand.grid(lapply(K, function(k) 1:k)))
  n_cells <- nrow(idx)

  # Bounds L e U
  L <- matrix(0, n_cells, d)
  U <- matrix(0, n_cells, d)
  for (j in 1:d) {
    Fj <- Flist[[j]]
    L[, j] <- Fj[idx[, j]]
    U[, j] <- Fj[idx[, j] + 1]
  }

  # Vertices inclusion–exclusion (2^d)
  V <- as.matrix(expand.grid(rep(list(0:1), d)))
  signs <- (-1)^(d - rowSums(V))

  # Inclusion–exclusion
  joint <- numeric(n_cells)
  for (k in 1:nrow(V)) {
    Uk <- L
    on <- which(V[k, ] == 1)
    if (length(on)) Uk[, on] <- U[, on]
    joint <- joint + signs[k] * frank_cdf(Uk, theta)
  }
  joint<-pmax(joint,eps)
  joint <- joint/sum(joint)
  P <- array(joint, dim = K)

  if(corr==TRUE){
    Sigma <- matrix(0,d,d)
    for(i in 1:(d-1))
    {
      for(j in (i+1):d)
      {
        pmf <- biv_table(P, i, j)
        # calculating Pearson's correlation
        p.1 <- margins[[i]]
        p.2 <- margins[[j]]
        x.1 <- 1:dim(pmf)[1]
        x.2 <- 1:dim(pmf)[2]
        m.1 <- sum(p.1*x.1)
        m.2 <- sum(p.2*x.2)
        v.1 <- sum(p.1*x.1^2)-m.1^2
        v.2 <- sum(p.2*x.2^2)-m.2^2
        # x1x2 <- matrix(kj[i],kj[j])
        cov.12 <- sum(outer(x.1,x.2)*pmf) - m.1*m.2
        cor.12 <- cov.12/sqrt(v.1*v.2)
        Sigma[i,j] <- cor.12
      }
    }
    Sigma <- Sigma + t(Sigma) - diag(diag(Sigma))
    diag(Sigma) <- 1
    return(list(pmf=P, cor=Sigma))} else return(list(pmf=P))
}
#
# pseudo-random simulation in dimension d
# from the discretized Frank copula
#
ordsample.F <- function(n, margins, theta) {
  d <- length(margins)
  cop <- frankCopula(param = theta, dim = d)
  u   <- rCopula(n, cop)
  breaks_list <- lapply(margins, function(p) c(0, cumsum(p)))
  x <- sapply(seq_len(d), function(j)
    as.integer(cut(u[, j], breaks_list[[j]], include.lowest = TRUE))
  )
  x <- as.matrix(x)
  x
}
# example
margins <-list(rep(1/2,2), rep(1/3,3))
theta <- 2
x <- ordsample.F(100, margins, theta)
cor(x)
apply(x, 2, function(col) prop.table(table(col)))
#
# log-likelihood in dimension d>=2
#
ell.Fd <- function(param, x)
{
  # x is a n times d matrix
  # param is a vector containing the d sets of marginal probabilities and
  # the theta parameter
  d <- dim(x)[2]
  # T is the d-variate table
  T <- table(as.data.frame(x))
  marginals <- lapply(seq_len(ncol(x)), function(i) table(x[, i]))
  kj <- sapply(marginals, length)
  margins <- vector("list", d)
  margins <- split(param[-length(param)], rep(seq_along(kj), times = kj))
  theta    <- tail(param, 1)
  p.ij <- contord.F(margins, theta, corr=FALSE)$pmf
  sum(T*log(p.ij))
}
# example
ell.Fd(c(unlist(margins), theta), x)
#
ell.Fpd <- function(margins, theta, x)
{
  # x is a n times d matrix
  p <- contord.F(margins, theta, corr=FALSE)$pmf
  # changed sign
  -sum(table(as.data.frame(x))*log(p))
}
# example
ell.Fpd(margins, theta, x)
#
ell.Fzd <- function(param, x)
{
  # x is a n times d matrix
  # param is a vector containing the d sets of (m_i-1) logarithmic marginal probabilities
  # plus the theta parameter
  d <- dim(x)[2]
  # T is the d-variate table
  T <- table(as.data.frame(x))
  marginals <- lapply(seq_len(ncol(x)), function(i) table(x[, i]))
  kj <- sapply(marginals, length)
  # LOGARITHMIC PROBABILITIES
  z <- vector("list", d)
  z <- split(param[-length(param)], rep(seq_along(kj-1), times = kj-1))
  z <- lapply(z, function(x) c(x,0))
  p <- lapply(z, function(z) exp(z)/sum(exp(z)))
  theta    <- tail(param, 1)
  ell.Fpd(p, theta, x)
}
#
ell_wrap <- function(par) ell.Fzd(par, x)
# example
param <- c(unlist(lapply(margins, function(x) log(x[-length(x)])-log(x[length(x)]))), theta)
ell.Fzd(param, x)
#
# BEGIN - PARAMETER ESTIMATION in DIMENSION d>=2
#
est.Fd <- function(x, method="full")
{
  # d-variate case
  # x is a n times d matrix
  n <- dim(x)[1]
  d <- dim(x)[2]
  marginals <- lapply(seq_len(ncol(x)), function(i) table(x[, i]))
  kj <- sapply(marginals, length)
  pmarginals <- lapply(marginals, prop.table)
  z0_list <- lapply(pmarginals, function(p) {
    m1 <- length(p)
    log(p[-m1]) - log(p[m1])
  })
  z.0 <- unlist(z0_list)
  theta.0 <- 10*mean(cor(x)[!diag(d)])

  # new
  if(method=="2-step")
  {
    res.2step <- optim(par=theta.0, fn=ell.Fpd, margins=pmarginals, x=x,
                       method="L-BFGS-B", hessian=TRUE, lower=0, upper=Inf)
    H <- res.2step$hessian
    se <- as.numeric(1/H^0.5)
    return(list(estimate=res.2step$par, se=se, ell.max=-res.2step$value))
  }

  par <- c(z.0, theta.0)
  if(d<=5) {
    res <- optim(par=par, fn=ell.Fzd, x=x, hessian=TRUE)
    z.sol <- res$par
  } else { # if the dimension is "large", we first run an optimization only over theta
    res.2step <- optim(par=theta.0, fn=ell.Fpd, margins=pmarginals, x=x,
                       method="L-BFGS-B", lower=0, upper=Inf)
    par[length(par)] <- res.2step$par
    # we set some controls in order to reduce the computation time
    control <- list(maxit = 10, trace = 1, reltol = 1e-3)
    res <- optim(par=par, fn=ell.Fzd, x=x, hessian=TRUE, method="CG", control=control)
    z.sol <- res$par
  }
  theta.hat <- z.sol[length(z.sol)]
  z.sol <- split(z.sol[-length(z.sol)], rep(seq_along(kj-1), times = kj-1))
  z.sol <- lapply(z.sol, function(x) c(x,0))
  L <- lapply(z.sol, function(z) exp(z)/sum(exp(z)))
  sol <- unlist(L)
  names(sol) <- unlist(
    mapply(
      function(v, i) paste0("M", i, ",", seq_along(v)),
      L,
      seq_along(L),
      SIMPLIFY = FALSE
    )
  )
  sol <- c(sol, theta.hat)
  names(sol)[length(sol)] <- "theta"
  H <- res$hessian
  V <- solve(H)
  Jmat <- function(p)
  {
    m <- length(p)
    J <- matrix(0, m, m-1)
    for (i in 1:(m-1)) for (j in 1:(m-1))
      J[i,j] <- p[i] * ((i==j) - p[j])
    J[m,] <- -p[m] * p[1:(m-1)]
    J
  }
  make_J_global <- function(p_list) {
    # p_list: list of length d, each element is a probability vector p_i
    J_blocks <- lapply(p_list, Jmat)
    # add theta as last parameter: derivative is 1 w.r.t. itself
    Matrix::bdiag(c(J_blocks, list(matrix(1, 1, 1))))
  }
  J <- make_J_global(L)
  V_nat <- J %*% V %*% t(J) # variance-covariance matrix of the "natural" (original) estimators
  se <- sqrt(diag(V_nat))   # vector of standard errors
  names(se) <- names(sol)
  return(list(estimates=sol,std.errors=se, ell.max=-res$value))
}
#
# ESTIMATION in DIMENSION d>=2 - END
#
################################################################################
#        STUDY ON RELATIONSHIP BETWEEN LATENT AND IMPLIED CORRELATIONS         #
#               FOR SEVERAL VALUES OF THE NUMBER OF CATEGORIES                 #
#     AND SEVERAL VALUES OF SPEARMAN'S RHO INDUCED BY FRANK COPULA THETA       #
#                               UNIFORM MARGINS                                #
################################################################################
k.vec <- 2:11                  # n. of categories
fc    <- frankCopula(dim=2)
rho.latent <- (0:10)/10        # latent correlations
theta.vec <- sapply(rho.latent, function(rho) iRho(fc, rho))
theta.vec
theta.vec[length(theta.vec)] <- Inf
rho.implied <- matrix(0, length(rho.latent), length(k.vec))
for(i in 1:length(theta.vec))
{
  for(j in 1:length(k.vec))
  {
      margins <- list(rep(1/k.vec[j], k.vec[j]), rep(1/k.vec[j], k.vec[j]))
      rho.implied[i,j] <- contord.F(margins, theta.vec[i])$cor[1,2] # implied correlation
  }
}
round(rho.implied, 4)
#
# graph for m=2, m=3 and m=5
op <- par()
par(mai=c(0.8,0.8,0.5,0.1),mgp=c(2.5,1,0))
plot(rho.latent, rho.implied[,1], xlab=expression(paste("latent correlation, ", rho[S])),
     ylab=expression(paste("implied correlation, ", Corr(X[1],X[2]))), ylim=c(0,1),
     pch=1, type="b",main="Discrete uniform margins",col="blue")
points(rho.latent, rho.implied[,2], type="b", pch=2,col="darkgreen")
points(rho.latent, rho.implied[,4], type="b", pch=3,col="red")
abline(0,1,lty=2)
abline(h=0,v=0)
legend(x = 0, y = 1,
       legend = c(
         bquote(m == .(k.vec[1])),
         bquote(m == .(k.vec[2])),
         bquote(m == .(k.vec[4]))
       ),
       pch = 1:3,
       text.col = c("blue","darkgreen","red"),
       col=c("blue","darkgreen","red"))
par(op)
# better (it takes a minute):
implied.unif <- Vectorize(function(rho,m)
{
  if(rho<1)
  {
  theta <- iRho(frankCopula(dim=2), rho)
  margins <- list(rep(1/m,m), rep(1/m,m))
  contord.F(margins, theta)$cor[2]
  } else
  {return(1)}
}
)
op <- par()
par(mai=c(0.8,0.8,0.1,0.1),mgp=c(2.5,1,0))
xlab <- expression(paste("latent correlation, ", rho[S]))
ylab <- expression(paste("implied correlation, ", Corr(X[1],X[2])))
plot(function(rho) implied.unif(rho, m=2), xlim=c(0,1),ylim=c(0,1), col="blue",
     xlab=xlab, ylab=ylab,n=500)
plot(function(rho) implied.unif(rho, m=3), xlim=c(0,1),col="darkgreen",add=TRUE,n=500)
plot(function(rho) implied.unif(rho, m=5), xlim=c(0,1),col="red",add=TRUE,n=500)
abline(0,1,lty=2)
abline(h=0,v=0)
points(0.3, implied.unif(0.3, 2), col="blue",pch=1)
points(0.5, implied.unif(0.5, 3), col="darkgreen",pch=2)
points(0.7, implied.unif(0.7, 5), col="red",pch=3)
legend(x = 0, y = 1,
       legend = c(
         expression(m == 2),
         expression(m == 3),
         expression(m == 5)
       ),
       pch = 1:3,
       text.col = c("blue","darkgreen","red"),
       col=c("blue","darkgreen","red"),
       bty="n")
abline(h=1)
abline(v=1)
par(op)
# -> Figure 3

# we now consider an increasing pattern
# for the probabilities of the ordinal margins
rho.implied.inc <- matrix(0, length(rho.latent), length(k.vec))
for(i in 1:length(theta.vec))
{
  for(j in 1:length(k.vec))
  {
    margins <- list((1:k.vec[j])/sum(1:k.vec[j]), (1:k.vec[j])/sum(1:k.vec[j]))
    rho.implied.inc[i,j] <- contord.F(margins, theta.vec[i])$cor[1,2] # implied correlation
  }
}
round(rho.implied.inc, 4)
rho.implied.inc <= rho.implied
#
#######################################################
###             OPTIMIZATION ROUTINE                ###
#   which finds the ordinal distribution maximizing   #
#      the implied rho given m and the latent rho     #
#######################################################
library(nloptr)
k.vec      <- 2:6      # n.of categories
rho.latent <- (1:9)/10  # latent correlations
theta.vec  <- sapply(rho.latent, function(rho) iRho(fc, rho)) # theta parameter
op <- par()
par(mfrow=c(length(theta.vec),length(k.vec)), mai=c(0.125,0.3,0.15,0), oma=c(0,3.5,0,0), xpd = NA)
set.seed(12345)
max.it <- 0
for(i in 1:length(theta.vec))
{
  for(j in 1:length(k.vec))
  {
    theta <- theta.vec[i]
    k <- k.vec[j]
    rho <- rho(frankCopula(theta))
    fn1 <- function(z){
      p <- exp(z)/sum(exp(z))
      margins <- list(p, p)
      s <- sign(theta)+(theta==0)
      -s*contord.F(margins, theta)$cor[1,2] # final correlation (with changed sign)
    }
    res <- nloptr(x0=rep(0,k), eval_f=fn1, opts=list(algorithm="NLOPT_LN_COBYLA",ftol_rel=1e-10,xtol_rel=1e-10, maxeval=1000))
    res$objective
    it.st <- 0
    while(!(res$status %in% c(1, 3, 5)))
    {
      res <- nloptr(x0=rep(0,k)+rnorm(k), eval_f=fn1,
          opts=list(algorithm="NLOPT_LN_COBYLA",ftol_rel=1e-4,xtol_rel=1e-4, maxeval=1000))
      it.st <- it.st + 1
    }
    max.it <- max(max.it,it.st)
    res$objective
    p <- exp(res$solution)/sum(exp(res$solution))
    p
    cat("rho_S=",rho,"m=",k,"prob=",p,"\n")
    if(which.max(p)>k/2) p <- rev(p)
    barplot(p, ylim=c(0,0.5))             # plotting the "optimal" distribution
    text(k*0.6+0.1, 0.45, sprintf("%.4f", -res$objective),pos=3)
    # writing the maximum correlation
    if(j==1) text(-1.5,0.125,substitute(list(rho[S]) == list(x),list(x = sprintf("%.1f", rho))),cex=1)
  }
}
par(op) # Figure 4
#
# when the number of categories is between 7 and 11
#
library(nloptr)
k.vec      <- 7:11       # n.of categories
rho.latent <- (1:9)/10  # latent correlations
theta.vec  <- sapply(rho.latent, function(rho) iRho(fc, rho)) # theta parameter
op <- par()
par(mfrow=c(length(theta.vec),length(k.vec)), mai=c(0.125,0.3,0.15,0), oma=c(0,3.5,0,0), xpd = NA)
set.seed(12345)
max.it <- 0
for(i in 1:length(theta.vec))
{
  for(j in 1:length(k.vec))
  {
    theta <- theta.vec[i]
    k <- k.vec[j]
    rho <- rho(frankCopula(theta))
    fn1 <- function(z){
      p <- exp(z)/sum(exp(z))
      margins <- list(p, p)
      s <- sign(theta)+(theta==0)
      -s*contord.F(margins, theta)$cor[1,2] # final correlation (with changed sign)
    }
    res <- nloptr(x0=rep(0,k), eval_f=fn1, opts=list(algorithm="NLOPT_LN_COBYLA",
                                    ftol_rel=1e-10,xtol_rel=1e-10, maxeval=1000))
    res$objective
    it.st <- 0
    while(!(res$status %in% c(1, 3, 5)))
    {
      res <- nloptr(x0=rep(0,k)+rnorm(k), eval_f=fn1,
          opts=list(algorithm="NLOPT_LN_COBYLA",ftol_rel=1e-4,xtol_rel=1e-4, maxeval=1000))
      it.st <- it.st + 1
    }
    max.it <- max(max.it,it.st)
    res$objective
    p <- exp(res$solution)/sum(exp(res$solution))
    p
    cat("rho_S=",rho,"m=",k,"prob=",p,"\n")
    if(which.max(p)>k/2) p <- rev(p)
    barplot(p, ylim=c(0,0.25))             # plotting the "optimal" distribution
    text(k*0.6+0.1, 0.15, sprintf("%.4f", -res$objective),pos=3)
    # writing the maximum correlation
    if(j==1) text(-6,0.0625,substitute(list(rho[S]) == list(x),list(x = sprintf("%.1f", rho))),cex=1)
  }
}
par(op) # Figure 5

# the optimization problem
# with two non-identical margins
# but with the same support
library(nloptr)
k.vec      <- 2:6      # n.of categories
rho.latent <- (1:9)/10  # latent correlations
theta.vec  <- sapply(rho.latent, function(rho) iRho(fc, rho)) # theta parameter
set.seed(12345)
max.it <- 0
for(i in 1:length(theta.vec))
{
  for(j in 1:length(k.vec))
  {
    theta <- theta.vec[i]
    k <- k.vec[j]
    rho <- rho(frankCopula(theta))
    fn1 <- function(z){
      h <- length(z)
      m <- h/2
      p <- exp(z[1:m])/sum(exp(z[1:m]))
      q <- exp(z[(m+1):h])/sum(exp(z[(m+1):h]))
      margins <- list(p, q)
      s <- sign(theta)+(theta==0)
      -s*contord.F(margins, theta)$cor[1,2] # final correlation (with changed sign)
    }
    res <- nloptr(x0=rep(0,2*k), eval_f=fn1,
        opts=list(algorithm="NLOPT_LN_COBYLA",ftol_rel=1e-10,xtol_rel=1e-10, maxeval=1000))
    res$objective
    it.st <- 0
    while(!(res$status %in% c(1, 3, 5)))
    {
      res <- nloptr(x0=rep(0,2*k)+rnorm(2*k), eval_f=fn1,
         opts=list(algorithm="NLOPT_LN_COBYLA",ftol_rel=1e-4,xtol_rel=1e-4, maxeval=1000))
      it.st <- it.st + 1
    }
    max.it <- max(max.it,it.st)
    res$objective
    p <- exp(res$solution[1:k])/sum(exp(res$solution[1:k]))
    p
    q <- exp(res$solution[(k+1):(2*k)])/sum(exp(res$solution[(k+1):(2*k)]))
    q
    cat("rho_S=",rho,"m=",k,"implied rho=",-res$objective,"prob X1=",p,"prob X2=",q,"\n")
  }
}

################################################################################
##### C O M P A R I S O N   b e t w e e n    F R AN K   A N D   G A U S S ######
############## D I S C R E T I Z E D   D I S T R I B U T I O N S ###############
################################################################################

plot_diff_matrix <- function(D, title = "") {
  D <- as.matrix(D)
  stopifnot(nrow(D) == ncol(D))  # must be square

  n <- nrow(D)

  # Codification by color: -1 (negative), 0 (zero), 1 (positive)
  Z <- matrix(0, n, n)
  Z[D > 0] <-  1
  Z[D < 0] <- -1
  # Inverting row in order to have 1 at the top
  op <- par(mgp = c(1, 0.3, 0))
  image(1:n, 1:n, t(Z[n:1, ]),
        col = c("lightblue", "white", "salmon"),
        axes = FALSE,
        xlab = "", ylab = "",
        breaks = c(-1.5, -0.5, 0.5, 1.5),
        main = title)

  axis(3, at = 1:n, tick=FALSE)
  axis(2, at = 1:n, labels = n:1, tick=FALSE, las=2)  # 1 in alto
  box()
  # Only + e −
  S <- ifelse(D > 0, "+", ifelse(D < 0, "−", ""))

  for (i in 1:n)
    for (j in 1:n)
      if (S[i, j] != "")
        text(j, n - i + 1, S[i, j], cex = 1.8)
}

#################################################################################
# computation of total variation distance and plot of signs of cell differences #
#################################################################################
par(mfrow=c(9,1), mai=c(0.125,0.3,0.15,0.125), oma=c(0,0,0,0), xpd = NA)
rhoS <- (1:9)/10
m    <-  5
TV <- matrix(0, length(rhoS), length(m))
diagM <- matrix(0, length(rhoS), length(m))
for(i in 1:length(rhoS))
{
  for(j in 1:length(m))
  {
    h <- floor(m[j]/2)-1
    s <- c(2^(0:h),2^(h+1),2^(h:0))
    s <- s/sum(s)
    margin1 <- margin2 <- s                     # symmetric unimodal
    #margin1 <- margin2 <- rep(1/m[j], m[j])    # uniform
    #margin1 <- margin2 <- (1:m[j])/sum(1:m[j]) # increasing
    theta <- iRho(frankCopula(dim=2), rhoS[i])
    rhoN  <- iRho(normalCopula(dim=2), rhoS[i])
    P <- contord(list(cumsum(margin1)[-m[j]], cumsum(margin2)[-m[j]]), matrix(c(1,rhoN,rhoN,1),2,2), prob=TRUE)$pij
    Q <- contord.F(list(margin1, margin2), theta)$pmf
    TV[i,j] <- TVdist(P,Q)
    diagM[i,j] <- sum(diag(P)) - sum(diag(Q))
    plot_diff_matrix(Q-P,title="")
    text(-0.75,2,substitute(list(rho[S]) == list(x),list(x = sprintf("%.1f", rhoS[i]))),cex=1)
  }
}
# -> Figure 6
TV
# -> Table 3

################################################################################
#                    EXAMPLES OF REAL DATA ANALYSIS                            #
################################################################################
# data set taken from L. Kolbe, F. Oort, and S. Jak                            #
# Bivariate distributions underlying responses to ordinal variables            #
# Psych, 3(4):562–578, 2021                                                    #
################################################################################
freq <- matrix(c(67,41,34,35,24,
                 15,28,48,22,10,
                 16,30,39,34,11,
                 8,4,11,28,11,
                 3,2,1,5,9),5,5)
n <- sum(freq)
tab <- as.table(freq)
X1 <- rep(1:5, times = rowSums(tab))
X2 <- unlist(lapply(1:5, function(i) rep(1:5, times = tab[i, ])))
X <- cbind(X1, X2)
cor(X)
res <- est.Fd(X)
res
param <- res$estimates
ell.Fd(param, X) # -1592.893
tab.est.F <- contord.F(margins=list(param[1:5],param[6:10]), param[11])$pmf*n
sum((tab.est.F-tab)^2/tab.est.F) # 53.06865
# discretized normal:
res.norm <- estcontord(X, "full", normal=TRUE)
res.norm <- res.norm[-2]
res.norm[2:11] <- log(res.norm[2:11])
-logLfull(res.norm, X) # -1593.006
rho<-res.norm[1]
margin.1<-exp(res.norm[2:6])/sum(exp(res.norm[2:6]))
margin.2<-exp(res.norm[7:11])/sum(exp(res.norm[7:11]))
tab.est.N<-contord(list(cumsum(margin.1)[-5],cumsum(margin.2)[-5]),
                   Sigma=matrix(c(1,rho,rho,1),2,2),df=Inf,prob=TRUE)$pij*n
tab.est.N
sum((tab.est.N-tab)^2/tab.est.N) # 53.3537
# rather bad fit for both models

################################################################################
#                           ISSP2000, Section 4.1                              #
################################################################################
library(prefmod)
data <- issp2000
X <- data[data$CNTRY==1, c(4,6)]
n <-dim(X)[1]
cor(X)
x <- matrix(as.numeric(table(X)), nrow = 5, ncol = 5)
res <- est.Fd(X)
res
ell.Fd(res$estimates, X) # -2050.506
param <- res$estimates
tab.est.F <- contord.F(margins=list(param[1:5], param[6:10]), param[11])$pmf*n
TV.obs <- TVdist(x/n, tab.est.F/n) # distance
prob.F    <- contord.F(margins=list(param[1:5], param[6:10]), param[11])$pmf
Chi.obs   <- sum((x-tab.est.F)^2/tab.est.F)
log0 <- function(x) ifelse(x==0,0,log(x))
G2.obs  <- 2*sum(x*log0(x/tab.est.F))
1-pchisq(Chi.obs, 25-4-4-1-1)
1-pchisq(G2.obs, 25-4-4-1-1)

# bootstrap
set.seed(12345)
N <- 500
Chi  <- numeric(N)
G2 <- numeric(N)
TV <- numeric(N)
for(i in 1:N)
{
  XMC0 <- ordsample.F(n=n, margins=list(param[1:5],param[6:10]), param[11])
  tMC0 <- table(as.data.frame(XMC0))
  r <- nrow(tMC0)
  c <- ncol(tMC0)
  res.b <- est.Fd(XMC0)
  param.b <- res.b$estimates
  tab.est.Fb <- contord.F(margins=list(param.b[1:r], param.b[(r+1):(r+c)]), param.b[r+c+1])$pmf*n
  Chi[i]  <- sum((table(as.data.frame(XMC0))-tab.est.Fb)^2/tab.est.Fb)
  G2[i]   <- 2*sum(tMC0*log0(tMC0/tab.est.Fb))
  TV[i] <- TVdist(tMC0/n, tab.est.Fb/n)
  print(i)
}
mean(Chi>=Chi.obs)
mean(G2>=G2.obs)
mean(TV>=TV.obs)

sum((x-tab.est.F)^2/tab.est.F)
res.norm <- estcontord(X, "full", normal=TRUE)
res.norm<-res.norm[-2]
res.norm[2:11]<-log(res.norm[2:11])
-logLfull(res.norm, X) # -3701.656
margin.1<-exp(res.norm[2:6])/sum(exp(res.norm[2:6]))
margin.2<-exp(res.norm[7:11])/sum(exp(res.norm[7:11]))
tab.est.N<-contord(list(cumsum(margin.1)[-5],cumsum(margin.2)[-5]),
                   Sigma=matrix(c(1,rho,rho,1),2,2),df=Inf,prob=TRUE)$pij*n
tab.est.N
sum((x-tab.est.N)^2/tab.est.N)

# # NOT RUN (IT TAKES SEVERAL MINUTES)
# # considering all the ordinal variables in the dataset
# # d=6
# x <- data[data$CNTRY==1, 1:6]
# sol <- est.Fd(x)
# # Transform each row in a unique string
# keys <- apply(x, 1, paste, collapse = "_")
# # Counting frequencies
# tab <- sort(table(keys), decreasing = TRUE)
# # Maximum frequency
# max_freq <- tab[1]
# # most frequent sextuple
# modes <- names(tab)[tab == max_freq]
# max_freq
# modes
# tab[2] # second most frequent sextuple
# margins <- list(sol$estimates[1:5],sol$estimates[6:10],sol$estimates[11:15],
# sol$estimates[16:20],sol$estimates[21:25],sol$estimates[26:30])
# P <- contord.F(margins, theta=sol$estimates[31], corr=TRUE)$pmf
# index <- which(P == max(P), arr.ind = TRUE)
# index
# P[index]
# P[1,1,1,1,1,1]

################################################################################
#                            Analysis of real data                             #
#                                Premarital sex                                #
#                                     and                                      #
#                            Teenage birth control                             #
#                                 Section 4.2                                  #
################################################################################
# Example from Agresti,
# An Introduction to Categorical Data Analysis (2018)
# table 7.10, p.214
tab <- matrix(c(81,24,18,36,68,26,41,57,60,29,74,161,38,14,42,157), 4, 4)
n <- sum(tab)
x <- matrix(NA, n, 2)
# building the bivariate sample as an n times 2 matrix
k <- 1
for (i in 1:nrow(tab)) {
  for (j in 1:ncol(tab)) {
    f <- tab[i, j]
    if (f > 0) {
      x[k:(k+f-1), ] <- cbind(rep(i, f), rep(j, f))
      k <- k + f
    }
  }
}
res.agresti <- est.Fd(x)
res.agresti
param <- res.agresti$estimates
tab.est.F <- contord.F(margins=list(param[1:4], param[5:8]), param[9])$pmf*n
round(tab.est.F,1)
TV.obs <- TVdist(tab/n, tab.est.F/n) # distance
prob.F    <- contord.F(margins=list(param[1:4], param[5:8]), param[9])$pmf
Chi.obs   <- sum((tab-tab.est.F)^2/tab.est.F)
log0 <- function(x) ifelse(x==0,0,log(x))
G2.obs  <- 2*sum(tab*log0(tab/tab.est.F))
1-pchisq(Chi.obs, 4*4-2*3-1-1)

# bivariate discretized normal
res.N <- estcontord(x, "full", normal=TRUE)
logLfull(res.N[c(1,3:10)], x)
margin1 <- res.N[3:6]
margin2 <- res.N[7:10]
Sigma   <- matrix(c(1, res.N[1], res.N[1], 1), 2, 2)
prob.N  <- contord(list(cumsum(margin1)[-4], cumsum(margin2)[-4]), Sigma, df=Inf, prob=TRUE)
n*prob.N$pij

# # NOT RUN
# # parametric bootstrap for deriving a more reliable p-value
# # for the chi-square and G-square statistics
# set.seed(12345)
# N <- 500
# Chi  <- numeric(N)
# G2   <- numeric(N)
# TV   <- numeric(N)
# for(i in 1:N)
# {
#   XMC0 <- ordsample.F(n=n, margins=list(param[1:4], param[5:8]), param[9])
#   tMC0 <- table(as.data.frame(XMC0))
#   r <- nrow(tMC0)
#   c <- ncol(tMC0)
#   res.b <- est.Fd(XMC0)
#   param.b <- res.b$estimates
#   tab.est.Fb <- contord.F(margins=list(param.b[1:r], param.b[(r+1):(r+c)]), param.b[r+c+1])$pmf*n
#   Chi[i]  <- sum((tMC0-tab.est.Fb)^2/tab.est.Fb)
#   G2[i]   <- 2*sum(tMC0*log0(tMC0/tab.est.Fb))
#   print(i)
# }
# mean(Chi>=Chi.obs)
# mean(G2>G2.obs)

################################################################################
#                         S I M U L A T I O N   P L A N                        #
#             for assessing the empirical distribution of theta.hat            #
#                                  (Section 3.2)                               #
################################################################################
# NOT RUN
# it takes some minutes
N <- 1000  # Monte Carlo runs
n <- 1000   # sample size (200 or 1000)
# we consider three "shapes" for the discrete distributions
# uniform, symmetric inverted-U shaped, increasing
# the first margin has three categories, the second five
mlab    <- "uniform"
margins <- list(rep(1/3,3), rep(1/5,5))
mlab    <- "symmetric"
margins <- list(c(0.25,0.5,0.25), c(1,2,4,2,1)/10)
mlab    <-"increasing"
margins <- list((1:3)/6, (1:5)/15)
rhoS    <- 0.8
theta   <- iRho(frankCopula(dim=2), rhoS)
theta.hat <- numeric(N)

if (rhoS == 0.2) {
  ylim <- c(-0.6, 3.2)
} else if (rhoS == 0.5) {
  ylim <- c(1.4, 6)
} else {
  ylim <- c(4, 14)
}

set.seed(12345)
for(i in 1:N)
{
  x <- ordsample.F(n, margins, theta)
  res <- est.Fd(x)
  theta.hat[i] <- res$estimates[length(res$estimates)]
  print(i)
}
op<-par()
par(mai=c(0.2,0.5,0.2,0.2))
boxplot(theta.hat, ylim=ylim)
abline(h=theta)
legend("topleft",
       legend = c(
         bquote(theta == .(round(theta, 3))),
         mlab
       ),
       bty = "n")
legend("topright",
       legend = c(
         paste0("mean = ", round(mean(theta.hat), 3)),
         paste0("sd = ", round(sd(theta.hat), 3)),
	   paste0("cv = ", round(sd(theta.hat)/mean(theta.hat), 3))
       ),
       bty = "n")
name <- paste("theta",round(theta,1),"rhoS",rhoS,"n",n,mlab)
sd(theta.hat)
par(op)
theta.hat1000 <- theta.hat
save(theta.hat1000, file=paste(name,".Rdata"))

################################################################################
#                        Additional MC simulation study                        #
#                              Frank latent model                              #
#                              with d=6 variables                              #
#                        (Section 3.2, Tables 4 and 5)                         #
################################################################################
d <- 6
# with different margins
margins <- list(rep(1/3, 3), rep(1/4, 4), rep(1/5, 5), c(1,2,1)/4, c(1,2,3)/6, c(3,2,1)/6)
# and theta=3
theta <- 3
contord.F(margins, theta)
n <- 200
N <- 1000
theta.hat    <- numeric(N)
se.theta.hat <- numeric(N)
theta.hat.full    <- numeric(N)
se.theta.hat.full <- numeric(N)
t1 <- Sys.time()
set.seed(12345)
for(i in 1:N)
{
x <- ordsample.F(n, margins, theta)
res <- est.Fd(x, method="2-step")
theta.hat[i] <- res$estimate
se.theta.hat[i] <- res$se
print(i)
}
t2 <- Sys.time()
t2-t1
mean(theta.hat)
sd(theta.hat)
mean(se.theta.hat)
t3 <- Sys.time()
set.seed(12345)
for(i in 1:N)
{
  x <- ordsample.F(n, margins, theta)
  res <- est.Fd(x)
  theta.hat.full[i]    <- res$estimates["theta"]
  se.theta.hat.full[i] <- res$std.errors["theta"]
  print(i)
}
t4 <- Sys.time()
t4-t3
mean(theta.hat.full)
sd(theta.hat.full)
mean(se.theta.hat.full)

as.numeric((t2-t1)/N, units = "secs")
as.numeric((t4-t3)/N, units = "secs")


install.packages("car")
library(car)
op<-par()
par(mar = c(5, 5, 1, 1) + 0.1)
scatterplot(theta.hat, theta.hat.full,            # Data
            pch = 1,        # Symbol of the points
            col = 1,         # Color of the points
            smooth = FALSE,  # Remove smooth estimate
            regLine = FALSE,  # Remove linear estimate
            xlab=expression(hat(theta)[two-step]),
            ylab=expression(hat(theta)[full]))
par(op)
# -> Figure 8

filename <- paste("Frank add sim N",N,"n",n,"d",d,"theta",theta)
filename <- paste(filename,"Rdata",sep=".")
save.image(file = filename)
