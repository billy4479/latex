#import "lib/template.typ": *
#import "lib/theorem.typ": *
#import "lib/algorithm.typ": *
#import "lib/utils.typ": *
#import "@preview/lovelace:0.3.1": *

#show: template.with(
  titleString: "Numerical Linear Algebra",
  author: "Giacomo Ellero",
  date: "A.Y. 2026/2027",
  font: "",
)

#show: thm-init
#show: alg-init

#let ub(it) = $upright(bold(it))$
#let vv(it) = math.bold(it)

= Preliminaries

We note $vv(x)$ a vector in $RR^n$, with $vv(0), vv(1)$ being the all zero and all 1 vectors,
while $vv(e)_i$ are the vectors which form the canonical base of $RR^n$.

Recall that a matrix is *nilpotent* if $exists k in NN$ such that $bold(A)^k = bold(0)$.

Also
$
  A^(-T) := (A^T)^(-1) = (A^(-1))^T \
  (A B)^(-1) = B^(-1) A^(-1)
$

Recall that if there exists $vv(x) != vv(0)$ such that $bold(A) vv(x) = vv(0)$, then $bold(A)$ is
singular and cannot be inverted.

Orthogonal matrices have that $bold(A)^T = bold(A)^(-1)$.

Upper and lower triangular matrices are non-singular (i.e. invertible) iff the diagonal elements are
all different from 0. They are called unitary if the diagonals are all 1.

== LU factorization
$
  P A = L U
$
for $A$ non-singular, $P$ a permutation, $U$ upper triangular, $L$ unit lower triangular.

== Cholesky decomposition
If $A$ is symmetric and positive definite ($vv(x)^T A vv(x) > 0 forall vv(x) != vv(0)$), then it can be decomposed
by
$
  A = L^T L
$
where $L$ is the same lower triangular matrix with positive entries on the diagonal.

== QR decomposition

If $A$ is non-singular then
$
  A = Q R
$
where $Q$ is orthogonal and $R$ is upper triangular.

== Determinant

Never compute it unless triangular, in which case $det(A)$ is the product of the diagonal.

Use LU factorization to compute determinant: $det(A) = plus.minus det(U)$ (since $L$ is unitary).
The $plus.minus$ comes from the permutation matrix.

== Sparse matrices

A matrix is sparse if the number of non-zero entries is $O(n)$.

= Iterative methods for sparse linear systems

== Introduction

We want to solve a linear system
$
  A vv(x) = vv(b)
$
where $A$ is non-singular and sparse.

We could work by directly manipulating $A$ and get a _direct solution_, but this is not a good fit
for us: usually these methods are $bigO(n^3)$ and do not preserve the sparsity of $A$.

We therefore introduce iterative methods.

#definition(title: "Iterative method")[
  This is a method to compute a sequence $vv(x)^((1)), ..., vv(x)^((k))$ starting from $vv(x)^((0))$ such that
  $
    lim_(k -> oo) vv(x)^((k)) = vv(x)
  $
  independently from $vv(x)^((0))$, where $vv(x)$ is the desired result.
]

In real computations we cannot have an infinite number of steps, therefore we use a stopping
criterion, which tells us when our solution is good enough.

== Linear iterative methods

We study the class of iterative methods such that
$
  vv(x)^((k + 1)) = B vv(x)^((k)) + vv(f)
$
where $B$ is the _iteration matrix_ and, together with $vv(f)$, fully specify the method.

The first criterion to chose these parameters is *consistency*: if $vv(x)^((k))$ is the correct
solution, then $vv(x)^((k + 1)) = vv(x)^((k))$. This gives
$
  vv(x) = B vv(x) + vv(f) ==> vv(f) = (I - B) vv(x) = (I - B) A^(-1) vv(b)
$

This condition is necessary, but not sufficient. On top of consistency, we need *convergence*.

#definition(title: "Error")[
  At step $k$ we define the error as
  $
    vv(e)^((k)) = vv(x) - vv(x)^((k))
  $
  where $vv(x)$ is the true solution.
]

For convergence to hold we want the norm of the error to go to zero as $k -> oo$. This in practice
gives
$
  norm(vv(e)^(k + 1)) & = norm(vv(x) - vv(x)^(k + 1)) \
                  & = norm(vv(x) - B vv(x)^(k) - vv(f)) \
                  & = norm(vv(x) - B vv(x)^(k) - (I - B)vv(x)) \
                  & = norm(B vv(e)^((k))) \
                  & <= norm(B) norm(vv(e)^((k)))
$
Therefore, for the error to go to zero we need $norm(B) < 1$. This is a sufficient condition for
convergence.

In practice, to make sure $norm(B) < 1$ we set its spectral radius $rho(B) > 1$.

#definition(title: "Spectral radius")[
  The spectral radius $rho(B)$ is defined as
  $
    rho(B) = max_j abs(lambda_j (B))
  $
  where $lambda_j (B)$ are the eigenvalues of $B$.
]

#proposition[
  The spectral radius is the smallest of the induced norms.
]

=== Stopping criterion

Ideally we want to stop when $norm(vv(x) - vv(x)^((k)))/norm(vv(x)) <= epsilon$, however we don't know the true
solution $vv(x)$.

#definition(title: "Conditioning number")[
  Given a matrix $A$, its conditioning number is defined as
  $
    kappa(A) = norm(A) dot.op norm(A^(-1))
  $
]

A method which can be used in practice is
$
  norm(vv(x) - vv(x)^((k)))/norm(vv(x)) <= kappa(A) norm(vv(r)^((k)))/norm(vv(b))
  ==> kappa(A) norm(vv(r)^((k)))/norm(vv(b)) < epsilon
$
or another one
$
  norm(vv(delta)^((k))):= norm(vv(x)^((k + 1)) - vv(x)^((k))) <= epsilon
$
and it can be shown that
$
  norm(vv(e)^((k))) <= 1 / (1- rho(B)) norm(vv(delta)^((k)))
$

=== Preconditioning

We introduce an SPD matrix $P^(-1)$ and we solve
$
  P^(-1/2) A P^(-1/2) vv(z) = P^(-1/2) vv(b)
$
Then $vv(x) = P^(1/2) vv(z)$.

We try to chose $P$ such that $kappa(P^(-1/2) A P^(-1/2)) << kappa(A)$.

$
  vv(x)^((k + 1)) = vv(x)^((k)) + P^(-1) vv(r)^((k))
$
where $vv(r)^((k)) = vv(b) - A vv(x)^((k))$ and $P$ is the preconditioner of the residual. In practice we never
invert $P$, we solve for $P vv(z)^((k)) = vv(r)^((k))$.

We can also write this in matrix form:
$
  A = P - N
$
This also preserves sparsity

== Richardson method

$P^(-1) vv(r)^((k))$ gives us the direction of the residual. We can however also add some coefficients
$alpha_k$ which give us the magnitude of this direction vector.

This is called Richardson method. In particular if $alpha_k = alpha forall k$ this is the static
variant, otherwise that's the dynamic version. In particular, if $A$ is SPD (symmetric and positive
definite), there is a good method to pick these $alpha_k$.

=== Choosing $alpha$

We want
$
  B alpha = I - alpha P^(-1) A
$
such that the spectral radius of $B alpha$ is as smaller that $1$. The role of $alpha$ is to push
back the eigenvalues towards $0$.

#theorem(title: [$P = I, A "SPD"$])[
  The method converges if and only if
  $
    0 < alpha < 2/(lambda_"max" (A))
  $

  The optimal is
  $
    alpha = 2/(lambda_"min" (A) + lambda_"max" (A))
  $
]

#theorem(title: [$P != I, P "SPD", A "SPD"$])[
  The method converges if and only if
  $
    0 < alpha < 2/(lambda_"max" (P^(-1) A))
  $

  The optimal is
  $
    alpha = 2/(lambda_"min" (P^(-1) A) + lambda_"max" (P^(-1) A))
  $
]<thm:rich-P-spd>

#remark[
  Let $A, B$ be SPD matrices. Then $A B$ is not guaranteed to be SPD.
]

#remark[
  Let $A$ be an SPD matrix. Then, there exists an unique matrix $A^(1/2)$ SPD such that
  $(A^(1/2))^2 = A$.
]

#remark[
  Let $A, B^(-1)$ be SPD matrices. Then $B^(-1/2) A B^(1/2) = B^(-1) A$ is also SPD.
]


This means that in @thm:rich-P-spd $lambda_"max"$ could be complex. Note that we do not want to
compute eigenvalues: this is a non-linear problem, which is very expensive to solve, especially
because we are starting from a linear problem.

We can now exploit the fact that $A$ is SPD. This means that $Phi(vv(y)) = 1/2 vv(y)^T A vv(y) - vv(y)^T vv(b)$ (call it
the _energy function_) is convex, and the unique minimum is given by $grad Phi(vv(y)) = vv(0) = A vv(y) - vv(b)$,
which is the solution of our system.

This means that we want to set the residual to
$
  vv(r)^((k)) = - grad Phi(vv(x)^((k))) = vv(b) - A vv(x)^((k))
$

It turns out that two consecutive residuals are always orthogonal. This can be proven by just
multiplying $vv(r)^((k))$ with $vv(r)^((k + 1))$.

Then our problem reduces to
$
  vv(x)^((k + 1)) = vv(x)^((k)) - alpha_k grad Phi(vv(x)^((k)))
$

To compute $alpha_k$ we can just expand $Phi(vv(x)^((k + 1)))$ and look at it as a function of $alpha_k$
and looking for its minimizer. Doing the algebra, we find out that $Phi(vv(x)^((k + 1)))$ is a 1
dimensional parabola in $alpha_k$, which is is trivial to minimize.

This gives us
$
  alpha_k = ((vv(r)^((k)))^T vv(r)^((k)))/((vv(r)^((k)))^T A vv(r)^((k)))
$

This gives us a full algorithm:
- Compute $alpha_k$ as above $--> bigO(n)$ if $A$ is sparse.
- $vv(x)^((k + 1)) = vv(x)^((k)) + alpha_k vv(r)^((k)) --> bigO(n)$.
- $vv(r)^((k + 1)) = vv(b) - A vv(x)^((k + 1)) = vv(b) - A(vv(x)^((k)) + alpha_k vv(r)^((k))) = vv(r)^((k)) - alpha_k A vv(r)^((k))
  --> bigO(n)$. Note that $A vv(r)^((k))$ has already been computed when computing $alpha_k$, if we
  reuse it we can save a matrix-vector multiplication.

=== Convergence

This method, in precise arithmetic, always converges.

#definition(title: "Matrix-induced norm")[
  Let $A$ be an SPD matrix. For a vector $vv(z)$ we define its norm induced by $A$ as
  $
    norm(vv(z))_A = sqrt(vv(z)^T A vv(z)) quad forall vv(z) in RR^n
  $
]


The speed of convergence depends on $A$:
$
  norm(vv(e)^((k + 1)))_A <= (kappa(A) - 1)/(kappa(A) + 1) norm(vv(e)^((k)))_A ==>
  norm(vv(e)^((k + 1)))_A <= ((kappa(A) - 1)/(kappa(A) + 1))^k norm(vv(e)^((0)))_A
$

=== Adding back the preconditioner

Now let $P != I$
$
  A vv(x) = vv(p) ==> P^(1/2) A P^(-1/2) vv(y) = P^(1/2) vv(b) quad "with" vv(y) = P^(1/2) vv(x)
$
where the bound for the error is

$
  norm(vv(e)^((k + 1)))_A <= [(kappa(P^(1/2) A P^(-1/2)) - 1)/(kappa(P^(1/2) A P^(-1/2)) + 1)]
  norm(vv(e)^((k)))_A
$

This has the issue that, in theory, we would need both to compute $P^(1/2)$ and invert it: both very
expensive operations. However, in practice, we can avoid fully materializing either $P^(1/2)$ or its
inverse: we just need the effect of $P$ on the residual.

Indeed, we can define the algorithm as

#algorithm(title: "Preconditioned Richardson method")[
  + Given $vv(x)^((0))$
  + Compute $vv(r)^((0)) = vv(b) - A vv(x)^((0))$
  + *While* `Stopping condition`
    + Solve $P vv(z)^((k)) = vv(r)^((k))$ for $vv(z)^((k))$
    + Compute $alpha_k = ((vv(z)^((k)))^T vv(r)^((k)))/((vv(z)^((k)))^T A vv(z)^((k)))$
    + Update $vv(x)^((k + 1)) = vv(x)^((k)) + alpha vv(z)^((k))$
    + Update $vv(r)^((k + 1)) = vv(r)^((k)) - alpha_k A vv(z)^((k))$
  + *End*
]

This gives us a tradeoff: a $P$ which is very good at minimizing the error might be very expensive
to compute, since at every iteration we need to solve a linear system involving $P$. We usually
choose $P$ such that it has a good structure and the system can be computed quickly.

== Conjugate gradient method

We now ask whether the residual is actually the best direction to follow. We start by relaxing this
assumption and see what we can get.

This relaxation comes from the idea that maybe I can look at the previous residuals.

#definition(title: [$A$-orthogonal])[
  Let $A$ be a SPD matrix and $vv(d)^((0)), ..., vv(d)^((k)) in RR^n$. We say that $vv(d)^((k+1))$ is
  $A$-orthogonal (or $A$-conjugate) to all the previous directions if
  $
    (vv(d)^((k+1)), vv(d)^((j)))_A := (vv(d)^((k+1)))^T A vv(d)^((j)) = 0 quad forall j <= k
  $
]

We try to impose that our new sequence of directions $vv(d)^((k))$, which we use in place of the
residuals, to be $A$-orthogonal to each other.

This fixes the issue we saw in the gradient method where each update was orthogonal just to the
preceding one, leading to a zig-zag pattern.

#theorem(title: "Conjugate gradient method error")[
  $
    norm(vv(e)^((k)))_A <= (2 c^k)/(1 + c^(2k)) norm(vv(e)^((0)))_A quad "with" c = (sqrt(kappa(A)) - 1)/(sqrt(kappa(A))+1)
  $
]

This also has the advantage that $vv(d)^((k))$ form a basis of $RR^n$, which means that the method
converges in at most $n$ steps.

The problem is then reframed as "finding iteratively a base to $RR^n$ in order to represent $vv(x)$".

At each step we need to find $vv(d)^((k+1))$ given the current residuals and the previous direction. The
next direction is given by
$
  vv(d)^((k + 1)) = vv(r)^((k + 1)) - beta_k vv(d)^((k))
$<eq:cg-short-recurrence>
and to compute $beta_k$ we impose that
$
  (vv(r)^((k+1)) - beta vv(d)^((k)))^T A vv(d)^((k)) = 0 <==>
  beta_k = ((vv(r)^((k+1)))^T A vv(d)^((k)))/((vv(d)^((k)))^T A vv(d)^((k)))
$
we will see later that this is enough to impose $A$-orthogonality across all previous directions as
well.


#algorithm(title: "Preconditioned conjugate gradient method")[
  + Given $vv(x)^((0))$.
  + Compute $vv(r)^((0)) = vv(b) - A vv(x)^((0))$.
  + Solve $P vv(z)^((0)) = vv(r)^((0))$ for $vv(z)^((0))$.
  + Set $vv(d)^((0)) = vv(z)^((0))$.
  + *While* (`Stopping criterion`):
    + Compute
      $ alpha_k = ((vv(z)^((k)))^T vv(r)^((k)))/((vv(d)^((k)))^T A vv(d)^((k))) $
    + Compute $vv(x)^((k+1)) = vv(x)^((k)) + alpha_k vv(d)^((k))$.
    + Compute $vv(r)^((k+1)) = vv(r)^((k)) - alpha_k A vv(d)^((k))$.
    + Solve $P vv(z)^((k + 1)) = vv(r)^((k+1))$ for $vv(z)^((k+1))$.
    + Compute
      $ beta_k = ((A vv(d)^((k)))^T vv(z)^((k+1)))/((vv(d)^((k)))^T A vv(d)^((k))) $
    + Set $vv(d)^((k+1)) = vv(z)^((k+1)) - beta_k vv(d)^((k))$.
  + *End*
]<alg:cg>

#proposition[
  Let $A in RR^(n times n)$ be an SPD matrix, choose $vv(x)^((0)) in RR^n$ arbitrarily and compute
  $vv(r)^((0)) = vv(b) - A vv(x)^((0))$. By running @alg:cg in exact arithmetic, at each $k$, the vectors
  generated up to $k + 1$ satisfy:
  + *Full conjugacy of directions*: $(vv(d)^((i)))^T A vv(d)^((j)) = 0$ for all $i != j$ and $i,j <= k+1$.
  + *Full orthogonality of residuals*: $(vv(r)^((i)))^T vv(r)^((j)) = 0$ for all $i != j$ and $i,j <= k+1$.
  + *Common growing subspace*: $"span"{vv(d)^((0)), ..., vv(d)^((k+1))} = "span"{vv(r)^((0)), ..., vv(r)^((k+1))}$.
  + *Short recurrence*: each $vv(d)^((k+1))$ is build only from @eq:cg-short-recurrence, no earlier
    vector needs to be read.
]
#proof[Skip.]

#remark[
  These properties hold for plain CG ($P = I$). When $P != I$ they hold in the transformed space:
  the residuals are orthogonal with respect to $P^(-1)$, i.e. $(vv(r)^((i)))^T P^(-1) vv(r)^((j)) = 0$
  for all $i != j$.
]

== Krylov space methods

Consider the Richardson method with $alpha=1$. Can write
$
  r^((k+1)) & = vv(b) - A vv(x)^((k + 1)) = vv(b) - A (vv(x)^((k)) + vv(r)^((k))) \
            & = vv(b) - A vv(x)^((k)) - A vv(r)^((k)) = vv(r)^((k)) - A vv(r)^((k))
$
Similar arguments can be made for all methods we discussed so far. This means that $vv(r)^((k + 1))$ is
a linear polynomial of $vv(r)^((k))$.

This means we can can recursively write each $vv(r)^((k))$. Then the residuals lie on
$
  vv(x)^((0)) + "span"{ vv(r)^((0)), A vv(r)^((0)), ..., A^(k-1) vv(r)^((0)) }
$
where the space spanned by this vectors is a Krylov space.

#definition(title: [Krylov space])[
  The $k$-th Krylov space generated by $A$ from $y != vv(0)$ is
  $
    cal(K)_k (A, vv(y)) := "span"(vv(y), A vv(y), ..., A^(k-1) vv(y))
  $
  and $cal(K)_1 subset.eq cal(K)_2 subset.eq ...$.
]

#lemma(title: [Existence of the grade $nu$])[
  There exists a positive integer $nu$ such that
  $
    dim(cal(K)_s (A, vv(y))) = cases(
      s quad & "if"s <= nu,
      nu quad & "if"s >= nu,
    )
  $
]
#proof[Skip.]

#lemma(title: [Characterization of the grade])[
  The grade $nu$ is characterized by
  $
    nu(vv(y), A) = min {s : A^(-1) vv(y) in cal(K)_s (A, vv(y))}
  $
]
#proof[Skip.]

Given these two lemmas we can conclude that, since the exact solution $vv(x)$ of the system is defined
as $vv(x) = vv(x)^((0)) + A^(-1) vv(r)^((0))$, we have
$
  vv(x) in vv(x)^((0)) + cal(K)_nu (A, vv(r)^((0)))
$

== Non symmetric systems

To solve non symmetric systems we still use Krylov space solvers, however the theory is not as
advanced.

=== Biconjugate gradient method

This is an extension of the conjugate gradient method for non-symmetric matrices.

Let the dual problem be
$
  vv(x)^T A^T = vv(b)^T
$
and look at the Krylov space generated by the dual and its shadow residuals (i.e. the residuals of
the dual).

The goal of this algorithm is to keep the residual and the shadow residuals orthogonal to each other
at all iterations.

#algorithm(title: [BiCG])[
  + Pick a column vector $vv(x)^((0))$ and a row vector $vv(hat(x))^((0))$.
  + Compute initial residuals $vv(r)^((0)) = vv(b) - A vv(x)^((0))$ and
    $vv(hat(r))^((0)) = vv(hat(b)) - vv(hat(x))^((0)) A^T$.
  + Set directions $vv(d)_0 = vv(r)^((0))$ and $vv(hat(d))_0 = vv(hat(r))^0$.
  + *While* (`Stopping condition`):
    + Compute the step length
      $
        alpha_k = (vv(hat(r))^((k)) vv(r)^((k)))/(vv(hat(d))_k A vv(d)_k)
      $
    + Update $vv(x)^((k+1)) = vv(x)^((k)) + alpha_k vv(d)_k$ and
      $vv(hat(x))^((k+1)) = vv(hat(x))^((k)) + alpha_k vv(hat(d))_k$ and recompute the residuals.
    + Compute
      $
        beta_k = (vv(hat(r))^((k + 1)) vv(r)^((k+1)))/(vv(hat(r))^((k)) vv(r)^((k)))
      $
    + Update the directions $vv(d)_(k + 1) = vv(r)^((k + 1)) + beta_k vv(d)_k$ and
      $vv(hat(d))_(k + 1) = vv(hat(r))^((k + 1)) + beta_k vv(hat(d))_k$
  + *End*.
]

This method is twice as expensive as the regular CG method.

=== GMRes Method

The Generalized Minimum Residual method is the most used in practice in this class of problems.

The idea of this method is to find the next guess $vv(x)^((k))$
$
  vv(x)^((k)) in vv(x)^((0)) + cal(K)_k (A, vv(r)^((0))) "minimizing" norm(vv(r)^((k)))
$

The naive base of the Krylov space however is numerically very bad, and those vectors become almost
linearly independent very quickly. The idea to fix this is to use Arnoldi's iteration, i.e. run
Gram-Schmidt on the Krylov sequence to produce an orthonormal basis of the space.

#algorithm(title: "GMRES")[
  + Choose $vv(x)^((0))$.
  + Compute $vv(r)^((0)) = vv(b) - A vv(x)$.
  + *While* (`Stopping condition`)
    + Compute $vv(q)_k$ with a suitable method.
    + Form $Q_k$ as the $n times k$ matrix formed by $vv(q)_1, ..., vv(q)_k$.
    + Find $vv(y)^((k))$ which minimize $norm(vv(r)^((k)))_2$.
    + Compute $vv(x)^((k+1)) = vv(x)^((0)) + Q_k vv(y)^((k))$.
  + *End*
]

The main issue is that $Q_k$ becomes a huge, dense matrix; in practice after a few iterations we
start over with a fresh $Q_k$.

= Eigenvalue problems

In this section, given a matrix $A in CC^(n times n)$, we want to find the set of
$(lambda, v) in CC times CC^n$ (with $vv(v) != vv(0)$) which solves
$
  A vv(v) = lambda vv(v)
$

Note that eigenvectors are defined up to a constant:
$
  A v = lambda v <==> A (c vv(v)) = lambda (c vv(v))
$
therefore, for convenience, we will impose the extra condition
$
  norm(vv(v)_i) = 1
$

== Preliminaries

#definition(title: "Spectrum")[
  Let $A in CC^(n times n)$. Then its spectrum is the set of eigenvalues of $A$.
  $
    sigma(A) = {lambda_i (A) "s.t." lambda_i "is an eigenvalue of" A}
  $
]

In some problems we might not be interested in the full spectrum, we only care about the $k$ largest
or smallest eigenvalues.

#definition(title: "Transpose conjugate")[
  For a matrix or a vector over $CC$, we denote $A^H$ the transpose conjugate
  $
    A^H = overline(A^T)
  $
]

#proposition(title: "Rayleigh quotient")[
  For any eigenpair $(lambda_i, vv(v)_i)$ of $A$
  $
    lambda_i = (vv(v)_i^H A vv(v)_i)/(vv(v)_i^H vv(v)_i)
  $
]<prop:rayleigh>

#proof[
  Start by the eigenvalues equation.
  $
    A vv(v) = lambda vv(v) <==> lambda vv(v)^H vv(v) = vv(v)^H A vv(v) <==> lambda = (vv(v)^H A vv(v))/(vv(v)^H vv(v))
  $

  Note that $vv(v)^H vv(v)$ is the norm of $vv(v)$, therefore always non-zero for a non-zero $vv(v)$.
]

=== Similarity transformations

#definition(title: "Similarity transformation")[
  A matrix $B$ is similar to $A$ if there exists an invertible matrix $T$ such that
  $B = T^(-1) A T$.
]

#proposition[
  Similarity transformations preserve the spectrum: for $A, B$ similar $sigma(A) = sigma(B)$.
]

#proof[
  Let $(lambda, vv(y))$ be an eigenpair of $B$.
  $
    B y = lambda y <==> T^(-1) A T vv(y) = lambda vv(y) <==> A vv(w) = lambda vv(w)
  $
  with $vv(w) = T vv(y)$.
]

Therefore the plan is to massage $A$ with some $T$ such that the problem becomes easy to solve. This
works well if we need the full spectrum, however massaging with $T$ loses sparsity and it is often
hard to compute the right $T$.

=== Blackboard method

To compute eigenvalues on the blackboard we usually solve
$
  (A - I lambda) vv(v) = vv(0)
$

For this equation to have a non-zero solution we need $A - I lambda$ to be singular, i.e.
$
  p(lambda) = det(A - I lambda) = 0
$
which is called the *characteristic polynomial*, its roots are the eigenvalues of $A$.

==== Why it fails

There exists no formula for polynomials of degree 5 and above, therefore we would have to rely on
numerical methods. However methods to compute polynomial roots decrease precision substantially: a
small perturbation to the characteristic polynomial can result in a huge deviation in the roots.

== Power method

If we need only a few eigenvalues we can do something better, exploiting the geometric
interpretation of the eigenvalue problem. We introduce the *power method*.

#algorithm(title: "Power method")[
  + Let $lambda_1, ..., lambda_n$ be the eigenvalue of $A$,
  + Order such that $abs(lambda_1) > abs(lambda_2) >= ... >= abs(lambda_n)$. Note that the first one
    is _isolated_.
  + Let $vv(x)^((0))$ be the initial guess, such that $norm(vv(x)^((0))) = 1$.
  + *While* (`Stopping criterion`)
    + Compute $vv(y)^((k+1)) <-- A vv(x)^((k))$
    + Normalize $vv(x)^((k+1)) <-- (vv(y)^((k+1)))/norm(vv(y)^((k+1)))$
    + Use the @prop:rayleigh to compute $nu^((k+1)) = [vv(x)^((k+1))]^H A vv(x)^((k+1))$.
  + *End*
]

#theorem[
  Let $A$ be diagonalizable and $lambda_1$ (being the eigenvalue with largest modulus) is isolated.
  Then
  $
    lim_(k -> oo) vv(x)^((k)) = vv(v)_1 wide
    lim_(k -> oo) nu^((k+1)) = lambda_1
  $
]
#proof[
  Since $A$ is diagonalizable, the set of eigenvectors for a basis for $C^n$. Which means that for
  any $vv(x)^((0))$ can be written in that basis:
  $
    vv(x)^((0)) = sum^n_(i = 1) alpha_i vv(v)_i wide "for suitable" alpha_1, ..., alpha_n
  $
  We need to assume that $alpha_1 != 0$, which is true with probability $1$ for a random $vv(x)^((0))$.

  We first prove this intermediate lemma:

  #lemma[
    $
      A^k vv(x)^((0)) = sum^n_(i = 1) alpha_i lambda_i^k vv(v)_i
    $
  ]<lem:power-sum>
  #subproof(<lem:power-sum>)[
    We prove this by induction on the exponent $k$.

    In the base case $k = 0$, assume that $A^0 = I$ and $lambda^0 = 1$. Then
    $vv(x)^((0)) = sum^n_(i = 1) alpha_i vv(v)_i$ is trivially true by construction.

    For the inductive step we assume that the statement is true at $k$ and try to prove it for
    $k + 1$. Start from the expression at $k$ and multiply by $A$:
    $
      A^(k+1) vv(x)^((0)) & = A sum^n_(i = 1) alpha_i lambda_i^k vv(v)_i = sum^n_(i = 1) alpha_i lambda_i^k A vv(v)_i \
      & = sum^n_(i = 1) alpha_i lambda_i^k (lambda_i vv(v)_i) = sum^n_(i = 1) alpha_i lambda_i^(k+1) vv(v)_i \
    $

    This concludes the proof of the first lemma.
  ]

  From the result of the lemma we decouple $i = 1$ from the sum and pull out $alpha_1 lambda_1$ (we
  can do this since we are assuming that $alpha_1 != 0$).
  $
    A^k vv(x)^((0)) & = alpha_1 lambda_1^k vv(v)_1 + sum^n_(i = 2) alpha_i lambda_i^k vv(v)_i \
                & = alpha_1 lambda_1^k [ vv(v)_1 + underbrace(
                      sum^n_(i = 2) alpha_i/alpha_1 (lambda_i/lambda_1)^k vv(v)_i,
                      := vv(r)^((k))
                    ) ] \
                & = alpha_1 lambda_1^k ( vv(v)_1 + vv(r)^((k)))
  $
  where $vv(r)^((k))$ is the residual.

  #lemma[
    $
      lim_(k -> oo) norm(vv(r)^((k))) = 0
    $
  ]<lem:residual-limit>
  #subproof(<lem:residual-limit>)[
    Since $abs(lambda_i/lambda_1) <= abs(lambda_2 / lambda_1)$ we can write
    $
      norm(vv(r)^((k))) & = norm(sum^n_(i = 2) alpha_i/alpha_1 (lambda_i/lambda_1)^k vv(v)_i) \
                    & <= abs((lambda_2/lambda_1))^k
                      sum^n_(i = 2) abs(alpha_i/alpha_1) underbrace(
                        norm(vv(v)_i), =
                        1
                      ) \
    $
    and since $abs(lambda_1) > abs(lambda_2)$ the limit as $k -> oo$ is zero.
  ]

  Note that right now $A^k vv(x)^((0))$ does not converge as $k -> oo$: indeed $lambda^k$ either
  diverges to $oo$, $0$, or has a rotating phase. This is where normalization comes in.

  $
    vv(x)^((k + 1)) & = (A^k vv(x)^((k))) / norm(A^k vv(x)^((k))) \
                & = (alpha_1 lambda_1^k)/(abs(alpha_1) abs(lambda_1^k))
                  (vv(v)_1 + vv(r)^((k)))/norm(vv(v)_1 + vv(r)^((k))) \
                & = e^(i theta_k) (vv(v)_1 + vv(r)^((k)))/norm(vv(v)_1 + vv(r)^((k)))
  $
  and as $k -> oo$ we get
  $
    vv(x)^((k + 1)) = e^(i theta_k) vv(v)_1/norm(vv(v)_1)
  $
  where the error decays as $bigO(abs(lambda_2/lambda_1)^k)$.

  When we reach the stopping condition $vv(x)^((k))$ is sufficiently close to $vv(x)_1$ that we can use
  @prop:rayleigh to estimate the eigenvalue. The error also decays as
  $bigO(abs(lambda_2/lambda_1)^k)$.
]

=== Deflation

Assume now we have computed the largest eigenvalue $lambda_1$ and we want to compute the next
largest $lambda_2$.

To do so, we want to find a similarity transformation $S$ which satisfies $S vv(v)_1 = alpha vv(e)_1$, where
$vv(e)_1$ is the first element of the canonical basis, such that
$
  S A S^(-1) = mat(lambda_1, vv(b)^T; 0, B)
$
where $B$ is a submatrix with the same spectrum of $A$ without $lambda_1$.

To recover the right eigenvector we compute $vv(v)_2 = S^(-1) vec(alpha, vv(z)_2)$.

=== Inverse power method

The power method is very efficient, and easily parallelizable, therefore we want to exploit it as
much as possible.

We now want to compute the smallest eigenvalue
$abs(lambda_1) >= ... >= abs(lambda_(n - 1)) > abs(lambda_n)$, where the smallest one is isolated.

#remark[
  Let $A$ be invertible. Then $(lambda_i, v_i)$ is an eigenpair of $A$ iff $(1/lambda, v_i)$ is an
  eigenpair of $A^(-1)$.
]

We exploit this remark to apply the power method to $A^(-1)$. However, we cannot invert $A$, so we
need to solve a linear system at each iteration:
#algorithm(title: "Inverse power method")[
  + Let $vv(q)^((0))$ such that $norm(vv(q)^((0))) = 1$
  + For each iteration
    + Solve $A vv(z)^((k+1)) = vv(q)^((k))$
    + Compute $vv(q)^((k + 1)) <-- (vv(z)^((k+1)))/norm(vv(z)^((k+1)))$
    + $sigma^((k+1)) <-- [vv(q)^((k+1))]^H A vv(q)^((k+1))$
]
Note that in the last step of the loop we use plain $A$.

At each step of the loop we need to solve a whole linear system. This could be very expensive: a
possible strategy is to precompute a factorization of $A$ and use it to solve the system directly.

=== Shift

There are also methods to compute eigenvalues of other positions in the spectrum.

Let $mu in RR$. We want to compute
$
  lambda_i in sigma(A) wide "s.t." i = argmin abs(lambda_i - mu)
$

Define
$
  M_mu = A - mu I
$
then, the eigenvalues of $M_mu$ satisfy
$
  M_mu vv(w) = xi vv(w) & <==> (A - mu I) vv(w) = xi vv(w) \
                & <==> A vv(w) = (mu - xi) vv(w)
$

This means that the eigenvalue closest to $mu$ is the minimum eigenvalue of $M_mu$, we can compute
it by using the inverse power method (with shift).

The convergence rate is given by
$
  (min_i abs(lambda_i - mu))/(min_(j != i) abs(lambda_j - mu))
$

== Tools

=== QR Factorization

#definition(title: "QR factorization")[
  Let $A in RR^(m times n)$. $A$ admits a QR factorization if
  - $exists Q in R^(m times m)$ orthogonal ($Q^T = Q^(-1)$)
  - $exists R in R^(m times n)$ upper trapezoidal such that
  $
    A = Q R
  $
]

Assume $A$ is full-rank, so that it's column vectors are linearly independent. We could do
Gram-Schmidt to create an orthogonal matrix derived from the columns of $A$, however Gram-Schmit is
not always stable, we will see some methods to mitigate this.

The QR factorization could be *full* or *partial*:
- In the full QR factorization $Q in RR^(m times m)$ is a full orthogonal matrix and $R^(n times m)$
  is a upper trapezoidal matrix.
- In the partial one, we note that $R$ is padded with zero-rows in the lower part, therefore the
  last columns of $Q$ are useless. We therefore only compute $hat(Q) in RR^(m times n)$ and
  $hat(R) in RR^(n times n)$ which is an upper triangular matrix.

#remark(title: "Unitary vs Orthogonal matrices")[
  Orthogonal is the real-valued special case of unitary.

  - Orthogonal: $Q in RR^(n times n)$ with $Q^T Q = I$.
  - Unitary: $U in CC^(n times n)$ with $U^H U = I$.
]

=== Gram-Schmidt orthogonalization

#algorithm(title: "Gram-Schmidt orthogonalization")[
  + Let $vv(a)_1, ..., vv(a)_n$ be a set of vectors (could be the columns of some matrix $A$).
  + *For* $j = 1, ..., n$:
    + Let $vv(w)_j <- vv(a)_j$.
    + *For* $i = 1, ..., j-1$:
      + *If* `Modified GS`:
        + Let $r_(i, j) <- vv(q)_i^H vv(w)_j$, this is more numerically stable and yields the same results.
      + *Else*:
        + Let $r_(i, j) <- vv(q)_i^H vv(a)_j$.
      + *End*
      + Let $vv(w)_j <- vv(w)_j - r_(i, j) vv(q)_i$.
      + *If* i = j:
        + Assign $r_(j, j) <- norm(vv(w)_j)$.
      + *End*
      + Normalize $vv(q)_j <- vv(w)_j / norm(vv(w)_j)$.
    + *End*
  + *End*
]

This takes $bigO(m n^2)$.

== Schur decomposition

We want to compute $U A U^H = T$ such that $U$ is unitary and $T$ is upper triangular, so that
$sigma(A) = sigma(T)$.

Columns of $U$ are called *Schur vectors*. In general, only $vv(u)_1$ is an eigenvector of $A$.

#definition(title: [Invariant subspace])[
  Let $cal(S) subset.eq V$ be a subspace of $V$. We say $cal(S)$ is an invariant with respect to
  some matrix $A$ if
  $
    vv(v) in cal(S) ==> A vv(v) in cal(S)
  $
]

Notably, each eigenvector spans an invariant subspace of its matrix. A weaker version also holds for
Schur vectors.

#proposition(title: [Schur vectors span invariant subspaces])[
  Let $vv(u)_1, ..., vv(u)_n$ be the Schur vectors of $A$. Then
  $
    cal(S)_k = angle(vv(u)_1, ..., vv(u)_k) wide forall k in 1, ..., n
  $
  are invariant subspaces of $A$.
]

#algorithm(title: "Basic QR algorithm")[
  + Let $A^((0)) = A$ and $U^((0)) = I$.
  + *While* (`Stopping criterion`)
    + Find $Q^((k-1)), R^((k-1))$ such that $A^((k-1)) = Q^((k-1)) R^((k-1))$, this is a QR
      factorization.
    + Define $A^((k)) = R^((k-1)) Q^((k-1))$ (which will be different from $A^((k-1))$ since
      products are not commutable.
    + Define $U^((k)) = U^((k - 1)) Q^((k - 1))$.
  + *End*
  + *Return* $T = A^((k)), U = U^((k))$.
]

This is very expensive: $bigO(k n^3)$, but gives $T$ triangular.

$
  A^((k)) & = R^((k)) Q^((k)) = [Q^((k))]^H Q^((k)) R^((k)) Q^((k)) \
          & = [Q^((k))]^H A^((k-1)) Q^((k)) \
          & = [Q^((k))]^(-1) A^((k-1)) Q^((k))
$
Applying this arguments to the whole sequence we show that all the $A^((k))$ are similar.

Assuming that all eigenvalues are isolated all elements below the diagonal converge to zero, and the
spectrum can be read on the diagonal.

== Lanzos algorithm

This algorithm computes in one shot the extreme eigenvalues for a SPD matrix $A$.

For this algorithm we want to decompose
$
  A = Q T Q^T wide "with" Q "orthonormal and"\
  T = mat(
    alpha_1, beta_1, 0, dots.c, 0;
    beta_1, alpha_2, beta_2, dots.c, 0;
    0, dots.down, dots.down, dots.v, 0;
    0, dots.down, dots.down, dots.v, beta_(n-1);
    0, dots.c, 0, beta_(n-1), alpha_n;
  ) "is tri-diagonal"
$

It can be proven that this decomposition exists and is unique given the first column $vv(q)_1$ of $Q$.

The decomposition is obtained by imposing $A Q = Q T$ column by column:
$
  A vv(q)_n = beta_(n - 1) vv(q)_(n - 1) + alpha_n vv(q)_n + beta_(n + 1) vv(q)_(n + 1) \
  "by orthogonality"
  ==> cases(
    alpha_n & = vv(q)_n^H A vv(q)_n,
    beta_n & = vv(q)_(n + 1)^H A vv(q)_n
  )
$

#algorithm(title: "Lanczos algorithm")[
  + Let $vv(r)_0 = vv(q)_1$, $vv(q)_0 = vv(0)$ and $beta_0 = 1$.
  + *For* ($k = 1, ..., n$)
    + *If* ($beta_(k - 1) = 0$)
      + *Break*
    + *End*
    + Compute $vv(q)_k = vv(r)_(k - 1)/beta_(k-1)$.
    + Compute $alpha_k = vv(q)_k^T A vv(q)_k$.
    + Compute $vv(r)_k = (A - alpha_k) vv(q)_k - beta_(k - 1) vv(q)_(k - 1)$.
    + Let $beta_k = abs(vv(r)_k)$.
  + *End*
]

Then at each iteration the extreme eigenvalues of $T = Q^T_k A Q_k$ converge to the ones of $A$.

=== Why this is useful

First of all, note that the algorithm is fully build on mat-vec multiplications, which is the only
viable operation for big and sparse matrices.

Lanczos does not yield a triangular or diagonal matrix, so eigenvalues cannot be read anywhere in
$T$, when we are done computing $T$ we still need to solve for its eigenvalues.

However, we don't need to compute the full $T$, often a few iterations are enough. This gives a
$T in RR^(k times k)$, which can be easily solved via Schur decomposition (since $T$ is both
Hessenberg and symmetric this allows to compute QR factorizations in $bigO(n^2)$ instead of
$bigO(n^3)$). Of course the approximation of the result gets better as $k -> n$ but we can often can
stop way before.

= Non-square systems

== Over-specified systems

In this kind of systems the matrices are high and thin, i.e. the number of rows is much larger than
the number of columns.

An example of this kind of matrix is *linear or polynomial regressions*: we have a lot of sample but
only two parameters.

In these systems we will never be able to have zero residuals, however the goal for a regression is
to minimize them as much as possible in the least square.

=== Minimizing the residual

Let the residual be $vv(r) = vv(b) - A vv(x)$. If the residual is the minimum in the least square sense, then it
is orthogonal to the image of $A$. We can impose this condition by setting $A^T vv(r) = vv(0)$ and
substituting $vv(r)$ we get
$
  A^T A vv(x) = A^T vv(b)
$

The same result can be obtained analytically: let $Phi(vv(x)) = norm(vv(b) - A vv(x))^2$, then
$
     min_x Phi(vv(x)) & <==> grad Phi(vv(x)) = vv(0) \
      grad Phi(vv(x)) & = grad (vv(b) - A vv(x))^T (vv(b) - A vv(x)) \
                  & = grad (vv(b)^T vv(b) - vv(b)^T A vv(x) - vv(x)^T A^T vv(b) + vv(x)^T A^T A vv(x)) \
                  & = - vv(b)^T A - A^T vv(b) + 2 A^T A vv(x) \
                  & = 2 A^T A vv(x) - 2 A^T vv(b) \
  grad Phi(vv(x)) = vv(0) & <==> A^T A vv(x) = A^T vv(b)
$

#remark[
  If $A$ is full-rank $A^T A$ is SPD.
]
#proof[
  We want to show that $vv(x)^T A^T A vv(x) > 0$ for all $vv(x) in R^n without {vv(0)}$. But
  $vv(x)^T A^T A vv(x) = norm(A vv(x))^2$, so that, if $A$ has full rank, $A vv(x) != vv(0)$ for all $vv(x) != vv(0)$. By the
  properties of the norm we have $norm(vv(y)) > 0$ for all $vv(y) != vv(0)$, showing that $A A^T$ is positive
  definite.

  Symmetry is just $(A^T A)^T = (A^T)^T A^T = A A^T$.
]

This gives us very powerful methods to solve this system, like conjugate gradient or the Cholesky
factorization.

This method also has a major drawback: we need to solve a system with a huge conditioning number
$kappa(A^T A) = kappa(A)^2$: this is a nightmare in floating point math. We might get such a bad
matrix that $A^T A$ even loses its positive definiteness.

=== QR to the rescue

Instead of computing $A^T A$ we try to transform $A$. The best candidate is to use orthogonal
matrices, since $norm(Q^T (A vv(x) - vv(b)))^2 = norm(A vv(x) - vv(b))$.

#theorem[
  Let $vv(x)^* = hat(R)^(-1) hat(Q)^T vv(b)$. Then $vv(x)^*$ is the solution to the system in the least squares
  sense. The minimum value is $Phi(vv(x)^*) = sum_(i = n + 1)^m [(Q^T vv(b))_i]^2$.
]

#proof[
  Compute the QR decomposition of $A$: $A = Q R$.
  $
    norm(A vv(x) - vv(b))^2 & = norm(Q^T ( A vv(x) - vv(b)))^2 \
                    & = norm(Q^T (Q R vv(x) - vv(b)))^2 \
                    & = norm(Q^T Q R vv(x) - Q^T vv(b))^2 \
                    & = norm(R vv(x) - Q^T vv(b))^2 \
                    & = norm(hat(R) vv(x) - hat(Q)^T vv(b))^2 + sum_(i = n + 1)^m [(Q^T vv(b))_i]^2
  $
  In the last step we split $Q$ and $R$ in their reduced forms: indeed $R$ is zero after $n$, so
  that all those terms cancel, while the terms involving $Q$ can be brought out into their own term.

  We note that the tail elements do not involve $vv(x)$, so there is nothing we can do about them, we
  are left with minimizing $norm(hat(R) vv(x) - Q^T vv(b))$. This happens when
  $hat(R) vv(x) = Q^T vv(b) <==> vv(x) = R^(-1) Q^T vv(b)$ as stated.
]

We still have an issue: if $A$ is singular the whole concept of solution breaks as $hat(R)$ becomes
singular and the inverse no longer exists. Cholesky would fail too since $A^T A$ becomes positive
semi-definite.

=== Singular Value Decomposition (SVD)

The solution to the singularity problem is, between the possible solutions, select the one with
minimal norm. The right tool to do this is the Singular Value Decomposition (SVD).

#theorem(title: [Singular Value Decomposition])[
  Let $A in RR^(m times n)$. Then there exists $U in RR^(m times m)$ and $V in RR^(n times n)$ *both
  orthogonal* such that
  $
    U^T A V = Sigma := diag(sigma_1, ..., sigma_p) in RR^(m times n)
  $
  where $p := min {m,n}$ and $sigma_1 >= sigma_2 >= dots.c >= sigma_p$ are called the *singular
  values* of $A$.

  Equivalently we can write
  $
    A = U Sigma V^T
  $
]

This has some very nice implications: first we note that we can just read off $r := rank(A)$ as the
number of non-zero singular values; then, by writing
$
  A V = U Sigma <==> A vv(v)_i = sigma_i vv(u)_i
$
we see that
$
  ker(A) = "span"(vv(v)_(r+1), ..., vv(v)_n) wide "range"(A) = "span"(vv(u)_1, ..., vv(u)_r)
$
this gives us a concrete orthonormal basis of the image and the kernel of $A$.

#definition(title: [Moore-Penrose pseudo-inverse])[
  Let $A = U Sigma V^T$ as in the SVD. The pseudo-inverse of $A$ is defined as
  $
    A^dagger := V Sigma^dagger U^T
    wide "where" Sigma^dagger := diag(1/sigma_1, ..., 1/sigma_r, 0, ..., 0)
  $
]

#theorem[
  The solution to the over-specified system in the least squares sense is given by
  $
    vv(x)^* = A^dagger vv(b)
  $
]

#proof[
  Start by a change of variable: define $vv(w) := V^T vv(x)$ so that $vv(x) = V vv(w)$. Then
  $
    norm(A vv(x) - vv(b))^2 & = norm(A V vv(w) - vv(b))^2 \
                    & = norm(U Sigma V^T V vv(w) - vv(b))^2 \
                    & = norm(U Sigma vv(w) - vv(b))^2 \
                    & = norm(Sigma vv(w) - U^T vv(b))^2 \
  $
  Now we split the norm in the components before $r$ and after $r$:
  $
    norm(Sigma vv(w) - U^T vv(b))^2 & = sum^r_(i = 1) [sigma_i w_i - (U^T vv(b))_i]^2
                              + sum^p_(i = r+1) [(U^T vv(b))_i]^2
  $
  Since $sigma_i > 0$ when $i <= r$ we get that $w_i = (U^T vv(b))/sigma_i$ for all $i <= r$. For
  $i > r$ we can choose $w_i$ freely, but minimizing the norm tells us that they should all be set
  to zero.

  This gives $vv(w)^* = Sigma^dagger U^T vv(b)$, meaning
  $
    vv(x)^* = V vv(w)^* = V Sigma^dagger U^T vv(b) = A^dagger vv(b)
  $
  as desired.
]

= Multi-grid methods

Consider a problem where we are, for example, solving some differential equation. The discretization
on an evenly spaced grid gives us a sparse matrix, since all points in the grid only interact with
the neighbouring ones.

We usually rely on the residual to estimate how good our solver is performing. The idea of
multi-grid methods is, given the residuals, estimate the true error as
$
  A_h vv(e)_h^((k)) = vv(r)_h^((k))
$
(where $h$ is the grid spacing, more on that later) and use it to correct the solution.

This is particularly useful for using the weighted Jacobi method to solve differential equations.
After one iteration the error updates as $vv(e)^((k+1))_h = B vv(e)^((k))_k$ for some $B$ we don't really
care about right now. In this case the error can be described as the combination of multiple
oscillatory modes. This method is good at removing modes which oscillate very fast, while it takes a
long time to converge when the modes look almost flat.

#example[
  Consider a 2D surface where the edges are kept at a fixed temperature. Given some heat sources
  spread in the surface we want to see how the temperature evolves.

  In this problem the weighted Jacobi solver is very good at fixing errors in near by regions of the
  surface, since there the modes oscillate faster, while it struggles to fix errors when they are
  spread out in the whole surface since their modes are smooth.
]

Multi-grid methods exploit the fact that smooth modes look more oscillatory when looked at from a
coarser grid.

== Introduction on two grids

#definition(title: [Interpolation operator])[
  Consider an operator $cal(I)_h^(h') : R^(n_a) -> R^(n_b)$, where $n_a$ is the dimension of the
  grid with spacing $h$ and $n_b$ is the dimension of the grid with spacing $h'$.
]

Many times we consider $h' = k h$ with $k in NN$ so that the interpolation operator becomes trivial:
when moving from fine to coarse we just drop the extra points; when moving from coarse to fine we
linearly interpolate between the two points in the coarser grid.

These operators are linear and can therefore be written as matrices.

#example(title: [Interpolation operator $3 -> 6$])[
  $
    I_(2 h )^(h ) vec(a, b, c) =
    mat(
      1, 0, 0;
      1/2, 1/2, 0;
      0, 1, 0;
      0, 1/2, 1/2;
      0, 0, 1
    )
    vec(a, b, c) =
    vec(
      a,
      (a + b)/2,
      b,
      (b + c)/2,
      c
    )
  $
]

Then the method we present now consists of:
+ Solve the problem on the fine grid and compute the residual $vv(r)_h$.
+ Restrict the residual to the coarser grid $vv(r)_(2 h)$.
+ Solve the error equation in the coarser grid $A_(2 h) vv(e)_(2 h) = vv(r)_(2 h)$, where
  $A_(2 h) := I^(2h)_h A_h I_(2h)^h$.
+ Interpolate the error back to the finer grid $vv(e)_h$.
+ Correct the estimate $vv(x)_h <- vv(x)_h + vv(e)_h$.

== Cycles

Instead of just moving between a fine and a coarse grid, we can choose some more sophisticated
cycle. This is done mainly for performance: some times it might be too expensive to compute the
direct solution even on a grid of size $2h$, therefore we use another multi-grid solver to go down
another level, and so on.

One of the most used one is the *V cycle*, where we start from a fine grid and we move $k$ grid
down, then $k$ grid up, but there are other routines as well.

#figure(
  image("assets/nla/multigrid-cycles.svg"),
  caption: [Examples of common multi-grid cycle paths.],
)

== Algebraic multi-grid methods

These are methods developed when we cannot create a coarser grid because of numerical issues. We
need to rely on a single grid and perform some algebra on just the matrix itself.

#definition(title: "Associated graph")[
  Let $A$ be a $n times n$ matrix. Its associated graph is a graph $G = (V, E)$ where
  $V = 1, ..., n$ and
  $
    E = {e_(i, j) | a_(i, j) != 0 and i != j}
  $
]

Given a matrix $A$ we generate its associated graph. Then we want to remove the "weak" connections.

#definition(title: "Strongly connected nodes")[
  Let $theta in (0, 1)$. We say a node $i$ is strongly connected with node $j$ if
  $
    -a_(i, j) >= theta max_(k != i) (-a_(i, k))
  $
]

This gives a set of vectors $S_i$ which are strongly correlated to $i$. In turns, we can construct a
*strength matrix* $S$ where each row is $S_i forall i in 1, ..., n$.

We partition $V$ in two sets $C$ (coarse) and $F$ (fine).

#algorithm(title: "General coarsing algorithm")[
  + Let $C <- varnothing$ and $F <- varnothing$.
  + *While* $C union F != V$:
    + Pick $i in 1, ..., n$ such that $v_i in.not C union F$.
    + Add $v_i$ to $C$.
    + Let $S_i$ be the set of strongly connected vertices to $i$.
    + Add all the elements of $S_i$ to $F$.
  + *End*.
]

=== Interpolation

Now that we have the partition we need a way to estimate points of $F$ given $C$.

The idea is that, for a smooth error $vv(e)$,
$
  A vv(e) approx vv(0) <==> a_(i i) e_i + sum_(j in N_i) a_(i, j) e_j approx 0
$
This means that if all the neighbours of a given point are in $C$ we could solve the equation
directly.

If an $F$ point is strongly connected to another $F$ point then we cannot interpolate it directly.
We can however rely on the neighbouring $C$ points to estimate the missing $F$ point.

Note that if $C$ is very coarse, interpolation might be hard to parallelize.

= Domain decomposition

This technique is used to split the domain of the underlying PDE in smaller subdomains, solve the
problem in the subdomains in parallel and reconstruct the solution of the big problem.

In general, sub-problems need to talk to each other because often we cannot split the problem in
independent subdomains.

== Overlapping domains (Schwartz)

Assume we split our problem in two subdomains $Omega_1, Omega_2$. Since $Omega_1$ and $Omega_2$ are
overlapping, there will be some parts of the boundary of $Omega_1$ in the interior of $Omega_2$ and
viceversa.

To solve PDEs we need boundary conditions _on the whole boundary_, so to obtain the part of the
boundary of $Omega_1$ which is in the interior of $Omega_2$ we use the best estimate of the solution
within $Omega_2$.

We continue to refine the solution in $Omega_1$ and $Omega_2$ using the current best estimation of
the solution available in the other domain.

This is called *multiplicative Schwartz method* it chooses to use the best approximation available
in spite of parallelism.

Another possibility is the *additive Schwartz method* which computes the solution of all subdomains
in parallels, trading parallelisms for less accurate iterations.

=== Additive Schwartz preconditioner

This idea can be used to construct very effective preconditioners.

Consider the linear system $A vv(x) = vv(b)$. Split $A$ in subdomains $A = union.big_i A_i$, then $R_i$ is
the *extraction operator* where $R_i vv(x)$ is the elements of $vv(x)$ which belong to subdomain $i$.

#algorithm(title: [Additive Schwartz preconditioner])[
  + Use some iterative solver to get a residual $vv(r)^((k)) = vv(b) - A vv(x)^((k))$.
  + For each subdomain $i$
    + Restrict the residual to $R vv(r)_i^((k))$.
    + Solve the error equation for a correction $delta_i$:
      $
        A_i vv(delta)_i = R vv(r)_i^((k)) ==> vv(delta)_i = A^(-1)_i R_i vv(r)^((k))
      $
    + Extend the correction back by multiplying by $R^T_i$:
      $
        R_i^T vv(delta)_i = R_i^T A_i^(-1) R_i vv(r)^(k)
      $
  + This gives
    $
      vv(x)^((k+1)) = vv(x)^((k)) + [sum_i R_i^T A_i^(-1) R_i] vv(r)^((k))
    $
]

We can then define $sum_i R_i^T A_i^(-1) R_i$ is called the Additive Schwartz preconditioner.

=== Coarse-grid correction

While methods like additive Schwartz can help reduce errors inside a certain subdomain, they take a
long time to converge when the error spans across different subdomains, meaning that the subdomains
disagree on what the prediction of a certain region should be.

To address this we introduce a coarse grid in which we solve the problem for the whole domain. This
can be very coarse, so that's not computationally too expensive, but it still helps far apart
subdomains to finding a solution more quickly.

== Non-overlapping domains (Schur)

Here instead we split the domain in non-overlapping subdomains: each subdomain only shares the
interface nodes $Gamma$ with other subdomains.

The problem then looks like
$
  mat(
    A_(I I), A_(I Gamma);
    A_(I Gamma)^T, A_(Gamma Gamma)
  )
  vec(vv(x)_I, vv(x)_Gamma) = vec(vv(b)_I, vv(b)_Gamma)
$

Since the interior of the subdomains are not connected, $A_(I I)$ is block-diagonal, so solving in
each subdomain can be done in parallel. We get
$
  vv(x)_I = A^(-1)_(I I) (vv(b)_I - A_(I Gamma) vv(x)_Gamma)
$
By substituting that in the second row we get
$
  underbrace((A_(Gamma Gamma) - A_(I Gamma)^T A^(-1)_(I I) A_(I Gamma)), =: S)vv(x)_Gamma
  = vv(b)_Gamma - A_(I Gamma)^T A^(-1)_(I I) vv(b)_I
$
which is a smaller system only involving the interfaces.

Even if this system is smaller, the matrix $S$ (the Schur complement) could be dense or hard to
solve. In practice we never materialize it.

Note that sometimes Schur is note enough and we still could need a preconditioner.

= Direct methods

Now we tackle solving $A x = b$ directly, in a finite number of operations.

== LU factorization

The idea is to factorize $A$ in two triangular matrices
$
  A = L U
$
so that the system can be solved as
$
  L vv(y) = vv(b) --> U vv(x) = vv(y)
$
just by using forward and backwards substitution.

This is also nice since the factorization can then be cached and reused for subsequent solves with a
different $vv(b)$.

#theorem(title: [Existence of $L U$ factorization])[
  If $A$ is invertible and the determinant of the top-left $i times i$ blocks of $A$ are all
  non-zero for $i = 1, ..., n - 1$, then the LU factorization exists.
]

We can also introduce pivoting
$
  P A = L U
$
where $P$ is a matrix which can swap the rows of $A$. This can be done in solving a linear system,
since rearranging the equations gives the same solution.

=== Fill-in

When factoring sparse matrices there is the issue that the factorization is usually not sparse. This
phenomenon is called fill-in.

Row (or even column) pivoting can greatly help reducing it.

== Cholesky factorization

If $A$ is SPD then we can do even better by factorizing it in $A = R^T R$ where $R$ is upper
triangular.

