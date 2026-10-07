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

= Preliminaries

We note $bold(x)$ a vector in $RR^n$, with $bold(0), bold(1)$ being the all zero and all 1 vectors,
while $bold(e)_i$ are the vectors which form the canonical base of $RR^n$.

Recall that a matrix is *nilpotent* if $exists k in NN$ such that $bold(A)^k = bold(0)$.

Also
$
  A^(-T) := (A^T)^(-1) = (A^(-1))^T \
  (A B)^(-1) = B^(-1) A^(-1)
$

Recall that if there exists $bold(x) != bold(0)$ such that $bold(A x) = bold(0)$, then $bold(A)$ is
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
If $A$ is symmetric and positive definite ($x^T A x > 0 forall x != 0$), then it can be decomposed by
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
  A x = b
$
where $A$ is non-singular and sparse.

We could work by directly manipulating $A$ and get a _direct solution_, but this is not a good fit
for us: usually these methods are $bigO(n^3)$ and do not preserve the sparsity of $A$.

We therefore introduce iterative methods.

#definition(title: "Iterative method")[
  This is a method to compute a sequence $x^((1)), ..., x^((k))$ starting from $x^((0))$ such that
  $
    lim_(k -> oo) x^((k)) = x
  $
  independently from $x^((0))$, where $x$ is the desired result.
]

In real computations we cannot have an infinite number of steps, therefore we use a stopping
criterion, which tells us when our solution is good enough.

== Linear iterative methods

We study the class of iterative methods such that
$
  x^((k + 1)) = B x^((k)) + f
$
where $B$ is the _iteration matrix_ and, together with $f$, fully specify the method.

The first criterion to chose these parameters is *consistency*: if $x^((k))$ is the correct
solution, then $x^((k + 1)) = x^((k))$. This gives
$
  x = B x + f ==> f = (I - B)x = (I - B) A^(-1) b
$

This condition is necessary, but not sufficient. On top of consistency, we need *convergence*.

#definition(title: "Error")[
  At step $k$ we define the error as
  $
    e^((k)) = x - x^((k))
  $
  where $x$ is the true solution.
]

For convergence to hold we want the norm of the error to go to zero as $k -> oo$. This in practice
gives
$
  norm(e^(k + 1)) & = norm(x - x^(k + 1)) \
                  & = norm(x - B x^(k) - f) \
                  & = norm(x - B x^(k) - (I - B)x) \
                  & = norm(B e^((k))) \
                  & <= norm(B) norm(e^((k)))
$
Therefore, for the error to go to zero we need $norm(B) < 1$.
This is a sufficient condition for convergence.

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

Ideally we want to stop when $norm(x - x^((k)))/norm(x) <= epsilon$, however we don't know the true
solution $x$.

#definition(title: "Conditioning number")[
  Given a matrix $A$, its conditioning number is defined as
  $
    kappa(A) = norm(A) dot.op norm(A^(-1))
  $
]

A method which can be used in practice is
$
  norm(x - x^((k)))/norm(x) <= kappa(A) norm(r^((k)))/norm(b)
  ==> kappa(A) norm(r^((k)))/norm(b) < epsilon
$
or another one
$
  norm(delta^((k))):= norm(x^((k + 1)) - x^((k))) <= epsilon
$
and it can be shown that
$
  norm(e^((k))) <= 1 / (1- rho(B)) norm(delta^((k)))
$

=== Preconditioning

We introduce an SPD matrix $P^(-1)$ and we solve
$
  P^(-1/2) A P^(-1/2) z = P^(-1/2) b
$
Then $x = P^(1/2) z$.

We try to chose $P$ such that $kappa(P^(-1/2) A P^(-1/2)) << kappa(A)$.

$
  x^((k + 1)) = x^((k)) + P^(-1) r^((k))
$
where $r^((k)) = b - A x^((k))$ and $P$ is the preconditioner of the residual.
In practice we never invert $P$, we solve for $P z^((k)) = r^((k))$.

We can also write this in matrix form:
$
  A = P - N
$
This also preserves sparsity

== Richardson method

$P^(-1) r^((k))$ gives us the direction of the residual. We can however also add some coefficients
$alpha_k$ which give us the magnitude of this direction vector.

This is called Richardson method. In particular if $alpha_k = alpha forall k$ this is the static
variant, otherwise that's the dynamic version.
In particular, if $A$ is SPD (symmetric and positive definite), there is a good method to pick these
$alpha_k$.

=== Choosing $alpha$

We want
$
  B alpha = I - alpha P^(-1) A
$
such that the spectral radius of $B alpha$ is as smaller that $1$.
The role of $alpha$ is to push back the eigenvalues towards $0$.

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

We can now exploit the fact that $A$ is SPD. This means that $Phi(y) = 1/2 y^T A y - y^T b$ (call it
the _energy function_) is convex, and the unique minimum is given by $grad Phi(y) = 0 = A y - b$,
which is the solution of our system.

This means that we want to set the residual to
$
  r^((k)) = - grad Phi(x^((k))) = b - A x^((k))
$

It turns out that two consecutive residuals are always orthogonal. This can be proven by just
multiplying $r^((k))$ with $r^((k + 1))$.

Then our problem reduces to
$
  x^((k + 1)) = x^((k)) - alpha_k grad Phi (x^((k))
$

To compute $alpha_k$ we can just expand $Phi(x^((k + 1)))$ and look at it as a function of
$alpha_k$ and looking for its minimizer. Doing the algebra, we find out that $Phi(x^((k + 1)))$ is
a 1 dimensional parabola in $alpha_k$, which is is trivial to minimize.

This gives us
$
  alpha_k = ((r^((k)))^T r^((k)))/((r^((k)))^T A r^((k)))
$

This gives us a full algorithm:
- Compute $alpha_k$ as above $--> bigO(n)$ if $A$ is sparse.
- $x^((k + 1)) = x^((k)) + alpha_k r^((k)) --> bigO(n)$.
- $r^((k + 1)) = b - A x^((k + 1)) = b - A(x^((k)) + alpha_k r^((k))) = r^((k)) - alpha_k A r^((k))
  --> bigO(n)$. Note that $A r^((k))$ has already been computed when computing $alpha_k$, if we
  reuse it we can save a matrix-vector multiplication.

=== Convergence

This method, in precise arithmetic, always converges.

#definition(title: "Matrix-induced norm")[
  Let $A$ be an SPD matrix.
  For a vector $z$ we define its norm induced by $A$ as
  $
    norm(z)_A = sqrt(z^T A z) quad forall z in RR^n
  $
]


The speed of convergence depends on $A$:
$
  norm(e^((k + 1)))_A <= (kappa(A) - 1)/(kappa(A) + 1) norm(e^((k)))_A ==>
  norm(e^((k + 1)))_A <= ((kappa(A) - 1)/(kappa(A) + 1))^k norm(e^((0)))_A
$

=== Adding back the preconditioner

Now let $P != I$
$
  A x = p ==> P^(1/2) A P^(-1/2) y = P^(1/2) b quad "with" y = P^(1/2) x
$
where the bound for the error is

$
  norm(e^((k + 1)))_A <= [(kappa(P^(1/2) A P^(-1/2)) - 1)/(kappa(P^(1/2) A P^(-1/2)) + 1)]
  norm(e^((k)))_A
$

This has the issue that, in theory, we would need both to compute $P^(1/2)$ and invert it: both very
expensive operations.
However, in practice, we can avoid fully materializing either $P^(1/2)$ or its inverse: we just need
the effect of $P$ on the residual.

Indeed, we can define the algorithm as

#algorithm(title: "Preconditioned Richardson method")[
  + Given $x^((0))$
  + Compute $r^((0)) = b - A x^((0))$
  + *While* `Stopping condition`
    + Solve $P z^((k)) = r^((k))$ for $z^((k))$
    + Compute $alpha_k = ((z^((k)))^T r^((k)))/((z^((k)))^T A z^((k)))$
    + Update $x^((k + 1)) = x^((k)) + alpha z^((k))$
    + Update $r^((k + 1)) = r^((k)) - alpha_k A z^((k))$
  + *End*
]

This gives us a tradeoff: a $P$ which is very good at minimizing the error might be very expensive
to compute, since at every iteration we need to solve a linear system involving $P$.
We usually choose $P$ such that it has a good structure and the system can be computed quickly.

== Krylov space methods

Let us start with an example.

=== Conjugate gradient method

We now ask whether the residual is actually the best direction to follow. We start by relaxing this
assumption and see what we can get.

This relaxation comes from the idea that maybe I can look at the previous residuals.

#definition(title: [$A$-orthogonal])[
  Let $A$ be a SPD matrix and $d^((0)), ..., d^((k)) in RR^n$.
  We say that $d^((k+1))$ is $A$-orthogonal (or $A$-conjugate) to all the previous directions if
  $
    (d^((k+1)), d^((j)))_A := (d^((k+1)))^T A d^((j)) = 0 quad forall j <= k
  $
]

We try to impose that our new sequence of directions $d^((k))$, which we use in place of the
residuals, to be $A$-orthogonal to each other.

#theorem(title: "Conjugate gradient method error")[
  $
    norm(e^((k)))_A <= (2 c^k)/(1 + c^(2k)) norm(e^((0)))_A quad "with" c = (sqrt(K(A)) - 1)/(sqrt(K(A))+1)
  $
]

This also has the advantage that $d^((k))$ form a basis of $RR^n$, which means that the method
converges in exactly $n$ steps.

The problem is then reframed as "finding iteratively a base to $RR^n$ in order to represent $x$".

This gives us this algorithm

#algorithm(title: "Conjugate gradient method")[
  + Given $x^((0))$.
  + Compute $r^((0)) = b - A x^((0))$.
  + Set $d^((0)) = r^((0))$.
  + *While* (`Stopping criterion`):
    + Compute $ alpha_k = ((d^((k)))^T r^((k)))/((d^((k)))^T A d^((k))) $
    + Compute $x^((k+1)) = x^((k)) + alpha_k d^((k))$.
    + Compute $r^((k+1)) = r^((k)) - alpha_k A d^((k))$.
    + Compute $ beta_k = ((A d^((k)))^T r^((k+1)))/((A d^((k)))^T A d^((k))) $
    + Set $d^((k+1)) = r^((k+1)) - beta_k d^((k))$.
  + *End*
]

We can of course also use preconditioning.

#algorithm(title: "Preconditioned conjugate gradient method")[
  + Given $x^((0))$.
  + Compute $r^((0)) = b - A x^((0))$.
  + Set $d^((0)) = r^((0))$.
  + *While* (`Stopping criterion`):
    + Compute $ alpha_k = ((z^((k)))^T r^((k)))/((z^((k)))^T A z^((k))) $
    + Compute $x^((k+1)) = x^((k)) + alpha_k d^((k))$.
    + Compute $r^((k+1)) = r^((k)) - alpha_k A d^((k))$.
    + Solve $P z^((k + 1)) = r^((k+1))$ for $z^((k+1))$.
    + Compute $ beta_k = ((A d^((k)))^T z^((k+1)))/((A d^((k)))^T A d^((k))) $
    + Set $d^((k+1)) = z^((k+1)) - beta_k d^((k))$.
  + *End*
]

=== In general

We write
$
  r^((k+1)) = r^((k)) - A r^((k))
$
which means that $r^((k + 1))$ is a linear polynomial of $r^((k))$.

This means we can can recursively write each $r^((k))$. Then the residuals lie on
$
  x^((0)) + "span"{ r^((0)), A r^((0)), ..., A^(k-1) r^((0)) }
$
where the space spanned by this vectors is a Krylov space.

== Non symmetric systems

To solve non symmetric systems we still use Krylov space solvers, however the theory is not as
advanced.

=== Biconjugate gradient method

This is an extension of the conjugate gradient method for non-symmetric matrices.

Let the dual problem be
$
  x^T A^T = b^T
$
and look at the Krylov space generated by the dual and its shadow residuals (i.e. the residuals of
the dual).

TODO: see slides (P2, page 84) for algorithm. The idea is to mix up the residuals of the primal and
the dual.

This method is twice as expensive as the regular CG method.

=== GMRES Method

The Generalized Minimum Residual method is the most used in practice in this class of problems.

This is also a Krylov space method, however note that since we no longer have the nicities of SPD
matrices, sometimes the vector which generate the space are very close to being aligned. This is an
issue for stability: we could use Gram-Schmit which we can use to get orthonormal vectors instead,
even if this could lead to additional instabilities and performance penalties.

#algorithm(title: "GMRES")[
  + Choose $x^((0))$.
  + Compute $r^((0)) = b - A x$.
  + *While* (`Stopping condition`)
    + Compute $q_k$ with a suitable method.
    + Form $Q_k$ as the $n times k$ matrix formed by $q_1, ..., q_k$.
    + Find $y^((k))$ which minimize $norm(r^((k)))_2$.
    + Compute $x^((k+1)) = x^((0)) + Q_k y^((k))$.
  + *End*
]

The main issue is that $Q_k$ becomes a huge, dense matrix; in practice after a few iterations we
start over with a fresh $Q_k$.

= Eigenvalue problems

In this section, given a matrix $A in CC^(n times n)$, we want to find the set of
$(lambda, v) in CC times CC^n$ (with $v != 0$) which solves
$
  A v = lambda v
$

Note that eigenvectors are defined up to a constant:
$
  A v = lambda v <==> A (c v) = lambda (c v)
$
therefore, for convenience, we will impose the extra condition
$
  norm(v_i) = 1
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
  For any eigenpair $(lambda_i, v_i)$ of $A$
  $
    lambda_i = (v_i^H A v_i)/(v_i^H v_i)
  $
]<prop:rayleigh>

#proof[
  Start by the eigenvalues equation.
  $
    A v = lambda v <==> lambda v^H v = v^H A v <==> lambda = (v^H A v)/(v^H v)
  $

  Note that $v^H v$ is the norm of $v$, therefore always non-zero for a non-zero $v$.
]

=== Similarity transformations

#definition(title: "Similarity transformation")[
  A matrix $B$ is similar to $A$ if there exists an invertible matrix $T$ such that
  $B = T^(-1) A T$.
]

#proposition[
  Similarity transformations preserve the spectrum:
  for $A, B$ similar $sigma(A) = sigma(B)$.
]

#proof[
  Let $(lambda, y)$ be an eigenpair of $B$.
  $
    B y = lambda y <==> T^(-1) A T y = lambda y <==> A w = lambda w
  $
  with $w = T y$.
]

Therefore the plan is to massage $A$ with some $T$ such that the problem becomes easy to solve.
This works well if we need the full spectrum, however massaging with $T$ loses sparsity and it is
often hard to compute the right $T$.

=== Blackboard method

To compute eigenvalues on the blackboard we usually solve
$
  (A - I lambda) v = 0
$

For this equation to have a non-zero solution we need $A - I lambda$ to be singular, i.e.
$
  p(lambda) = det(A - I lambda) = 0
$
which is called the *characteristic polynomial*, its roots are the eigenvalues of $A$.

==== Why it fails

There exists no formula for polynomials of degree 5 and above, therefore we would have to rely on
numerical methods.
However methods to compute polynomial roots decrease precision substantially: a small perturbation
to the characteristic polynomial can result in a huge deviation in the roots.

== Power method

If we need only a few eigenvalues we can do something better, exploiting the geometric
interpretation of the eigenvalue problem. We introduce the *power method*.

#algorithm(title: "Power method")[
  + Let $lambda_1, ..., lambda_n$ be the eigenvalue of $A$,
  + Order such that $abs(lambda_1) > abs(lambda_2) >= ... >= abs(lambda_n)$.
    Note that the first one is _isolated_.
  + Let $x^((0))$ be the initial guess, such that $norm(x^((0))) = 1$.
  + *While* (`Stopping criterion`)
    + Compute $y^((k+1)) <-- A x^((k))$
    + Normalize $x^((k+1)) <-- (y^((k+1)))/norm(y^((k+1)))$
    + Use the @prop:rayleigh to compute $nu^((k+1)) = [x^((k+1))]^H A x^((k+1))$.
  + *End*
]

#theorem[
  Let $A$ be diagonalizable and $lambda_1$ (being the eigenvalue with largest modulus) is isolated.
  Then
  $
    lim_(k -> oo) x^((k)) = v_1 wide
    lim_(k -> oo) nu^((k+1)) = lambda_1
  $
]
#proof[
  Since $A$ is diagonalizable, the set of eigenvectors for a basis for $C^n$.
  Which means that for any $x^((0))$ can be written in that basis:
  $
    x^((0)) = sum^n_(i = 1) alpha_i v_i wide "for suitable" alpha_1, ..., alpha_n
  $
  We need to assume that $alpha_1 != 0$, which is true with probability $1$ for a random $x^((0))$.

  We first prove this intermediate lemma:

  #lemma[
    $
      A^k x^((0)) = sum^n_(i = 1) alpha_i lambda_i^k v_i
    $
  ]
  #proof[
    We prove this by induction on the exponent $k$.

    In the base case $k = 0$, assume that $A^0 = I$ and $lambda^0 = 1$.
    Then $x^((0)) = sum^n_(i = 1) alpha_i v_i$ is trivially true by construction.

    For the inductive step we assume that the statement is true at $k$ and try to prove it for
    $k + 1$.
    Start from the expression at $k$ and multiply by $A$:
    $
      A^(k+1) x^((0)) & = A sum^n_(i = 1) alpha_i lambda_i^k v_i = sum^n_(i = 1) alpha_i lambda_i^k A v_i \
      & = sum^n_(i = 1) alpha_i lambda_i^k (lambda_i v_i) = sum^n_(i = 1) alpha_i lambda_i^(k+1) v_i \
    $

    This concludes the proof of the first lemma.
  ]

  From the result of the lemma we decouple $i = 1$ from the sum and pull out $alpha_1 lambda_1$ (we
  can do this since we are assuming that $alpha_1 != 0$).
  $
    A^k x^((0)) & = alpha_1 lambda_1^k v_1 + sum^n_(i = 2) alpha_i lambda_i^k v_i \
                & = alpha_1 lambda_1^k [ v_1 + underbrace(
                      sum^n_(i = 2) alpha_i/alpha_1 (lambda_i/lambda_1)^k v_i,
                      := r^((k))
                    ) ] \
                & = alpha_1 lambda_1^k ( v_1 + r^((k)))
  $
  where $r^((k))$ is the residual.

  #lemma[
    $
      lim_(k -> oo) norm(r^((k))) = 0
    $
  ]
  #proof[
    Since $abs(lambda_i/lambda_1) <= abs(lambda_2 / lambda_1)$ we can write
    $
      norm(r^((k))) & = norm(sum^n_(i = 2) alpha_i/alpha_1 (lambda_i/lambda_1)^k v_i) \
                    & <= abs((lambda_2/lambda_1))^k
                      sum^n_(i = 2) abs(alpha_i/alpha_1) underbrace(
                        norm(v_i), =
                        1
                      ) \
    $
    and since $abs(lambda_1) > abs(lambda_2)$ the limit as $k -> oo$ is zero.
  ]

  Note that right now $A^k x^((0))$ does not converge as $k -> oo$: indeed $lambda^k$ either
  diverges to $oo$, $0$, or has a rotating phase. This is where normalization comes in.

  $
    x^((k + 1)) & = (A^k x^((k))) / norm(A^k x^((k))) \
                & = (alpha_1 lambda_1^k)/(abs(alpha_1) abs(lambda_1^k))
                  (v_1 + r^((k)))/norm(v_1 + r^((k))) \
                & = e^(i theta_k) (v_1 + r^((k)))/norm(v_1 + r^((k)))
  $
  and as $k -> oo$ we get
  $
    x^((k + 1)) = e^(i theta_k) v_1/norm(v_1)
  $
  where the error decays as $bigO(abs(lambda_2/lambda_1)^k)$.

  When we reach the stopping condition $x^((k))$ is sufficiently close to $x_1$ that we can use
  @prop:rayleigh to estimate the eigenvalue. The error also decays as
  $bigO(abs(lambda_2/lambda_1)^k)$.
]

=== Inverse power method

The power method is very efficient, and easily parallelizable, therefore we want to exploit it as
much as possible.

We now want to compute the smallest eigenvalue
$abs(lambda_1) >= ... >= abs(lambda_(n - 1)) > abs(lambda_n)$, where the smallest one is isolated.

#remark[
  Let $A$ be invertible. Then $(lambda_i, v_i)$ is an eigenpair of $A$ iff $(1/lambda, v_i)$ is an
  eigenpair of $A^(-1)$.
]

We exploit this remark to apply the power method to $A^(-1)$.
However, we cannot invert $A$, so we need to solve a linear system at each iteration:
#algorithm(title: "Inverse power method")[
  + Let $q^((0))$ such that $norm(q^((0))) = 1$
  + For each iteration
    + Solve $A z^((k+1)) = q^((k))$
    + Compute $q^((k + 1)) <-- (z^((k+1)))/norm(z^((k+1)))$
    + $sigma^((k+1)) <-- [q^((k+1))]^H A q^((k+1))$
]
Note that in the last step of the loop we use plain $A$.

At each step of the loop we need to solve a whole linear system. This could be very expensive: a
possible strategy is to precompute a factorization of $A$ and use it to solve the system directly.

=== Deflation methods

This is just a sketch, however there are also methods to compute eigenvalues of other positions in
the spectrum.

Let $mu in.not sigma(A)$. We want to compute
$
  lambda_i in sigma(A) wide "s.t." i = argmin abs(lambda_i - mu)
$

Define
$
  M_mu = A - mu I
$
then, the eigenvalues of $M_mu$ satisfy
$
  M_mu w = xi w & <==> (A - mu I) w = xi w \
                & <==> A w = (mu - xi) w
$

This means that the eigenvalue closest to $mu$ is the minimum eigenvalue of $M_mu$ using the inverse
power method (with shift).

== QR Factorization

#definition(title: "QR factorization")[
  Let $A in RR^(n times n)$.
  $A$ admits a QR factorization if
  - $exists Q in R^(n times n)$ orthogonal ($Q^T = Q^(-1)$)
  - $exists R in R^(n times n)$ upper triangular
  such that
  $
    A = Q R
  $
]

Assume $A$ is full-rank, so that it's column vectors are linearly independent. We could do
Gram-Schmit to create an orthogonal matrix derived from the columns of $A$, however Gram-Schmit is
not always stable, we will see some methods to mitigate this.

=== Gram-Schmit orthogonalization

Let $a_1, ..., a_n$ (in this case the columns of $A$).

$
  q_j = w_j/norm(w_j) wide "with" w_j = a_j sum^(j - 1)_(k = 1) (q_k^H a_j) q_k
$
then
$
  r_(i j) = cases(
    q_i^H a_j wide & "if" i != j,
    norm(a_j - sum^(j-1)_(i= 1) r_(i j) q_i) wide & "if" i == j
  )
$

This is unstable!

=== Basic QR algorithm

#algorithm(title: "Basic QR algorithm")[
  + Let $A^((0)) = A$ and $U^((0)) = I$.
  + *While* (`Stopping criterion`)
    + Find $Q^((k-1)), R^((k-1))$ such that $A^((k-1)) = Q^((k-1)) R^((k-1))$.
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

=== Stopping criteria

#figure(
  table(
    columns: (auto, auto, auto),
    table.header("", "Power methods", "QR"),
    [Stopping criterion],
    [$abs(nu^((k+1)) - nu^((k)))/abs(nu^((k+1))) <= "Tol"$],
    [The largest element below the diagonal is less than some tolerance.],
  ),
)


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

It can be proven that this decomposition exists and is unique given the first column $q_1$ of $Q$.

The decomposition is obtained by imposing $A Q = Q T$:
$
  A q_n = alpha_n
$

#algorithm(title: "Lanczos algorithm")[
  + Let $r_0 = q_1$, $q_0 = 0$ and $beta_0 = 1$.
  + *For* ($k = 1, ..., n$)
    + *If* ($beta_(k - 1) = 0$)
      + *Break*
    + *End*
    + Compute $q_k = r_(k - 1)/beta_(k-1)$.
    + Compute $alpha_k = q_k^T A q_k$.
    + Compute $r_k = (A - alpha_k) q_k - beta_(k - 1) q_(k - 1)$.
    + Let $beta_k = abs(r_k)$.
  + *End*
]

Then at each iteration the extreme eigenvalues of $T = Q^T_k A Q_k$ converge to the ones of $A$.

Note that the algorithm is build on vector operations, it is matrix-free, which is very useful if
$A$ is sparse.

= Non-square systems

== Over-specified systems

In this kind of systems the matrices are high and thin, i.e. the number of rows is much larger
than the number of columns.

An example of this kind of matrix is *linear or polynomial regressions*: we have a lot of sample
but only two parameters.

In these systems we will never be able to have zero residuals, however the goal for a regression is
to minimize them as much as possible in the least square.

#remark[
  If $A$ is full-rank $A^T A$ is SPD.
]


This means that we can solve
$
  A^T A x = A^T b
$
instead. Moreover, since $A^T A$ is SPD, this is a convex minimization problem, therefore we can
just set the gradient to zero.

