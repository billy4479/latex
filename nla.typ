#import "lib/template.typ": *
#import "lib/theorem.typ": *
#import "lib/utils.typ": *
#import "@preview/lovelace:0.3.1": *

#show: template.with(
  titleString: "Numerical Linear Algebra",
  author: "Giacomo Ellero",
  date: "A.Y. 2026/2027",
  font: "",
)

#show: thm-init

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

TODO -> lecture P2 until Richardson method

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

Recall that the spectral radius $rho(B) = max_j abs(lambda_j (B))$ where $lambda_j (B)$ are the
eigenvalues of $B$. The role of $alpha$ is to push back the eigenvalues towards $0$.

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

#definition(title: "Conditioning number")[
  Given a matrix $A$, its conditioning number is defined as
  $
    K(A) = norm(A) dot.op norm(A^(-1))
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

#pseudocode-list[
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
