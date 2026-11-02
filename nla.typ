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
#let v(it) = bold(it)

= Preliminaries

We note $v(x)$ a vector in $RR^n$, with $v(0), v(1)$ being the all zero and all 1 vectors,
while $v(e)_i$ are the vectors which form the canonical base of $RR^n$.

Recall that a matrix is *nilpotent* if $exists k in NN$ such that $bold(A)^k = bold(0)$.

Also
$
  A^(-T) := (A^T)^(-1) = (A^(-1))^T \
  (A B)^(-1) = B^(-1) A^(-1)
$

Recall that if there exists $v(x) != v(0)$ such that $bold(A) v(x) = v(0)$, then $bold(A)$ is
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
If $A$ is symmetric and positive definite ($v(x)^T A v(x) > 0 forall v(x) != v(0)$), then it can be decomposed
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
  A v(x) = v(b)
$
where $A$ is non-singular and sparse.

We could work by directly manipulating $A$ and get a _direct solution_, but this is not a good fit
for us: usually these methods are $bigO(n^3)$ and do not preserve the sparsity of $A$.

We therefore introduce iterative methods.

#definition(title: "Iterative method")[
  This is a method to compute a sequence $v(x^((1))), ..., v(x^((k)))$ starting from $v(x^((0)))$ such that
  $
    lim_(k -> oo) v(x^((k))) = v(x)
  $
  independently from $v(x^((0)))$, where $v(x)$ is the desired result.
]

In real computations we cannot have an infinite number of steps, therefore we use a stopping
criterion, which tells us when our solution is good enough.

== Linear iterative methods

We study the class of iterative methods such that
$
  v(x^((k + 1))) = B v(x^((k))) + v(f)
$
where $B$ is the _iteration matrix_ and, together with $v(f)$, fully specify the method.

The first criterion to chose these parameters is *consistency*: if $v(x^((k)))$ is the correct
solution, then $v(x^((k + 1))) = v(x^((k)))$. This gives
$
  v(x) = B v(x) + v(f) ==> v(f) = (I - B) v(x) = (I - B) A^(-1) v(b)
$

This condition is necessary, but not sufficient. On top of consistency, we need *convergence*.

#definition(title: "Error")[
  At step $k$ we define the error as
  $
    v(e^((k))) = v(x) - v(x^((k)))
  $
  where $v(x)$ is the true solution.
]

For convergence to hold we want the norm of the error to go to zero as $k -> oo$. This in practice
gives
$
  norm(v(e^(k + 1))) & = norm(v(x) - v(x^(k + 1))) \
                  & = norm(v(x) - B v(x^(k)) - v(f)) \
                  & = norm(v(x) - B v(x^(k)) - (I - B)v(x)) \
                  & = norm(B v(e^((k)))) \
                  & <= norm(B) norm(v(e^((k))))
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

Ideally we want to stop when $norm(v(x) - v(x^((k))))/norm(v(x)) <= epsilon$, however we don't know the true
solution $v(x)$.

#definition(title: "Conditioning number")[
  Given a matrix $A$, its conditioning number is defined as
  $
    kappa(A) = norm(A) dot.op norm(A^(-1))
  $
]

A method which can be used in practice is
$
  norm(v(x) - v(x^((k))))/norm(v(x)) <= kappa(A) norm(v(r^((k))))/norm(v(b))
  ==> kappa(A) norm(v(r^((k))))/norm(v(b)) < epsilon
$
or another one
$
  norm(v(delta^((k)))):= norm(v(x^((k + 1))) - v(x^((k)))) <= epsilon
$
and it can be shown that
$
  norm(v(e^((k)))) <= 1 / (1- rho(B)) norm(v(delta^((k))))
$

=== Preconditioning

We introduce an SPD matrix $P^(-1)$ and we solve
$
  P^(-1/2) A P^(-1/2) v(z) = P^(-1/2) v(b)
$
Then $v(x) = P^(1/2) v(z)$.

We try to chose $P$ such that $kappa(P^(-1/2) A P^(-1/2)) << kappa(A)$.

$
  v(x^((k + 1))) = v(x^((k))) + P^(-1) v(r^((k)))
$
where $v(r^((k))) = v(b) - A v(x^((k)))$ and $P$ is the preconditioner of the residual. In practice we never
invert $P$, we solve for $P v(z^((k))) = v(r^((k)))$.

We can also write this in matrix form:
$
  A = P - N
$
This also preserves sparsity

== Richardson method

$P^(-1) v(r^((k)))$ gives us the direction of the residual. We can however also add some coefficients
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

We can now exploit the fact that $A$ is SPD. This means that $Phi(v(y)) = 1/2 v(y)^T A v(y) - v(y)^T v(b)$ (call it
the _energy function_) is convex, and the unique minimum is given by $grad Phi(v(y)) = v(0) = A v(y) - v(b)$,
which is the solution of our system.

This means that we want to set the residual to
$
  v(r^((k))) = - grad Phi(v(x^((k)))) = v(b) - A v(x^((k)))
$

It turns out that two consecutive residuals are always orthogonal. This can be proven by just
multiplying $v(r^((k)))$ with $v(r^((k + 1)))$.

Then our problem reduces to
$
  v(x^((k + 1))) = v(x^((k))) - alpha_k grad Phi(v(x^((k))))
$

To compute $alpha_k$ we can just expand $Phi(v(x^((k + 1))))$ and look at it as a function of $alpha_k$
and looking for its minimizer. Doing the algebra, we find out that $Phi(v(x^((k + 1))))$ is a 1
dimensional parabola in $alpha_k$, which is is trivial to minimize.

This gives us
$
  alpha_k = ((v(r^((k))))^T v(r^((k))))/((v(r^((k))))^T A v(r^((k))))
$

This gives us a full algorithm:
- Compute $alpha_k$ as above $--> bigO(n)$ if $A$ is sparse.
- $v(x^((k + 1))) = v(x^((k))) + alpha_k v(r^((k))) --> bigO(n)$.
- $v(r^((k + 1))) = v(b) - A v(x^((k + 1))) = v(b) - A(v(x^((k))) + alpha_k v(r^((k)))) = v(r^((k))) - alpha_k A v(r^((k)))
  --> bigO(n)$. Note that $A v(r^((k)))$ has already been computed when computing $alpha_k$, if we
  reuse it we can save a matrix-vector multiplication.

=== Convergence

This method, in precise arithmetic, always converges.

#definition(title: "Matrix-induced norm")[
  Let $A$ be an SPD matrix. For a vector $v(z)$ we define its norm induced by $A$ as
  $
    norm(v(z))_A = sqrt(v(z)^T A v(z)) quad forall v(z) in RR^n
  $
]


The speed of convergence depends on $A$:
$
  norm(v(e^((k + 1))))_A <= (kappa(A) - 1)/(kappa(A) + 1) norm(v(e^((k))))_A ==>
  norm(v(e^((k + 1))))_A <= ((kappa(A) - 1)/(kappa(A) + 1))^k norm(v(e^((0))))_A
$

=== Adding back the preconditioner

Now let $P != I$
$
  A v(x) = v(p) ==> P^(1/2) A P^(-1/2) v(y) = P^(1/2) v(b) quad "with" v(y) = P^(1/2) v(x)
$
where the bound for the error is

$
  norm(v(e^((k + 1))))_A <= [(kappa(P^(1/2) A P^(-1/2)) - 1)/(kappa(P^(1/2) A P^(-1/2)) + 1)]
  norm(v(e^((k))))_A
$

This has the issue that, in theory, we would need both to compute $P^(1/2)$ and invert it: both very
expensive operations. However, in practice, we can avoid fully materializing either $P^(1/2)$ or its
inverse: we just need the effect of $P$ on the residual.

Indeed, we can define the algorithm as

#algorithm(title: "Preconditioned Richardson method")[
  + Given $v(x^((0)))$
  + Compute $v(r^((0))) = v(b) - A v(x^((0)))$
  + *While* `Stopping condition`
    + Solve $P v(z^((k))) = v(r^((k)))$ for $v(z^((k)))$
    + Compute $alpha_k = ((v(z^((k))))^T v(r^((k))))/((v(z^((k))))^T A v(z^((k))))$
    + Update $v(x^((k + 1))) = v(x^((k))) + alpha v(z^((k)))$
    + Update $v(r^((k + 1))) = v(r^((k))) - alpha_k A v(z^((k)))$
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
  Let $A$ be a SPD matrix and $v(d^((0))), ..., v(d^((k))) in RR^n$. We say that $v(d^((k+1)))$ is
  $A$-orthogonal (or $A$-conjugate) to all the previous directions if
  $
    (v(d^((k+1))), v(d^((j))))_A := (v(d^((k+1))))^T A v(d^((j))) = 0 quad forall j <= k
  $
]

We try to impose that our new sequence of directions $v(d^((k)))$, which we use in place of the
residuals, to be $A$-orthogonal to each other.

This fixes the issue we saw in the gradient method where each update was orthogonal just to the
preceding one, leading to a zig-zag pattern.

#theorem(title: "Conjugate gradient method error")[
  $
    norm(v(e^((k))))_A <= (2 c^k)/(1 + c^(2k)) norm(v(e^((0))))_A quad "with" c = (sqrt(K(A)) - 1)/(sqrt(K(A))+1)
  $
]

This also has the advantage that $v(d^((k)))$ form a basis of $RR^n$, which means that the method
converges in exactly $n$ steps.

The problem is then reframed as "finding iteratively a base to $RR^n$ in order to represent $v(x)$".

At each step we need to find $v(d^((k+1)))$ given the current residuals and the previous direction. The
next direction is given by
$
  v(d^((k + 1))) = v(r^((k + 1))) - beta_k v(d^((k)))
$<eq:cg-short-recurrence>
and to compute $beta_k$ we impose that
$
  (v(r^((k+1))) - beta v(d^((k))))^T A v(d^((k))) = 0 <==>
  beta_k = ((v(r^((k+1))))^T A v(d^((k))))/((v(d^((k))))^T A v(d^((k))))
$
we will see later that this is enough to impose $A$-orthogonality across all previous directions as
well.


#algorithm(title: "Preconditioned conjugate gradient method")[
  + Given $v(x^((0)))$.
  + Compute $v(r^((0))) = v(b) - A v(x^((0)))$.
  + Set $v(d^((0))) = v(r^((0)))$.
  + *While* (`Stopping criterion`):
    + Compute
      $ alpha_k = ((v(z^((k))))^T v(r^((k))))/((v(z^((k))))^T A v(z^((k)))) $
    + Compute $v(x^((k+1))) = v(x^((k))) + alpha_k v(d^((k)))$.
    + Compute $v(r^((k+1))) = v(r^((k))) - alpha_k A v(d^((k)))$.
    + Solve $P v(z^((k + 1))) = v(r^((k+1)))$ for $v(z^((k+1)))$.
    + Compute
      $ beta_k = ((A v(d^((k))))^T v(z^((k+1))))/((A v(d^((k))))^T A v(d^((k)))) $
    + Set $v(d^((k+1))) = v(z^((k+1))) - beta_k v(d^((k)))$.
  + *End*
]<alg:cg>

#proposition[
  Let $A in RR^(n times n)$ be an SPD matrix, choose $v(x^((0))) in RR^n$ arbitrarily and compute
  $v(r^((0))) = v(b) - A v(x^((0)))$. By running @alg:cg in exact arithmetic, at each $k$, the vectors
  generated up to $k + 1$ satisfy:
  + *Full conjugacy of directions*: $v(d^((i))) A v(d^((j))) = 0$ for all $i != j$ and $i,j <= k+1$.
  + *Full orthogonality of residuals*: $(v(r^((i))))^T v(r^((j))) = 0$ for all $i != j$ and $i,j <= k+1$.
  + *Common growing subspace*: $"span"{v(d^((0))), ..., v(d^((k+1)))} = "span"{v(r^((0))), ..., v(r^((k+1)))}$.
  + *Short recurrence*: each $v(d^((k+1)))$ is build only from @eq:cg-short-recurrence, no earlier
    vector needs to be read.
]
#proof[Skip.]

== Krylov space methods

Consider the Richardson method with $alpha=1$. Can write
$
  r^((k+1)) & = v(b) - A v(x^((k + 1))) = v(b) - A (v(x^((k))) + v(r^((k)))) \
            & = v(b) - A v(x^((k))) - A v(r^((k))) = v(r^((k))) - A v(r^((k)))
$
Similar arguments can be made for all methods we discussed so far. This means that $v(r^((k + 1)))$ is
a linear polynomial of $v(r^((k)))$.

This means we can can recursively write each $v(r^((k)))$. Then the residuals lie on
$
  v(x^((0))) + "span"{ v(r^((0))), A v(r^((0))), ..., A^(k-1) v(r^((0))) }
$
where the space spanned by this vectors is a Krylov space.

#definition(title: [Krylov space])[
  The $k$-th Krylov space generated by $A$ from $y != v(0)$ is
  $
    cal(K)_k (A, v(y)) := "span"(v(y), A v(y), ..., A^(k-1) v(y))
  $
  and $cal(K)_1 subset.eq cal(K)_2 subset.eq ...$.
]

#lemma(title: [Existence of the grade $nu$])[
  There exists a positive integer $nu$ such that
  $
    dim(cal(K)_s (A, v(y))) = cases(
      s quad & "if"s <= nu,
      nu quad & "if"s >= nu,
    )
  $
]
#proof[Skip.]

#lemma(title: [Characterization of the grade])[
  The grade $nu$ is characterized by
  $
    nu(v(y), A) = min {s : A^(-1) v(y) in cal(K)_s (A, v(y))}
  $
]
#proof[Skip.]

Given these two lemmas we can conclude that, since the exact solution $v(x)$ of the system is defined
as $v(x) = v(x^((0))) + A^(-1) v(r^((0)))$, we have
$
  v(x) in v(x^((0))) + cal(K)_nu (A, v(r^((0))))
$

== Non symmetric systems

To solve non symmetric systems we still use Krylov space solvers, however the theory is not as
advanced.

=== Biconjugate gradient method

This is an extension of the conjugate gradient method for non-symmetric matrices.

Let the dual problem be
$
  v(x)^T A^T = v(b)^T
$
and look at the Krylov space generated by the dual and its shadow residuals (i.e. the residuals of
the dual).

The goal of this algorithm is to keep the residual and the shadow residuals orthogonal to each other
at all iterations.

#algorithm(title: [BiCG])[
  + Pick a column vector $v(x^((0)))$ and a row vector $v(hat(x)^((0)))$.
  + Compute initial residuals $v(r^((0))) = v(b) - A v(x^((0)))$ and
    $v(hat(r)^((0))) = v(hat(b)) - v(hat(x)^((0))) A^T$.
  + Set directions $v(d_0) = v(r^((0)))$ and $v(hat(d)_0) = v(hat(r)^0)$.
  + *While* (`Stopping condition`):
    + Compute the step length
      $
        alpha_k = (v(hat(r)^((k))) v(r^((k))))/(v(hat(d)_k) A v(d_k))
      $
    + Update $v(x^((k+1))) = v(x^((k))) + alpha_k v(d_k)$ and
      $v(hat(x)^((k+1))) = v(hat(x)^((k))) + alpha_k v(hat(d)_k)$ and recompute the residuals.
    + Compute
      $
        beta_k = (v(hat(r)^((k + 1))) v(r^((k+1))))/(v(hat(r)^((k))) v(r^((k))))
      $
    + Update the directions $v(d_(k + 1)) = v(r^((k + 1))) + beta_k v(d_k)$ and
      $v(hat(d)_(k + 1)) = v(hat(r)^((k + 1))) + beta_k v(hat(d)_k)$
  + *End*.
]

This method is twice as expensive as the regular CG method.

=== GMRes Method

The Generalized Minimum Residual method is the most used in practice in this class of problems.

The idea of this method is to find the next guess $v(x^((k)))$
$
  v(x^((k))) in v(x^((0))) + cal(K)_k (A, v(r^((0)))) "minimizing" norm(v(r^((k))))
$

The naive base of the Krylov space however is numerically very bad, and those vectors become almost
linearly independent very quickly. The idea to fix this is to use Arnoldi's iteration, i.e. run
Gram-Schmidt on the Krylov sequence to produce an orthonormal basis of the space.

#algorithm(title: "GMRES")[
  + Choose $v(x^((0)))$.
  + Compute $v(r^((0))) = v(b) - A v(x)$.
  + *While* (`Stopping condition`)
    + Compute $v(q_k)$ with a suitable method.
    + Form $Q_k$ as the $n times k$ matrix formed by $v(q_1), ..., v(q_k)$.
    + Find $v(y^((k)))$ which minimize $norm(v(r^((k))))_2$.
    + Compute $v(x^((k+1))) = v(x^((0))) + Q_k v(y^((k)))$.
  + *End*
]

The main issue is that $Q_k$ becomes a huge, dense matrix; in practice after a few iterations we
start over with a fresh $Q_k$.

= Eigenvalue problems

In this section, given a matrix $A in CC^(n times n)$, we want to find the set of
$(lambda, v) in CC times CC^n$ (with $v(v) != v(0)$) which solves
$
  A v(v) = lambda v(v)
$

Note that eigenvectors are defined up to a constant:
$
  A v = lambda v <==> A (c v(v)) = lambda (c v(v))
$
therefore, for convenience, we will impose the extra condition
$
  norm(v(v_i)) = 1
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
  For any eigenpair $(lambda_i, v(v_i))$ of $A$
  $
    lambda_i = (v(v_i)^H A v(v_i))/(v(v_i)^H v(v_i))
  $
]<prop:rayleigh>

#proof[
  Start by the eigenvalues equation.
  $
    A v(v) = lambda v(v) <==> lambda v(v)^H v(v) = v(v)^H A v(v) <==> lambda = (v(v)^H A v(v))/(v(v)^H v(v))
  $

  Note that $v(v)^H v(v)$ is the norm of $v(v)$, therefore always non-zero for a non-zero $v(v)$.
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
  Let $(lambda, v(y))$ be an eigenpair of $B$.
  $
    B y = lambda y <==> T^(-1) A T v(y) = lambda v(y) <==> A v(w) = lambda v(w)
  $
  with $v(w) = T v(y)$.
]

Therefore the plan is to massage $A$ with some $T$ such that the problem becomes easy to solve. This
works well if we need the full spectrum, however massaging with $T$ loses sparsity and it is often
hard to compute the right $T$.

=== Blackboard method

To compute eigenvalues on the blackboard we usually solve
$
  (A - I lambda) v(v) = v(0)
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
  + Let $v(x^((0)))$ be the initial guess, such that $norm(v(x^((0)))) = 1$.
  + *While* (`Stopping criterion`)
    + Compute $v(y^((k+1))) <-- A v(x^((k)))$
    + Normalize $v(x^((k+1))) <-- (v(y^((k+1))))/norm(v(y^((k+1))))$
    + Use the @prop:rayleigh to compute $nu^((k+1)) = [v(x^((k+1)))]^H A v(x^((k+1)))$.
  + *End*
]

#theorem[
  Let $A$ be diagonalizable and $lambda_1$ (being the eigenvalue with largest modulus) is isolated.
  Then
  $
    lim_(k -> oo) v(x^((k))) = v(v_1) wide
    lim_(k -> oo) nu^((k+1)) = lambda_1
  $
]
#proof[
  Since $A$ is diagonalizable, the set of eigenvectors for a basis for $C^n$. Which means that for
  any $v(x^((0)))$ can be written in that basis:
  $
    v(x^((0))) = sum^n_(i = 1) alpha_i v(v_i) wide "for suitable" alpha_1, ..., alpha_n
  $
  We need to assume that $alpha_1 != 0$, which is true with probability $1$ for a random $v(x^((0)))$.

  We first prove this intermediate lemma:

  #lemma[
    $
      A^k v(x^((0))) = sum^n_(i = 1) alpha_i lambda_i^k v(v_i)
    $
  ]<lem:power-sum>
  #subproof(<lem:power-sum>)[
    We prove this by induction on the exponent $k$.

    In the base case $k = 0$, assume that $A^0 = I$ and $lambda^0 = 1$. Then
    $v(x^((0))) = sum^n_(i = 1) alpha_i v(v_i)$ is trivially true by construction.

    For the inductive step we assume that the statement is true at $k$ and try to prove it for
    $k + 1$. Start from the expression at $k$ and multiply by $A$:
    $
      A^(k+1) v(x^((0))) & = A sum^n_(i = 1) alpha_i lambda_i^k v(v_i) = sum^n_(i = 1) alpha_i lambda_i^k A v(v_i) \
      & = sum^n_(i = 1) alpha_i lambda_i^k (lambda_i v(v_i)) = sum^n_(i = 1) alpha_i lambda_i^(k+1) v(v_i) \
    $

    This concludes the proof of the first lemma.
  ]

  From the result of the lemma we decouple $i = 1$ from the sum and pull out $alpha_1 lambda_1$ (we
  can do this since we are assuming that $alpha_1 != 0$).
  $
    A^k v(x^((0))) & = alpha_1 lambda_1^k v(v_1) + sum^n_(i = 2) alpha_i lambda_i^k v(v_i) \
                & = alpha_1 lambda_1^k [ v(v_1) + underbrace(
                      sum^n_(i = 2) alpha_i/alpha_1 (lambda_i/lambda_1)^k v(v_i),
                      := v(r^((k)))
                    ) ] \
                & = alpha_1 lambda_1^k ( v(v_1) + v(r^((k))))
  $
  where $v(r^((k)))$ is the residual.

  #lemma[
    $
      lim_(k -> oo) norm(v(r^((k)))) = 0
    $
  ]<lem:residual-limit>
  #subproof(<lem:residual-limit>)[
    Since $abs(lambda_i/lambda_1) <= abs(lambda_2 / lambda_1)$ we can write
    $
      norm(v(r^((k)))) & = norm(sum^n_(i = 2) alpha_i/alpha_1 (lambda_i/lambda_1)^k v(v_i)) \
                    & <= abs((lambda_2/lambda_1))^k
                      sum^n_(i = 2) abs(alpha_i/alpha_1) underbrace(
                        norm(v(v_i)), =
                        1
                      ) \
    $
    and since $abs(lambda_1) > abs(lambda_2)$ the limit as $k -> oo$ is zero.
  ]

  Note that right now $A^k v(x^((0)))$ does not converge as $k -> oo$: indeed $lambda^k$ either
  diverges to $oo$, $0$, or has a rotating phase. This is where normalization comes in.

  $
    v(x^((k + 1))) & = (A^k v(x^((k)))) / norm(A^k v(x^((k)))) \
                & = (alpha_1 lambda_1^k)/(abs(alpha_1) abs(lambda_1^k))
                  (v(v_1) + v(r^((k))))/norm(v(v_1) + v(r^((k)))) \
                & = e^(i theta_k) (v(v_1) + v(r^((k))))/norm(v(v_1) + v(r^((k))))
  $
  and as $k -> oo$ we get
  $
    v(x^((k + 1))) = e^(i theta_k) v(v_1)/norm(v(v_1))
  $
  where the error decays as $bigO(abs(lambda_2/lambda_1)^k)$.

  When we reach the stopping condition $v(x^((k)))$ is sufficiently close to $v(x_1)$ that we can use
  @prop:rayleigh to estimate the eigenvalue. The error also decays as
  $bigO(abs(lambda_2/lambda_1)^k)$.
]

=== Deflation

Assume now we have computed the largest eigenvalue $lambda_1$ and we want to compute the next
largest $lambda_2$.

To do so, we want to find a similarity transformation $S$ which satisfies $S v(v_1) = alpha v(e_1)$, where
$v(e_1)$ is the first element of the canonical basis, such that
$
  S A S^(-1) = mat(lambda_1, v(b)^T; 0, B)
$
where $B$ is a submatrix with the same spectrum of $A$ without $lambda_1$.

To recover the right eigenvector we compute $v(v_2) = S^(-1) vec(alpha, v(z_2))$.

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
  + Let $v(q^((0)))$ such that $norm(v(q^((0)))) = 1$
  + For each iteration
    + Solve $A v(z^((k+1))) = v(q^((k)))$
    + Compute $v(q^((k + 1))) <-- (v(z^((k+1))))/norm(v(z^((k+1))))$
    + $sigma^((k+1)) <-- [v(q^((k+1)))]^H A v(q^((k+1)))$
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
  M_mu v(w) = xi v(w) & <==> (A - mu I) v(w) = xi v(w) \
                & <==> A v(w) = (mu - xi) v(w)
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
  + Let $v(a_1), ..., v(a_n)$ be a set of vectors (could be the columns of some matrix $A$).
  + *For* $j = 1, ..., n$:
    + Let $v(w_j) <- v(a_j)$.
    + *For* $i = 1, ..., j-1$:
      + *If* `Modified GS`:
        + Let $r_(i, j) <- v(q_i)^H v(w_j)$, this is more numerically stable and yields the same results.
      + *Else*:
        + Let $r_(i, j) <- v(q_i)^H v(a_j)$.
      + *End*
      + Let $v(w_j) <- v(w_j) - r_(i, j) v(q_i)$.
      + *If* i = j:
        + Assign $r_(j, j) <- norm(v(w_j))$.
      + *End*
      + Normalize $v(q_j) <- v(w_j) / norm(v(w_j))$.
    + *End*
  + *End*
]

This takes $bigO(m n^2)$.

== Schur decomposition

We want to compute $U A U^H = T$ such that $U$ is unitary and $T$ is upper triangular, so that
$sigma(A) = sigma(T)$.

Columns of $U$ are called *Schur vectors*. In general, only $v(u_1)$ is an eigenvector of $A$.

#definition(title: [Invariant subspace])[
  Let $cal(S) subset.eq V$ be a subspace of $V$. We say $cal(S)$ is an invariant with respect to
  some matrix $A$ if
  $
    v(v) in cal(S) ==> A v(v) in cal(S)
  $
]

Notably, each eigenvector spans an invariant subspace of its matrix. A weaker version also holds for
Schur vectors.

#proposition(title: [Schur vectors span invariant subspaces])[
  Let $v(u_1), ..., v(u_n)$ be the Schur vectors of $A$. Then
  $
    cal(S)_k = angle(v(u_1), ..., v(u_k)) wide forall k in 1, ..., n
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

It can be proven that this decomposition exists and is unique given the first column $v(q_1)$ of $Q$.

The decomposition is obtained by imposing $A Q = Q T$ column by column:
$
  A v(q_n) = beta_(n - 1) v(q_(n - 1)) + alpha_n v(q_n) + beta_(n + 1) v(q_(n + 1)) \
  "by orthogonality"
  ==> cases(
    alpha_n & = v(q_n)^H A v(q_n),
    beta_n & = v(q_(n + 1))^H A v(q_n)
  )
$

#algorithm(title: "Lanczos algorithm")[
  + Let $v(r_0) = v(q_1)$, $v(q_0) = v(0)$ and $beta_0 = 1$.
  + *For* ($k = 1, ..., n$)
    + *If* ($beta_(k - 1) = 0$)
      + *Break*
    + *End*
    + Compute $v(q_k) = v(r_(k - 1))/beta_(k-1)$.
    + Compute $alpha_k = v(q_k)^T A v(q_k)$.
    + Compute $v(r_k) = (A - alpha_k) v(q_k) - beta_(k - 1) v(q_(k - 1))$.
    + Let $beta_k = abs(v(r_k))$.
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

Let the residual be $v(r) = v(b) - A v(x)$. If the residual is the minimum in the least square sense, then it
is orthogonal to the image of $A$. We can impose this condition by setting $A^T v(r) = v(0)$ and
substituting $v(r)$ we get
$
  A^T A v(x) = A^T v(b)
$

The same result can be obtained analytically: let $Phi(v(x)) = norm(v(b) - A v(x))^2$, then
$
     min_x Phi(v(x)) & <==> grad Phi(v(x)) = v(0) \
      grad Phi(v(x)) & = grad (v(b) - A v(x))^T (v(b) - A v(x)) \
                  & = grad (v(b)^T v(b) - v(b)^T A v(x) - v(x)^T A^T v(b) + v(x)^T A^T A v(x)) \
                  & = - v(b)^T A - A^T v(b) + 2 A^T A v(x) \
                  & = 2 A^T A v(x) - 2 A^T v(b) \
  grad Phi(v(x)) = v(0) & <==> A^T A v(x) = A^T v(b)
$

#remark[
  If $A$ is full-rank $A^T A$ is SPD.
]
#proof[
  We want to show that $v(x)^T A^T A v(x) > 0$ for all $v(x) in R^n without {v(0)}$. But
  $v(x)^T A^T A v(x) = norm(A v(x))^2$, so that, if $A$ has full rank, $A v(x) != v(0)$ for all $v(x) != v(0)$. By the
  properties of the norm we have $norm(v(y)) > 0$ for all $v(y) != v(0)$, showing that $A A^T$ is positive
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
matrices, since $norm(Q^T (A v(x) - v(b)))^2 = norm(A v(x) - v(b))$.

#theorem[
  Let $v(x)^* = hat(R)^(-1) hat(Q)^T v(b)$. Then $v(x)^*$ is the solution to the system in the least squares
  sense. The minimum value is $Phi(v(x)^*) = sum_(i = n + 1)^m [(Q^T v(b))_i]^2$.
]

#proof[
  Compute the QR decomposition of $A$: $A = Q R$.
  $
    norm(A v(x) - v(b))^2 & = norm(Q^T ( A v(x) - v(b)))^2 \
                    & = norm(Q^T (Q R v(x) - v(b)))^2 \
                    & = norm(Q^T Q R v(x) - Q^T v(b))^2 \
                    & = norm(R v(x) - Q^T v(b))^2 \
                    & = norm(hat(R) v(x) - hat(Q)^T v(b))^2 + sum_(i = n + 1)^m [(Q^T v(b))_i]^2
  $
  In the last step we split $Q$ and $R$ in their reduced forms: indeed $R$ is zero after $n$, so
  that all those terms cancel, while the terms involving $Q$ can be brought out into their own term.

  We note that the tail elements do not involve $v(x)$, so there is nothing we can do about them, we
  are left with minimizing $norm(hat(R) v(x) - Q^T v(b))$. This happens when
  $hat(R) v(x) = Q^T v(b) <==> v(x) = R^(-1) Q^T v(b)$ as stated.
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
  A V = U Sigma <==> A v(v_i) = sigma_i v(u_i)
$
we see that
$
  ker(A) = "span"(v(v_(r+1)), ..., v(v_n)) wide "range"(A) = "span"(v(u_1), ..., v(u_r))
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
    v(x)^* = A^dagger v(b)
  $
]

#proof[
  Start by a change of variable: define $v(w) := V^T v(x)$ so that $v(x) = V v(w)$. Then
  $
    norm(A v(x) - v(b))^2 & = norm(A V v(w) - v(b))^2 \
                    & = norm(U Sigma V^T V v(w) - v(b))^2 \
                    & = norm(U Sigma v(w) - v(b))^2 \
                    & = norm(Sigma v(w) - U^T v(b))^2 \
  $
  Now we split the norm in the components before $r$ and after $r$:
  $
    norm(Sigma v(w) - U^T v(b))^2 & = sum^r_(i = 1) [sigma_i w_i - (U^T v(b))_i]^2
                              + sum^p_(i = r+1) [(U^T v(b))_i]^2
  $
  Since $sigma_i > 0$ when $i <= r$ we get that $w_i = (U^T v(b))/sigma_i$ for all $i <= r$. For
  $i > r$ we can choose $w_i$ freely, but minimizing the norm tells us that they should all be set
  to zero.

  This gives $v(w)^* = Sigma^dagger U^T v(b)$, meaning
  $
    v(x)^* = V v(w)^* = V Sigma^dagger U^T v(b) = A^dagger v(b)
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
  A_h v(e_h^((k))) = v(r_h^((k)))
$
(where $h$ is the grid spacing, more on that later) and use it to correct the solution.

This is particularly useful for using the weighted Jacobi method to solve differential equations.
After one iteration the error updates as $v(e^((k+1))_h) = B v(e^((k))_k)$ for some $B$ we don't really
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
+ Solve the problem on the fine grid and compute the residual $v(r_h)$.
+ Restrict the residual to the coarser grid $v(r_(2 h))$.
+ Solve the error equation in the coarser grid $A_(2 h) v(e_(2 h)) = v(r_(2 h))$, where
  $A_(2 h) := I^(2h)_h A_h I_(2h)^h$.
+ Interpolate the error back to the finer grid $v(e_h)$.
+ Correct the estimate $v(x_h) <- v(x_h) + v(e_h)$.

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

The idea is that, for a smooth error $v(e)$,
$
  A v(e) approx v(0) <==> a_(i i) e_i + sum_(j in N_i) a_(i, j) e_j approx 0
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

Consider the linear system $A v(x) = v(b)$. Split $A$ in subdomains $A = union.big_i A_i$, then $R_i$ is
the *extraction operator* where $R_i v(x)$ is the elements of $v(x)$ which belong to subdomain $i$.

#algorithm(title: [Additive Schwartz preconditioner])[
  + Use some iterative solver to get a residual $v(r^((k))) = v(b) - A v(x^((k)))$.
  + For each subdomain $i$
    + Restrict the residual to $R v(r_i^((k)))$.
    + Solve the error equation for a correction $delta_i$:
      $
        A_i v(delta_i) = R v(r_i^((k))) ==> v(delta_i) = A^(-1)_i R_i v(r^((k)))
      $
    + Extend the correction back by multiplying by $R^T_i$:
      $
        R_i^T v(delta_i) = R_i^T A_i^(-1) R_i v(r^(k))
      $
  + This gives
    $
      v(x^((k+1))) = v(x^((k))) + [sum_i R_i^T A_i^(-1) R_i] v(r^((k)))
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
  v(vec(x_I, x_Gamma)) = v(vec(b_I, b_Gamma))
$

Since the interior of the subdomains are not connected, $A_(I I)$ is block-diagonal, so solving in
each subdomain can be done in parallel. We get
$
  v(x_I) = A^(-1)_(I I) (v(b_I) - A_(I Gamma) v(x_Gamma))
$
By substituting that in the second row we get
$
  underbrace((A_(Gamma Gamma) - A_(I Gamma)^T A^(-1)_(I I) A_(I Gamma)), =: S)v(x_Gamma)
  = v(b_Gamma) - A_(I Gamma)^T A^(-1)_(I I) v(b_I)
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
  L v(y) = v(b) --> U v(x) = v(y)
$
just by using forward and backwards substitution.

This is also nice since the factorization can then be cached and reused for subsequent solves with a
different $v(b)$.

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

