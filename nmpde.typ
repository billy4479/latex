#import "lib/template.typ": *
#import "lib/theorem.typ": *
#import "lib/algorithm.typ": *
#import "lib/utils.typ": *
#import "@preview/lovelace:0.3.1": *

#show: template.with(
  titleString: "Numerical Methods for Partial Differential Equations",
  author: "Giacomo Ellero",
  date: "A.Y. 2026/2027",
  font: "",
)

#show: thm-init
#show: alg-init

#let vu(it) = $upright(bold(it))$
#let vb(it) = math.bold(it)
#let va(it) = math.arrow(it)

= Introduction

== Refresher: derivatives on $RR^d$

Let $Omega subset RR^d$ be open, $u: Omega -> RR$ a scalar field, and $va(F): Omega -> RR^d$ a
vector field. Unless stated otherwise, assume the fields have continuous derivatives of the order
appearing in each formula.

Notation: $C^k (overline(Omega), RR^d)$ is the set of continuously $k$-times differentiable
functions with domain $overline(Omega)$ and image $RR^d$.

=== Gradients

#definition(title: [Gradient and directional derivative])[
  The gradient of $u$ is
  $
    grad u = mat(pdv(u, x_1), ..., pdv(u, x_d))^T.
  $
  For a unit vector $va(e)$, the directional derivative is
  $
    D_(arrow(e)) u(x)
    = lim_(t -> 0) (u(x + t va(e)) - u(x))/t
    = grad u(x) dot.op va(e).
  $
]

#definition(title: [Jacobian and Hessian])[
  The Jacobian of $va(F)$ and the Hessian of $u$ are the matrices
  $
    (D va(F))_(i j) = pdv(F_i, x_j),
    quad (D^2 u)_(i j) = pdv(u, x_i, x_j),
    quad i, j = 1, dots, d.
  $
  In particular, $D^2 u = D(grad u)$ when $u in C^2(Omega)$.
]

#theorem(title: [Schwarz's theorem])[
  If $u in C^2(Omega)$, then mixed second derivatives commute:
  $
    pdv(u, x_i, x_j) = pdv(u, x_j, x_i).
  $
  Consequently, the Hessian $D^2 u$ is symmetric.
]

#proof[Skip.]

=== Divergence

#definition(title: [Divergence])[
  The divergence of $va(F)$ is the scalar field
  $
    div va(F) = sum_(i=1)^d pdv(F_i, x_i) = tr(D va(F)).
  $
]

#definition(title: [Laplacian])[
  The Laplacian of $u$ is
  $
    Delta u = div(grad u)
    = sum_(i=1)^d pdv(pdv(u, x_i), x_i) = tr(D^2 u).
  $
  For a vector field, the Laplacian is applied componentwise.
]

#definition(title: [Normal derivative])[
  At a smooth point of $partial Omega$, let $va(n)$ be the outward unit normal. The normal
  derivative is
  $
    pdv(u, n) = grad u dot.op va(n).
  $
  Thus $va(F) dot.op va(n)$ is the outward normal flux of $va(F)$.
]

#theorem(title: [Product and chain rules])[
  For scalar fields $u, v, a$, a vector field $va(F)$, a differentiable function $g: RR -> RR$, and
  a differentiable map $va(Phi): U -> Omega$,
  $
                  grad(u v) & = u grad v + v grad u, \
               div(u va(F)) & = grad u dot.op va(F) + u div va(F), \
              div(a grad u) & = grad a dot.op grad u + a Delta u, \
                 grad(g(u)) & = g'(u) grad u, \
    grad(u compose va(Phi)) & = (D va(Phi))^T ((grad u) compose va(Phi)).
  $
]

#proof[Skip.]

For the integral identities below, assume $Omega$ is bounded with $C^1$ boundary and $va(n)$ is its
outward unit normal. The fields and their required derivatives are assumed continuous up to the
boundary. The same identities hold on piecewise smooth domains, with the normal defined on each
smooth face.

#theorem(title: [Divergence theorem (Gauss)])[
  For $va(F) in C^1(overline(Omega); RR^d)$,
  $
    integral_Omega div va(F) dif x
    = integral_(partial Omega) va(F) dot.op va(n) dif S.
  $
]
#proof[Skip.]

#theorem(title: [Integration by parts])[
  For $u in C^1(overline(Omega))$ and $va(F) in C^1(overline(Omega); RR^d)$,
  $
    integral_Omega grad u dot.op va(F) dif x
    = - integral_Omega u div va(F) dif x
    + integral_(partial Omega) u va(F) dot.op va(n) dif S.
  $
  In particular, for each $i = 1, dots, d$,
  $
    integral_Omega pdv(u, x_i) v dif x
    = - integral_Omega u pdv(v, x_i) dif x
    + integral_(partial Omega) u v n_i dif S.
  $
]
#proof[Skip.]

#theorem(title: [Green's identities])[
  For $u, v in C^2(overline(Omega))$, the first identity is
  $
    integral_Omega grad u dot.op grad v dif x
    = - integral_Omega v Delta u dif x
    + integral_(partial Omega) v pdv(u, n) dif S.
  $
  The second identity is
  $
    integral_Omega (u Delta v - v Delta u) dif x
    = integral_(partial Omega)
    (u pdv(v, n) - v pdv(u, n)) dif S.
  $
]<thm:green>
#proof[Skip.]

#corollary(title: [Diffusion term in weak form])[
  For $a, v in C^1(overline(Omega))$ and $u in C^2(overline(Omega))$,
  $
    integral_Omega (-div(a grad u)) v dif x
    = integral_Omega a grad u dot.op grad v dif x
    - integral_(partial Omega) a pdv(u, n) v dif S.
  $
  The boundary term vanishes wherever $v = 0$ (Dirichlet test functions), while prescribed fluxes
  enter through $a pdv(u, n)$ (Neumann data).
]
#proof[Skip.]

== What is a PDE

#definition(title: [PDE])[
  A Partial Differential Equation is generally defined as
  $
    cases(
      L u = f wide & "in" Omega,
      "Boundary conditions" wide & "on" partial Omega
    )
  $
  where $f: RR^d -> RR$ is a known function, and $L$ is a generic differential operator. The goal is
  to find the function the function $u: RR^d -> RR$ satisfying the conditions.
]<def:pde-general>

== Weak problem

#let po = $("P")$
#let pw = $("PW")$

Lets start with an example. This representation is also called the *original problem* #po.

#example(title: [Laplace equation])[
  $
    cases(
      -laplace u = f wide & "in" Omega subset RR^d,
      "Boundaries conditions" wide & "on" partial Omega
    )
  $
  Here, going back to the general @def:pde-general, we have that $L = -laplace$,
  $laplace = div grad$ is the divergence of the gradient.
]
#solution[
  Now consider a test function $v: RR^d -> RR$ and multiply it on both sides:
  $
    -laplace u dot.op v = f dot.op v
  $
  then we integrate and use the first identity of @thm:green.
  $
        & - integral_Omega laplace u dot.op v = integral_Omega f dot.op v \
    ==> & integral_Omega grad u dot.op grad v - integral_(partial Omega) (grad u dot.op va(n)) v =
          integral_Omega f dot.op v
  $
  Then, we don't want any unknown integrating on the boundary. Since $v$ is a test function, we
  choose it such that $evaluated(v)_(partial Omega) = 0$, giving
  $
    integral_(partial Omega) (grad u dot.op va(n)) v = 0
  $
]

This is our *weak problem* #pw. Defined as
$
  integral_Omega grad u dot.op grad v = integral_Omega f dot.op v
  wide forall v: RR^d -> RR "s.t." evaluated(v)_(partial Omega) = 0
$

In order to solve this problem we need to relax it by considering the solution $u$ to be
approximated by a _finite element function_ $u_N tilde u$, i.e.
$
  abs("Image"(u_N)) = N
$
The problem we need to solve is then
$
  integral_omega grad u_N dot.op grad v_N = integral_omega f dot.op v_N
  wide forall v_N "s.t." evaluated(v_N)_(partial omega) = 0
$

Then, this finite version approximation, suggests we can represent $u_N$ in a finite-dimensional
vector space
$
  u_N(x) = sum^N_(i = 1) u_i phi_i (x) wide forall x in RR^d
$
where $phi_i$ is the basis of the space.

= Elliptic PDEs

#definition(title: [ADR])[
  The original problem is
  $
    cases(
      L u = - div (mu grad u) + va(b) dot.op grad u + sigma u = f wide & "in" Omega subset RR^d,
      u = phi wide & "on" Gamma_D,
      mu pdv(u, n) = psi wide & "on" Gamma_N
    )
  $
  where the data is
  $
    {mu, va(b), sigma, f, phi, psi, Omega, Gamma_D, Gamma_F}
  $
  and the solution is $u$.
]

#remark[
  $
    pdv(u, n) = grad u vec(n)
  $
]

In this PDE we can split $L u$ in three terms
$
  L u =
  underbrace(- div (mu grad u), "diffusion")
  + underbrace(va(b) dot.op grad u, "convection/transport")
  + underbrace(sigma u, "reaction/absortion")
$


Also note that the boundary $partial Omega = Gamma_D union Gamma_N$ (and
$Gamma_D inter Gamma_N = varnothing$), so we have different boundary conditions on different parts
of the boundary.

== Finding the Weak Problem <sec:elliptic-weak-formulation>

As in the Laplace equation, we start by multiplying both sides by a test function $v$ and follow the
same procedure (integrate + Green's).

$
                        & integral_Omega L u v = integral_Omega f v \
           ==>^"expand" & integral_Omega - div(mu grad u) v
                          + integral_Omega va(b) dot.op grad u dot.op v
                          + integral_Omega sigma u dot.op v
                          = integral_Omega f v \
          ==>^"Green's" & integral_Omega mu grad(u) grad v - integral_(partial Omega) mu grad u va(n) v
                          + integral_Omega va(b) dot.op grad u dot.op v
                          + integral_Omega sigma u dot.op v
                          = integral_Omega f v \
   ==>^"split boundary" & integral_Omega mu grad(u) grad v
                          - integral_(Gamma_D) mu grad u va(n) v
                          - integral_(Gamma_N) mu grad u va(n) v
                          + integral_Omega va(b) dot.op grad u dot.op v
                          + integral_Omega sigma u dot.op v
                          = integral_Omega f v \
  ==>^"substitute b.c." & integral_Omega mu grad(u) grad v
                          - integral_(Gamma_D) mu pdv(u, n) v
                          - underbrace(integral_(Gamma_N) psi v, "function of data")
                          + integral_Omega va(b) dot.op grad u dot.op v
                          + integral_Omega sigma u dot.op v
                          = integral_Omega f v \
$
We now impose $evaluated(v)_(Gamma_D) = 0$ so that we eliminate the solution from the boundary.

This leaves us with

$
  underbrace(
    integral_Omega mu grad(u) grad v
    + integral_Omega va(b) dot.op grad u dot.op v
    + integral_Omega sigma u dot.op v, a(u, v)
  )
  = underbrace(
    integral_Omega f v
    + integral_(Gamma_N) psi v, F(v)
  )
$<eq:def-a>

#definition(title: [Square integrable])[
  $
    L^2(Omega) := {v: Omega --> RR : integral_Omega v^2(x) dd(x) < infinity}
  $
]

#definition(title: [Sobder space])[
  $
    H^1 (Omega) = { v: Omega --> RR : v in L^2 (Omega)
      and (pdv(v, x_i) in L^2 (Omega)) forall i = 1, ... d}
  $

  Moreover
  $
    H^1_Gamma (Omega) = {v: Omega --> RR : v in H^1 and evaluated(v)_Gamma = 0}
  $
]

Our problem then reduces to reduces to
$
  "Find" u in H^1 "s.t." cases(
    a(u, v) = F(v) wide & "in" Omega,
    u = phi wide & "on" Gamma_D
  ) wide forall v in H_(Gamma_D)^1
$

Then, we extend $phi$ on the whole $Omega$ by defining $R: phi --> R phi$ such that
$
  cases(
    R phi in H^1 (Omega),
    evaluated(R phi)_(Gamma_D) = phi
  )
$

Now define
$
  u^0 = u - R phi
$
such that
$
  evaluated(u^0)_(Gamma_D) = evaluated(u)_(Gamma_D) - evaluated(R phi)_(Gamma_D)
  = phi - phi = 0
  ==> u^0 in H^1_(Gamma_D)
$
meaning we can decompose $u = u^0 + R phi$.

In turns, since $a$ is bilinear, we can split it as
$
  a(u^0, v) = a(R phi, v) = F(v)
$
but $R phi$ only depends on data, so $a(R phi, v)$ can be moved to the right.
$
  a(u^0, v) = tilde(F) (v)
$

#definition(title: [Search and test space])[
  We take
  $
    V = H^1_(Gamma_D) (Omega) = {v in H^1 (Omega) : evaluated(v)_(Gamma_D) = 0}.
  $
  If there is no Dirichlet boundary, $V = H^1 (Omega)$.
]<def:search-test-space>

== General analysis of Weak Problem

=== Norms

#definition(title: [Inner product on $H^1 (Omega)$])[
  Let $u, v in H^1 (Omega)$. The inner product can be defined as the convolution (?) of $u$ and $v$
  plus the convolution of their gradients.
  $
    (u, v)_(H^1 (Omega)) & := integral_Omega u v + integral_Omega grad u grad v \
                         & = (u, v)_(L^2 (Omega)) + (grad u, grad v)_(L^2 (Omega))
  $
]

#proposition(title: [$H^1 (Omega)$ norm])[
  $
    norm(v)_(h^1 (omega)) = sqrt(integral_omega v^2 + integral_omega (grad v)^2)
  $
]
#proof[
  From the definition of inner product on $H^1 (Omega)$ we have
  $
    norm(v)_(h^1 (omega)) & = sqrt((v, v)_(H^1 (Omega))) \
                          & = sqrt(norm(v)_(L^2 (Omega)) + norm(grad v)_(L^2 (Omega))) \
                          & = sqrt(integral_Omega v^2 + integral_Omega (grad v)^2)
  $
]

#definition(title: [Seminorm on $H^1 (Omega)$])[
  The seminorm on $H^1 (Omega)$ is denoted with $abs(dot)_(H^1 (Omega))$ and defined as
  $
    abs(v)_(H^1 (Omega)) := norm(grad v)_(L^2 (Omega)) = sqrt((grad v, grad v))
  $
]

From the definition we can easily see that
$
  abs(v)_(H^1 (Omega)) <= norm(v)_(H^1 (Omega))
$

#theorem(title: [Controlling the $L^2$ norm])[
  For every $v in H^1 (Omega)$,
  $
    norm(v)_(L^2 (Omega)) <= norm(v)_(H^1 (Omega)).
  $
  If $Omega$ is bounded, connected and Lipschitz, and $Gamma_D$ has positive boundary measure,
  Poincaré's inequality also gives
  $
    norm(v)_(L^2 (Omega)) <= c_P norm(grad v)_(L^2 (Omega)) wide forall v in V,
  $
  where $V$ is from @def:search-test-space and $c_P > 0$ does not depend on $v$. So on $V$ we can
  also use the gradient norm: it is equivalent to the full $H^1$ norm.
]<thm:l2-control>
#proof[
  The first bound follows directly from
  $
    norm(v)^2_(H^1 (Omega)) = norm(v)^2_(L^2 (Omega)) + norm(grad v)^2_(L^2 (Omega)).
  $
  The proof of Poincaré's inequality is omitted. Together with the first bound, it gives
  $
    norm(grad v)_(L^2 (Omega)) <= norm(v)_(H^1 (Omega))
    <= sqrt(1 + c_P^2) norm(grad v)_(L^2 (Omega)),
  $
  which is the equivalence of the two norms on $V$.
]

=== Lax-Milgram

#theorem(title: [Lax-Milgram lemma])[
  Consider a PDE $L u = f$, where $u : V -> RR$. Define $a$ and $F$ as in @eq:def-a.

  + $exists norm(dot) : V -> RR$ a norm, such that $forall v in V ==> norm(v) >= 0$ and
    $norm(v) = 0 <==> v = 0$.
  + $V$ is an Hilbert space: $exists (dot, dot): V times V -> RR$ inner product, such that
    $norm(v)^2 = (v, v)$.
  + $a$ is continuous/bounded, then $exists M > 0$ such that $abs(a(u, v)) <= M norm(v) norm(u)$,
    $forall v, u in V$.
  + $a$ is cohercive: $exists alpha > 0$ such that $a(v, v) >= alpha norm(v)^2$, $forall v in V$.
  + $F$ is linear and bounded/continuous: $exists k > 0$ such that $abs(F(v)) <= k norm(v)$,
    $forall v in V$.

  Under the above assumptions, there exists a solution $u$ to the weak problem.
]<thm:lax-milgram>
#proof[Very hard, skip.]

#corollary[
  $
    norm(u) <= k/alpha
  $
]
#proof[
  Let $v = u$. Then $a(u, u) = F(u)$. Since $a$ is cohercive and $F$ is bounded, we have
  $
    alpha norm(u)^2 <= a(u, u) = F(u) <= k norm(u) \
    ==> alpha norm(u) <= k
  $
  as desired.
]

=== Stability

As we know, to compute an approximate solution, we want to search for a candidate in a countable set
of functions, called $V_h$, where $h$ is the "grid size".

#let pg = $("G")$
$
  pg wide "Find" u_h in V_h "s.t." a(u_h, v_h) = F(v_h) quad forall v_h in V_h
$

This corollary is very important, since this means that the solution is *stable*.

#theorem(title: [Céa lemma ])[
  $
    a(u - u_h, v_h) = 0 wide forall v_h in V_h
  $
]
#proof[
  Consider #pw. Since $v$ can be chosen arbitrarily in $V$, let $v = v_h in V_h subset V$. Now
  subtract #pg from #pw.
  $
    a(u, v_h) - a(u_h, v_h) = F(v_h) - F(v_h) = 0
  $
  but $a(u, v_h) - a(u_h, v_h) = a(u - u_h, v_h)$, giving the result.
]

#remark(title: [Galurkin orthogonality])[
  If $a(dot, dot)$ is symmetric, then
  $
    u - u_h perp v_h wide forall v_h
  $
]

This means that, if $a$ is symmetric, then we know that $u_h$ is the projection of $u$ onto $V_h$,
i.e. the best possible result.

=== Convergence
#proposition(title: [Convergence])[
  If $a$ satisfies the assumptions of @thm:lax-milgram, there holds
  $
    lim_(h -> 0) norm(u - u_h) = 0
  $
  for a properly chosen $V_h$.
]
#proof[
  Lets start from a lemma.

  #lemma[
    $
      norm(u - u_h) <= M/alpha norm(u - w_h) wide forall w_h in V_h
    $
  ]

  #proof[
    Start from coercivity:
    $
      alpha norm(u - u_h)^2 & <= a(u - u_h, u - u_h) \
                            & = a(u - u_h, u - w_h + w_h - u_h) wide "for any" w_h in V_h \
                            & = a(u - u_h, u - w_h) + underbrace(
                                a(u - u_h, w_h - u_h),
                                = 0 "by G.O."
                              ) \
                            & = a(u - u_h, u - w_h) \
                            & <= M norm(u - u_h) norm(u - w_h)
    $
    where the last step is given by continuity of $a$. By simplifying the norm squared we get the
    result.
  ]

  The result of the lemma implies
  $
    norm(u - u_h) <= M/alpha inf_(w_h in V_h) norm(u - w_h)
  $

  By taking limits as $h -> 0$ we get
  $
    lim_(h -> 0) norm(u - u_h) <= M/alpha lim_(h -> 0) inf_(w_h in V_h) norm(u - w_h)
  $

  We now want to show that
  $
    lim_(h -> 0) inf_(w_h in V_h) norm(u - w_h) = 0
  $
  since this is equivalent to the desired result.

  To do so we go back to the choice of $V_h$: we want to chose is such that, as $h -> 0$,
  $V_h -> V$. This is called "saturation property".
]

=== Choosing $V_h$ <sec:choosing-vh>

Consider the set of piecewise polynomial functions:
$
  cal(X)_h^r = {v_h : Omega -> RR : v_h in C^0 (Omega) and evaluated(v_h)_(k_j) in PP^r quad forall j}
$
where $Omega = union.big_j k_j$ and $max_j abs(k_j) = h$.

Then a sensible choice for $V_h$ is
$
  V_h := {v_h in cal(X)_h^r : evaluated(v_h)_(Gamma_D) = 0}
$

When $r = 1$, a basis could be chosen simply by letting
$
  phi_j (x_i) = delta_(i j)
$

== Analysis of elliptic PDEs

=== Continuity of $a$

#proposition(title: [Continuity])[
  If $mu$, $va(b)$ and $sigma$ are bounded, then
  $
    abs(a(u, v)) <= M norm(u)_(H^1 (Omega)) norm(v)_(H^1 (Omega)),
  $
  with $M = norm(mu)_(L^infinity) + norm(va(b))_(L^infinity) + norm(sigma)_(L^infinity)$.
]
#proof[
  Bound the coefficients, then apply Cauchy-Schwarz to each integral:
  $
    abs(a(u, v)) & <= norm(mu)_(L^infinity) norm(grad u)_(L^2) norm(grad v)_(L^2)
                   + norm(va(b))_(L^infinity) norm(grad u)_(L^2) norm(v)_(L^2)
                   + norm(sigma)_(L^infinity) norm(u)_(L^2) norm(v)_(L^2).
  $
  Each $L^2$ norm on the right is bounded by the corresponding full $H^1$ norm. Factor these out to
  get the result.
]

=== Coercivity

#proposition(title: [Coercivity])[
  There exists $alpha > 0$ such that
  $
    a(v, v) >= alpha norm(v)^2_(H^1 (Omega)) wide forall v in V
  $
  for $a(u, v) = integral_Omega mu grad u dot.op grad v
  + integral_Omega (va(b) dot.op grad u) v
  + integral_Omega sigma u v$, under the positivity assumptions used below.
]

#proof[
  Start by substituting $u = v$.
  $
    a(v, v) & = integral_Omega mu grad v grad v
              + integral_Omega va(b) dot.op grad v dot.op v
              + integral_Omega sigma v^2 \
            & = integral_Omega mu (grad v)^2
              + integral_Omega va(b) dot.op grad v dot.op v
              + integral_Omega sigma v^2 \
            & = integral_Omega mu (grad v)^2
              + 1/2 integral_Omega va(b) dot.op grad (v^2)
              + integral_Omega sigma v^2 \
  $

  If $va(b) = 0$ we just get
  $
    & = integral_Omega mu (grad v)^2
      + integral_Omega sigma v^2 \
    & >= min mu norm(grad v)^2_(L^2) + min sigma norm(v)^2_(L^2) \
    & >= min(mu, sigma) (norm(grad v)_(L^2)^2 + norm(v)_(L^2)^2) \
    & = min(mu, sigma) norm(v)^2
  $
  where we assume that $mu > 0$ and $sigma > 0$.

  Otherwise, if $va(b) != 0$, we get
  $
    & integral_Omega mu (grad v)^2
      + 1/2 integral_Omega va(b) dot.op grad (v^2)
      + integral_Omega sigma v^2 \
    & = integral_Omega mu (grad v)^2
      - 1/2 integral_Omega div va(b) v^2
      + 1/2 integral_(partial Omega) va(b) dot.op va(n) v^2
      + integral_Omega sigma v^2 \
    & = integral_Omega mu (grad v)^2
      + integral_Omega underbrace((sigma -1/2 div va(b)), gamma >= 0) v^2
      + 1/2 integral_(partial Omega) va(b) dot.op va(n) v^2 \
    & >= min mu norm(grad v)^2_(L^2) + min gamma norm(v)^2_(L^2)
      + 1/2 integral_(partial Omega) underbrace(va(b) dot.op va(n), >= 0) v^2 \
    & >= min(mu, gamma) (norm(grad v)_(L^2)^2 + norm(v)_(L^2)^2) \
    & = min(mu, gamma) norm(v)^2
  $
  Here we assume uniform lower bounds $mu >= mu_0 > 0$ and $gamma >= gamma_0 > 0$, and
  $va(b) dot.op va(n) >= 0$ on $Gamma_N$; on $Gamma_D$, $v = 0$ already. Then
  $alpha = min(mu_0, gamma_0)$. In the case $va(b) = 0$, use a positive lower bound for $sigma$
  instead of $gamma$. If the reaction lower bound is only zero, we can still use Poincaré's
  inequality when the assumptions of @thm:l2-control hold.
]

#example[
  Now consider
  $
    L u = - div (mu grad u) + div (va(b) u) + sigma u
  $
  Check coercivity.
]
#solution[
  The only different part is the second term $div(va(b) u)$, so we just check
  $
    integral_Omega div(va(b) u) v &
    = - integral_Omega va(b) u grad v + integral_(partial Omega) va(b) dot.op va(n) u v \
    = - integral_Omega va(b) v grad v + integral_(partial Omega) va(b) dot.op va(n) v^2\
  $

  Put $u = v$ and use $v grad v = 1/2 grad(v^2)$. Integrating by parts once more gives
  $
    -1/2 integral_Omega va(b) dot.op grad(v^2)
    + integral_(partial Omega) va(b) dot.op va(n) v^2
    = 1/2 integral_Omega div(va(b)) v^2
    + 1/2 integral_(partial Omega) va(b) dot.op va(n) v^2.
  $
  So the full expression is
  $
    a(v, v) = integral_Omega mu abs(grad v)^2
    + integral_Omega (sigma + 1/2 div(va(b))) v^2
    + 1/2 integral_(partial Omega) va(b) dot.op va(n) v^2.
  $
  Compared to the previous operator, the sign of $1/2 div(va(b))$ has changed. Take
  $mu >= mu_0 > 0$, $sigma + 1/2 div(va(b)) >= gamma_0 > 0$, and $va(b) dot.op va(n) >= 0$ on
  $Gamma_N$. Then
  $
    a(v, v) >= min(mu_0, gamma_0) norm(v)^2_(H^1 (Omega)).
  $
  Again, if the reaction lower bound is zero, Poincaré's inequality can replace it.
]

=== Continuity of $F$
#proposition[
  There exists $K > 0$ such that
  $
    abs(F(v)) <= K norm(v)
  $
]
#proof[
  $
    abs(F(v)) & <= abs(integral_Omega f v)
                + abs(integral_(Gamma_N) psi v)
                + abs(a(R phi, v)) \
              & <= norm(f)_(L^2 (Omega)) norm(v)_(L^2 (Omega))
                + norm(psi)_(L^2 (Gamma_N)) norm(v)_(L^2 (Gamma_N))
                + M norm(R phi)_V norm(v)_V
  $

  #lemma(title: [Trace inequality])[
    If $v in H^1 (Omega)$
    $
      norm(v)_(L^2 (partial Omega)) <= c_1 norm(v)_V
    $
    for a constant $c_1$.

    Similarly, for a constant $c_2$
    $
      norm(R phi)_V <= c_2 norm(phi)_(H^(1/2) (Gamma))
    $
  ]
  #proof[
    Skip.
  ]


  $
    abs(F(v)) & <= norm(f)_(L^2 (Omega)) norm(v)_(L^2 (Omega))
                + c_1 norm(psi)_(L^2 (Gamma_N)) norm(v)_V
                + c_2 M norm(phi)_(H^(1/2)_(Gamma_D)) norm(v)_V \
              & <=^"Poincarre" c_P norm(f)_(L^2 (Omega)) norm(v)_(V)
                + c_1 norm(psi)_(L^2 (Gamma_N)) norm(v)_V
                + c_2 M norm(phi)_(H^(1/2)_(Gamma_D)) norm(v)_V \
              & <= (c_P norm(f)_(L^2 (Omega))
                  + c_1 norm(psi)_(L^2 (Gamma_N))
                  + c_2 M norm(phi)_(H^(1/2)_(Gamma_D)) ) norm(v)_V
  $
]

=== Convergence

#proposition(title: [Convergence estimate])[
  $
    norm(u - u_h)_(H^1 (Omega)) <= C M/phi h^r abs(u)_(H^(r + 1) (Omega)) wide "for" r = 1, 2, 3
  $
  and $h$ is the degree of the approximate polynomials.

  Different norms give different results
  $
    norm(u - u_h)_(L^2 (Omega)) <= tilde(C) M/phi h^r abs(u)_(H^(r + 1) (Omega)) wide "for" r = 1, 2, 3
  $
]

#proof[Skip.]

= Parabolic Equations

This is the same problem as before but here we consider that our solution depends on time.

$
  pdv(u, t) + L u = f wide x in Omega, 0 < t < T
$

The domain of this problem is a cylinder $Q_T = Omega times (0, T)$, and its boundary is
$Sigma_T = partial Omega times (0, T)$.

Usual boundaries conditions are
$
  cases(
    u = phi wide & "on" Gamma_D times (0, T),
    mu pdv(u, n) = psi wide & "on" Gamma_N times (0, T),
    u = u_0 wide & "in" Omega\, t = 0
  )
$
this is generally referred as an Initial-Boundary Value Problem (IBVP).

Let's start with zero boundary data, then see what changes when $psi$ and $phi$ are nonzero. We use
the same spatial bilinear form $a$ as in the elliptic case. For the derivations below, assume enough
regularity to integrate by parts.

We use the space $V$ from @def:search-test-space for the test functions and the unknown with zero
Dirichlet data.

#proposition(title: [Homogeneous boundary data])[
  If $phi = 0$ and $psi = 0$, the weak formulation is: find $u(t) in V$ such that
  $
    integral_Omega pdv(u, t) v dd(x) + a(u, v) = integral_Omega f(t) v dd(x)
    wide forall v in V,
  $
  with $u(0) = u_0$.
]
#proof[
  *Same as elliptic:* multiply by $v in V$ and integrate in space, now at each fixed $t$:
  $
    integral_Omega pdv(u, t) v dd(x) + integral_Omega L u v dd(x)
    = integral_Omega f(t) v dd(x).
  $
  *Same as elliptic:* integrate the spatial term by parts as in @sec:elliptic-weak-formulation. We
  get the same $a(u, v)$; the boundary terms vanish because $v = 0$ on $Gamma_D$ and $psi = 0$ on
  $Gamma_N$.

  *New:* the term $integral_Omega pdv(u, t) v dd(x)$ remains. We do not integrate by parts in time.
  The unknown is now $u(t) in V$, and we also need the initial condition $u(0) = u_0$.
]

#proposition(title: [Nonzero Neumann data])[
  If $phi = 0$ but $psi != 0$, the same formulation holds with right-hand side
  $
    F(t)(v) = integral_Omega f(t) v dd(x) + integral_(Gamma_N) psi(t) v dd(s).
  $
  The space $V$ and the initial condition do not change.
]
#proof[
  *Same as elliptic:* nonzero Neumann data give a boundary term when integrating by parts:
  $
    integral_Omega L u v dd(x) = a(u, v) - integral_(Gamma_N) psi(t) v dd(s).
  $
  Move the boundary integral to the right-hand side, exactly as before. There is no new boundary
  step here: $psi$ and $F$ can now depend on $t$.]

#proposition(title: [Nonzero Dirichlet data])[
  If also $phi != 0$, take a sufficiently regular lifting $w(t) = R phi(t)$ and write $u = z + w$.
  Then $z(t) in V$ satisfies
  $
    integral_Omega pdv(z, t) v dd(x) + a(z, v) = tilde(F)(t)(v) wide forall v in V,
  $
  where
  $
    tilde(F)(t)(v) = F(t)(v) - integral_Omega pdv(w, t) v dd(x) - a(w(t), v),
  $
  and $z(0) = u_0 - w(0)$.
]
#proof[
  *Same as elliptic:* choose a lifting with $w = phi$ on $Gamma_D$, so $z = u - w$ has zero
  Dirichlet data. Substitute $u = z + w$ and use the bilinearity of $a$:

  $
    integral_Omega (pdv(z, t) + pdv(w, t)) v dd(x) + a(z, v) + a(w, v) = F(t)(v).
  $
  *Same as elliptic:* move $a(w, v)$ to the right-hand side.

  *New:* the time derivative also splits, so we must move $integral_Omega pdv(w, t) v dd(x)$ to the
  right. This term vanishes if the lifting is independent of time. We must also transform the
  initial condition: $z(0) = u_0 - w(0)$.
]

From now on, call the unknown with zero Dirichlet data $u$ again, and include any lifting terms in
$F$. This way we can always work with the same weak formulation.

#remark[
  We can group $(x, t)$ together, but this does not turn the problem into an elliptic one: we
  differentiate once in $t$ and twice in $x$. We also need an initial condition, not just boundary
  conditions in space.
]

#theorem(title: [Parabolic well-posedness])[
  Under the continuity and coercivity assumptions on $a$ from @thm:lax-milgram, and with suitable
  initial data and forcing, the parabolic problem is well posed: a solution exists, is unique, and
  depends continuously on the data.
]
#proof[Skip. A different proof is needed: we cannot apply Lax-Milgram directly.]

Furthermore, we can relax coercivity to *weak coercivity*, which is still sufficient.

#definition(title: [Weak coercivity])[
  $
    exists alpha > 0 exists lambda > 0 "s.t." a(v, v) + lambda norm(v)^2_(L_2 (Omega))
    >= alpha norm(v)^2_V wide forall v in V
  $
]

#example(title: [Heat equation])[
  Consider the problem
  $
    pdv(u, t) + L u = f
  $
  with $L u = -mu laplace u$, constant $mu > 0$, and homogeneous Neumann boundary conditions:
  $
    cases(
      pdv(u, t) - mu laplace u = f wide & "in" Omega times (0, T),
      mu pdv(u, va(n)) = 0 wide & "on" partial Omega times (0, T),
      u(0, x) = u_0(x) wide & "in" Omega.
    )
  $
  Here $va(n)$ is the outward unit normal. No heat crosses the boundary: the body is insulated.

  Why do we need weak coercivity?
]
#solution[
  We do not fix $u$ on the boundary, so $V = H^1 (Omega)$. The Neumann condition is used when
  integrating by parts. Then
  $
    a(v, v) = mu norm(grad v)^2_(L^2 (Omega)) = mu abs(v)^2_(H^1 (Omega)).
  $
  This is a squared seminorm, not a squared norm: any nonzero constant has zero gradient, but a
  nonzero $H^1$ norm. So $a$ is not coercive on $V$.

  However, adding an $L^2$ term fixes this. For any $lambda > 0$,
  $
    a(v, v) + lambda norm(v)^2_(L^2 (Omega))
    >= min(mu, lambda) norm(v)^2_(H^1 (Omega)).
  $
  Its square root is a norm equivalent to the $H^1$ norm. This is weak coercivity. We are not
  changing the PDE, just checking an inequality for $a$.

  Diffusion smooths temperature differences, but a uniform temperature stays uniform when $f = 0$.
  This is not a uniqueness problem here, since the initial condition fixes that temperature.
]

== Approximate solution

As before, we discretize $V$ to $V_h$, we however do _not_ discretize $t$: this is called a
*semi-discretization*.

Since $V_h$ is a linear space, there exists a basis ${phi_i}^(N_h)_(i = 1)$. We can choose one as in
@sec:choosing-vh. This means that
$
  forall t, wide u_h (t, x) = sum^(N_h)_(j = 1) u_j (t) phi_j (x)
$
this gives us a decomposition of the solution where the basis depends on space, while the
coefficients depend only on time.

Now we plug this in $pw_h$ and choose $v_h = phi_i$ for all $i$.
$
  cases(
    display(
      integral_Omega sum_j pdv(u_j, t) phi_j phi_i (x) dd(x) + a(sum_j u_j (t) phi_j, phi_i) =
      F(phi_i)
    )
    wide forall i = 1\, ...\, N_h,
    u_h (t = 0) = u_(0 h)
  )
$
but $u_j$ does not depend on $x$, so we can pull it out of $a$:
$
  sum_j pdv(u_j, t) underbrace(integral_Omega phi_j phi_i (x) dd(x), m_(i, j))
  + sum_j u_j (t) underbrace(a(phi_j, phi_i), a_(i, j))
  = underbrace(F(phi_i), F_i)
$
giving
$
  M dv(va(u), t) + A va(u) = va(F)
$<eq:ell-ode>
where
$
  va(u) = va(u)(t) = vec(u_1 (t) = u_h (t, x_1), dots.v, u_(N_h) (t) = u_h (t, x_(N_h)))
$

We now want to solve @eq:ell-ode. This is, however just a *system of first order, linear, ordinary
differential equations*.

#remark[
  To solve this problem we need to use a numerical method, such as Euler's method (forwards or
  backwards), central derivative, or Runge-Kutta.

  Here the professor went on a side-quest explaining how these methods work (skip RK) and applied
  them to our problem.
]

These methods give us a way to approximate the derivative as a finite sum by discretizing $t$. We
get
$
  cases(
    M va(u)^(n + 1) = M va(u)^(n) + Delta t (va(F)^n - A va(u)^n) wide & ("FE"),
    (M + Delta t A) va(u)^(n) = M va(u)^(n-1) + Delta t va(F)^n wide & ("BE"),
    M va(u)^(n + 1) = M va(u)^(n-1) + 2 Delta t (va(F)^n - A va(u)^n) wide & ("CD"),
  )
$
Note that, assuming $M = I$, $("FE")$ and $("CD")$ are explicit, while $("BE")$ is implicit, i.e.
requires a linear solve per iteration. If $M != I$ we still need to invert $M$ or, more likely,
introduce a linear solver for that too.

$M$ is commonly called the *mass matrix* while $A$ is the *stiffness matrix*.

#remark(title: [Mass lumping])[
  This is a method to approximate $M$ as a diagonal matrix $tilde(M)$. The diagonal entries of
  $tilde(M)$ are obtained by summing the corresponding row.

  This turns $("FE")$ and $("CD")$ in true explicit methods, which require no solve step.
]

Another method we could use is Crank-Nicolson
$
  M (va(u)^(n + 1) - va(u)^n)/(Delta t) + 1/2 A (va(u)^n + va(u)^(n+1)) = 1/2 (va(F)^n + va(F)^(n+1))
$
this is second order and implicit, but only requires one step.

#figure(
  table(
    columns: (auto, auto, auto, auto),
    table.header([*Method*], [*\# Steps*], [*Impl/Expl*], [*Order*]),
    [FE], $1$, [Explicit], $1$,
    [BE], $1$, [Implicit], $1$,
    [CD], $2$, [Explicit], $2$,
    [CN], $1$, [Implicit], $2$,
  ),
  caption: [Some numerical methods to solve ODEs.],
)

We can also define generally a $theta$-method. We choose $theta in [0, 1]$ then
$
  M (va(u)^(n + 1) - va(u)^n)/(Delta t) + A (theta va(u)^n + (1 - theta)va(u)^(n+1))
  = theta va(F)^n + (1-theta) va(F)^(n+1)
$

We now need to see how to choose $Delta t$. In general, implicit methods are way more stable than
explicit ones, which therefore require a more adequate choice of $Delta t$.

#definition(title: [Stability])[
  Let $delta$ small. Then we say a solution is stable if there exists $C > 0$ such that
  $
    abs(u(t) - u_delta (t)) <= C abs(u_0 - (u_0 + delta)) = C delta wide forall t
  $
]

== Analysis

For the following energy estimates, assume homogeneous boundary data, so that
$F(t)(v) = integral_Omega f(t) v dd(x)$. Assume *coercivity* for simplicity, even if weak coercivity
would be enough.

#proposition(title: [Energy estimate and boundedness])[
  The semidiscrete solution satisfies
  $
    norm(u_h (t))^2_(L^2 (Omega)) + alpha integral_0^t norm(u_h (s))^2_V dd(s)
    <= norm(u_(0 h))^2_(L^2 (Omega)) + 1/alpha integral_0^t norm(f(s))^2_(L^2 (Omega)) dd(s).
  $
  In particular, if $f = 0$, then
  $
    norm(u_h (t))_(L^2 (Omega)) <= norm(u_(0 h))_(L^2 (Omega)) wide forall t in [0, T].
  $
  The general estimate bounds the solution by the initial data and forcing; the unforced case says
  that its $L^2$ norm cannot increase. The latter only requires $a(v, v) >= 0$, so it also applies
  to the homogeneous Neumann heat equation above.
]
#proof[
  Let $v_h = u_h (t)$ for all $t$.

  $
    integral_Omega pdv(u_h, t) u_h dd(x) + a(u_h, u_h) = F(u_h)
  $
  by coercivity we have
  $
    1/2 dv(, t) integral_Omega u^2_h (t) dd(x) + alpha norm(u_h (t))^2_V <= F(u_h) <=
    norm(f(t))_(L^2) norm(u_h (t))_(L^2)
  $
  now integrate over $t$, by the fundamental theorem of calculus we get
  $
    integral_Omega u^2_h (t) dd(x)
    + 2 alpha integral_0^t norm(u_h (s))^2_V dd(s)
    <= integral_Omega u^2_(0 h) dd(x)
    + 2 integral_0^t norm(f(s))_(L^2 (Omega)) norm(u_h (s))_(L^2 (Omega)) dd(s) \
    ==>
    norm(u_h (t))^2_(L^2 (Omega)) + 2 alpha integral_0^t norm(u_h (s))^2_V dd(s)
    <= norm(u_(0 h))^2_(L^2 (Omega))
    + 2 integral_0^t norm(f(s))_(L^2 (Omega)) norm(u_h (s))_(L^2 (Omega)) dd(s) \
  $

  First consider $f = 0$. The last term vanishes and the energy term on the left is nonnegative,
  giving the unforced boundedness statement. For general $f$, continue with Young's inequality.

  #lemma(title: [Young inequality])[
    $
      a b <= epsilon a^2 + 1/(4 epsilon) b^2 wide forall a, b in RR, epsilon > 0
    $
  ]
  #proof[
    Start by noting that
    $
      (sqrt(epsilon) a - 1/(2 sqrt(epsilon)) b)^2 >= 0
    $
    since it is a squared quantity.

    Then expand
    $
      epsilon a^2 + b^2 /(4 epsilon) - a b >= 0
    $
    and rearranging terms we get the result.
  ]

  Now we use this inequality on the last part of the above equation (the one dependent on $f$) to
  get
  $
    2 integral_0^t norm(f(s))_(L^2 (Omega)) norm(u_h (s))_(L^2 (Omega)) dd(s)
    & <= 2/(4 epsilon) integral^t_0 norm(f(s))^2_(L^2 (Omega)) dd(s)
    + 2 epsilon integral^t_0 norm(u_h (s))^2_(L^2 (Omega)) dd(s) \
    & <= 1/(2 epsilon) integral^t_0 norm(f(s))^2_(L^2 (Omega)) dd(s)
    + 2 epsilon integral^t_0 norm(u_h (s))^2_V dd(s) \
  $
  where we use $norm(v)_(L^2 (Omega)) <= norm(v)_V$ for the chosen full $H^1$ norm. This gives the
  same time-integrated $V$ norm as on the left, allowing us to absorb part of it.

  Now choose $epsilon = alpha/2$. This gets us
  $
    norm(u_h (t))^2_(L^2 (Omega)) + alpha integral_0^t norm(u_h (s))^2_V dd(s)
    <= norm(u_(0 h))^2_(L^2 (Omega)) + 1/alpha integral^t_0 norm(f(s))^2_(L^2 (Omega)) dd(s)
  $
  This is the result, as we are bounding the solution by the data.
]

#theorem(title: [Stability of linear problems])[

  TODO: see recording

  Consider a linear problem
  $
    cases(
      dv(y, t) = A y + b,
      evaluated(y)_(t = 0) = y_0
    )
  $
  and perturb it
  $
    cases(
      dv(z, t) = A z + b,
      evaluated(z)_(t = 0) = y_0 + delta
    )
  $

  For a constant matrix $A$, on any fixed interval $[0, T]$,
  $
    norm(z(t) - y(t)) <= exp(T norm(A)) norm(delta).
  $
  Here we use the Euclidean norm and its induced matrix norm. If the symmetric part $(A + A^T)/2$ is
  negative semidefinite, we get the stronger bound
  $
    norm(z(t) - y(t)) <= norm(delta) wide forall t >= 0.
  $
  So a general linear problem has bounded amplification on a finite interval; a dissipative one does
  not amplify the perturbation at all.
]

#proof[
  Subtract the systems and set $w = z - y$. The common forcing cancels:
  $
    dv(w, t) = A w, quad w(0) = delta.
  $
  Thus $w(t) = exp(t A) delta$. Using the matrix exponential series,
  $norm(exp(t A)) <= exp(t norm(A))$, giving the first bound.

  For the stronger bound, track the squared error instead:
  $
    1/2 dv(, t) norm(w)^2 = w dot.op A w <= 0.
  $
  Its norm cannot increase. The key assumption here is dissipativity, not just linearity.
]

#proposition(title: [Stability of parabolic])[
  Assume $a$ is coercive and use the full $H^1$ norm on $V$, as in the energy estimate above.
  Backward Euler satisfies, for every $Delta t > 0$,
  $
    norm(u_h^N)^2_(L^2) + alpha Delta t sum_(n=0)^(N-1) norm(u_h^(n+1))^2_V
    <= norm(u_(0 h))^2_(L^2) + (Delta t)/alpha sum_(n=0)^(N-1) norm(f^(n+1))^2_(L^2).
  $
  In particular, if $f = 0$, the $L^2$ norm cannot increase from one step to the next. The
  difference of two solutions with the same forcing also cannot grow:
  $
    norm(u_h^N - tilde(u)_h^N)_(L^2) <= norm(u_(0 h) - tilde(u)_(0 h))_(L^2).
  $
  There is no restriction on $Delta t$ for these stability bounds.
]
#proof[
  Start from backwards euler (i.e. $theta = 1$):
  $
    integral_Omega (u_h^(n + 1) - u_h^n)/(Delta t) v_h dd(x) + a (u^(n+1)_h, v_h)
    = integral_Omega f^(n + 1) v_h dd(x) wide forall v_h in V_h
  $
  Choose $v_h = u_h^(n + 1)$. This gives
  $
    integral_Omega (u_h^(n + 1) - u_h^n)/(Delta t) u_h^(n+1) dd(x) + a (u^(n+1)_h, u^(n+1)_h)
    = integral_Omega f^(n+1) u_h^(n+1)
  $
  We use coercivity and Cauchy-Schwarz: (TODO: what else?)
  $
    1/(2 Delta t) (norm(u_h^(n+1))^2_(L^2 (Omega)) - norm(u_h^n)^2_(L^2 (Omega)))
    + alpha norm(u_h^(n+1))^2_V <= norm(f^(n+1))_(L^2 (Omega)) norm(u_h^(n+1))_(L^2 (Omega))
  $
  Now use Young inequality on the rhs:
  $
    norm(f^(n+1))_(L^2 (Omega)) norm(u_h^(n+1))_(L^2 (Omega))
    & <= epsilon norm(u_h^(n+1))^2_(L^2 (Omega)) + 1/(4 epsilon) norm(f^(n+1))^2_(L^2 (Omega)) \
    & <= epsilon norm(u_h^(n+1))^2_V + 1/(4 epsilon) norm(f^(n+1))^2_(L^2 (Omega))
  $
  by choosing $epsilon = alpha/2$ we get
  $
    norm(u_h^(n+1))^2_(L^2 (Omega)) - norm(u_h^n)^2_(L^2 (Omega)) + alpha Delta t norm(u_h^(n+1))^2_V
    <= (Delta t)/alpha norm(f^(n + 1))^2_(L^2 (Omega))
  $

  We now sum over the $n$:
  $
    sum^m_(n = 0) (norm(u_h^(n+1))^2_(L^2 (Omega)) - norm(u_h^n)^2_(L^2 (Omega)))
    + alpha Delta t sum^m_(n = 0) norm(u_h^(n+1))^2_V \
    <= (Delta t)/alpha sum^m_(n = 0) norm(f^(n + 1))^2_(L^2 (Omega))
  $

  Now we notice that this is a telescopic sum:
  $
    norm(u_h^(m+1))^2_(L^2 (Omega)) + alpha Delta t sum^m_(n = 0) norm(u^(n + 1)_h)^2_V <=
    norm(u^0)^2_(L^2 (Omega)) + (Delta t)/alpha sum^m_(n = 0) norm(f^n)^2_(L^2 (Omega))
  $

  Which is exactly what we want.
]

#proposition(title: [Stability of the $theta$ method])[
]
#proof[
  We will only prove what happens when $f = 0$.

  Start from the general $theta$-method formula
  $
    integral_Omega (u_h^(n+1) - u_h^n)/(Delta t) v_h dd(x) +
    a(theta u_h^(n+1) + (1 + Omega) u^n_h, v_h) = 0 wide forall v_h in V_h
  $

  #definition(title: [Eigenfunctions])[
    Let $a$ be a bilinear form. We say that $w$ is an eigenfunction of $a$ with eigenvalue $lambda$
    is
    $
      a(w, v) = lambda integral_Omega w v dd(x) wide forall v in V
    $
  ]

  #lemma[
    If $a$ is a symmetric and cohercive bilinear form of a finite space, then its eigenfunctions are
    $w_h in V_h$. Eigenfunctions form an orthonormal basis of $V_h$.
  ]

  We can decompose
  $
    u_h^n (x) = sum_(j = 1)^(N_h) u_j^n w_h^j (x)
  $

  Then, we take $v_h = w_h^i$
  $
    1/(Delta t) integral_Omega sum_(j = 1)^(N_h) (u_j^(n+1) - u_j^n) w_h^j w_h^i dd(x) \
    + a(theta sum_(j = 1)^(N_h) u_j^(n + 1) w_h^j + (1- theta) sum_(j = 1)^(N_h) u_j^n w_h^j, w^i_h) = 0
  $

  $
    1/(Delta t) sum_(j = 1)^(N_h) (u_j^(n+1) - u_j^n) integral_Omega w_h^j w_h^i dd(x) \
    + sum_(j = 1)^(N_h) (theta u_j^(n + 1) + (1- theta) u_j^n ) a(w_h^j, w^i_h) = 0
  $

  $
    1/(Delta t) sum_(j = 1)^(N_h) (u_j^(n+1) - u_j^n) delta_(i j)
    + sum_(j = 1)^(N_h) (theta u_j^(n + 1) + (1- theta) u_j^n ) lambda^j_h delta_(i j) = 0
  $

  Giving, for each $i = 1, ..., N_h$:
  $
    1/(Delta t) (u_i^(n+1) - u_i^n) + (theta u_i^(n + 1) + (1 - theta) u_i^n ) lambda^i_h = 0
  $
  and by rearranging we get
  $
    u_i^(n+1) = underbrace(
      [(1 - Delta t lambda_h^i (1-theta))/(1 + Delta t lambda_h^i
        theta)], P_i(Delta t, theta)
    ) u_i^n
  $
  Assuming $P_i(Delta t, theta) < 1$ for all $i$, we get that
  $
    sum_(i = 1)^(N_h) abs(u_i^(n+1))^2 <= sum_(i = 1)^(N_h) abs(u_i^n)^2
  $

  #remark[
    $
      norm(u_h^n)^2_(L^2 (Omega)) = (sum_())
    $

    TODO: complete here by decomposing using the eigenfunctions
  ]

  Using the remark above we obtain that
  $
    norm(u_h^(n+1))_(L^2)^2 < norm(u_h^n)_(L^2)^2
  $
  which in turns is
  $
    norm(u_h^n)_(L^2)^2 < norm(u^0)_(L^2)^2
  $

  #lemma(title: [Condition for stability])[
    $abs(P_i) < 1$ is always true when $theta in [1/2, 1]$.

    If $theta in [0, 1/2)$, we need
    $
      Delta t < 2/(lambda_h^i (1 - 2 theta))
    $
  ]
  #proof[
    The statement we want to prove is identical to
    $
      -1 - Delta t lambda^i_h theta < 1 - Delta t lambda_h^i (1-theta)
    $
    For all $Delta t > 0$ we can
    $
      -1 - Delta t lambda^i_h theta <
      1 - Delta t lambda_h^i (1-theta) < 1 + Delta t lambda_h^i theta
    $
    then, rearranging
    $
      Delta t [- theta lambda_h^i + lambda_h^i (1 - theta)] < 2
    $
    or equivalently
    $
      Delta t lambda_h^i (1 - 2 theta) < 2
    $

    Since $lambda_h^i$ is positive, the only way this inequality is false is if the content of the
    parenthesis is also positive. If $1 - 2 theta < 0$ this is always verified.
  ]

  When the above condition applies, we have the result.
]


#proposition(title: [Convergence])[
  $
    abs(u(t^n, x_j) - u^n_h (x_j)) -->^(Delta t -> 0, h -> 0) 0
  $
  where $t^n = n Delta t$.

  Moreover, for some constant $C(u) > 0$
  $
    norm(u(t^n) - u^n_h)_(H^1 (Omega)) <= C (Delta t^P + h^r)
  $
  where $r$ is the order of finite elements, while $P$ is the order of the time discretization
  method.
]

#proof[
  TODO
]

= Navier-Stokes Equations

This equation governs incompressible viscous fluids.

$
  cases(
    display(pdv(va(u), t) - nu laplace va(u) + (va(u) dot grad) va(u) + grad p = va(f)) wide
    & x in Omega \, 0<t<T,
    div va(u) = 0 wide & x in Omega\, 0<t< T
  )
$

We are considering the viscosity $nu >= 0$ constant and both the velocity $va(u)$ and the pressure
$p$ are unknowns.

Initial and boundary conditions are
$
  cases(
    va(u) = va(psi) wide & "on" Gamma_D,
    display(v pdv(va(u), va(n)) - p va(n) = va(psi)) wide & "on" Gamma_N,
    va(u) = u^0
  )
$

Note that this is a non-linear equation: the fluid is propelled by its own velocity.

Some common simplifications are:
- At steady state we set the time derivative to zero.
- If the velocity is small we can drop the quadratic term and linearize the equation, getting us the
  Stokes version.
- Do both at the same time.

== Weak formulation

=== Static Stokes

Let $V$ be the velocity space and $Q$ be the pressure space.

$
  cases(
    display(integral_Omega - nu laplace u v dd(x) + integral_Omega grad p v dd(x) = f v) wide & forall v in V,
    display(integral_Omega div u q dd(x) = 0) wide & forall q in Q
  )
$
using Green formula
$
  cases(
    display(
      nu integral_Omega - grad u grad v dd(x) - integral_(partial Omega) nu pdv(u, n) v dd(x)
      + integral_Omega grad p v dd(x) = f v
    ) wide & forall v in V,
    display(integral_Omega div u q dd(x) = 0) wide & forall q in Q
  )
$
and substituting the boundary conditions

TODO: something missing here
$
  cases(
    display(
      nu integral_Omega - grad u grad v dd(x)
      - integral_(Gamma_D) nu pdv(u, n) v dd(x)
      - integral_(Gamma_N) psi v dd(x)
      + integral_Omega grad p v dd(x) = f v
    ) wide & forall v in V,
    display(integral_Omega div u q dd(x) = 0) wide & forall q in Q
  )
$
and take $v = 0$ on $Gamma_D$

This gives us
$
  cases(
    V = {v in {H^1 (Omega)}^d : evaluated(v)_(Gamma_D) = 0},
    Q = display(
      cases(
        L^2 (Omega) wide & "if" Gamma_N != varnothing,
        display(
          L^2_0 (Omega) = {q in L^2 (Omega) : integral_Omega q dd(x) = 0} wide &
          "if" Gamma_D = partial Omega
        )
      )
    )
  )
$
