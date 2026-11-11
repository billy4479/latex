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

== Finding the Weak Problem

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
$

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

This means we define our search space $V$ as
$
  V = H^1_(Gamma_D) = cases()
$

TODO

== Analysis of Weak Problem

Assumptions:
+ $exists norm(dot) : V -> RR$ a norm, such that $forall v in V ==> norm(v) >= 0$ and
  $norm(v) = 0 <==> v = 0$.
+ $V$ is an Hilbert space: $exists (dot, dot): V times V -> RR$ inner product, such that
  $norm(v)^2 = (v, v)$.
+ $a$ is continuous/bounded, then $exists M > 0$ such that $abs(a(u, v)) <= M norm(v) norm(u)$,
  $forall v, u in V$.
+ $a$ is cohercive: $exists alpha > 0$ such that $a(v, v) >= alpha norm(v)^2$, $forall v in V$.
+ $F$ is linear and bounded/continuous: $exists k > 0$ such that $abs(F(v)) <= k norm(v)$,
  $forall v in V$.

#theorem(title: [Lax-Milgram lemma])[
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

This corollary is very important, since this means that the solution is *stable*.

#theorem(title: [Céa lemma (Galurkin orthogonality)])[
  $
    a(u - u_h, v_h) = 0 wide forall v_h in V_h
  $
]
#proof[
  $v = v_h$, then $("PW") without ("G")$.
  $
    a(u, v_h) - a(u_h, v_h) = F(u_h) - F(u_h) = 0
  $
  but $a(u, v_h) - a(u_h, v_h) = a(u - u_h, v_k)$, giving the result.
]
