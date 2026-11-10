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

#let ub(it) = $upright(bold(it))$
#let vv(it) = math.bold(it)

= AAA

Consider the original problem
$
  cases(
    L u = f wide & "in" Omega subset RR^d,
    "Boundaries conditions" wide & "on" partial Omega
  )
$

Then the *weak problem* is
$
  "Find" u in V "s.t." a(u, v) = F(v) wide forall v in V
$
where
- $a : V times V -> RR$ is a bilinear form
- $F: V -> RR$ is a linear functional

#example(title: [ADR])[
  The original problem is
  $
    cases(
      L u = - dd(w) (mu grad u) + vec(b) dot.op grad u + sigma u = f wide & "in" Omega,
      u = phi wide & "on" Gamma_D,
      mu pdv(u, n) = psi wide & "on" Gamma_N
    )
  $
  where the data is
  $
    {mu, vec(b), sigma, f, phi, psi, Omega, Gamma_D, Gamma_F}
  $
  and the solution is $u$.
]

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
]
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
