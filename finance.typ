#import "lib/template.typ": template
#import "lib/theorem.typ": *

#show: template.with(
  title: "Mathematical Modelling for Finance",
  author: "Giacomo Ellero",
  date: "A.Y. 2025/2026",
)
#show: great-theorems-init

= One-period models

In this kind of models we have that $t in {0, 1}$.
We consider $N$ securities $S_j$ and $B$ being the risk free asset
which always costs $1$ and always returns $1 + r$, where $r$ is the safe rate;
meanwhile, for each $j in {1, ..., N}$ will have current cost $S_j (0)$ and a future revenue which
is given by a random variable $S_j (1)(omega_k)$ where each $omega$ comes from a _finite_ set
$Omega$ of all possible events.

With this in mind we can arrange costs and revenues in a vector
$
  S(0) = vec(S_1 (0), dots.v, S_N (0)) wide
  S(1)(omega_k) = vec(S_1 (1)(omega_k), dots.v, S_N (1)(omega_k))
$
and subsequently in a so called _cashflow matrix_
$
  cal(M) = mat(
    -1, -S_1 (0), ..., -S_N (0);
    1+r, S_1 (1)(omega_1), ..., S_N (1)(omega_1);
    dots.v, dots.v, dots.down, dots.v;
    1+r, S_1 (1)(omega_k), ..., S_N(1)(omega_k)
  )
$
where each row represents the cost of selling said security and the first column represents $B$,
which is safe by definition and therefore its revenue is not influenced by $omega$.
We can also define the _payoff matrix_ $cal(A)$ by removing the first row of $cal(M)$.

Then, we introduce the $N+1$ dimensional vector $theta$, which counts how many of each security we
are buying, with $theta_0$ representing the amount of $B$ we are buying.
Note that
$
  theta_j > 0 & ==> "we are buying asset" j \
  theta_j < 0 & ==> "we are selling asset" j
$

Now we can define a value function defining how much money goes in or out of our pocket at a certain
time.
$
  V_theta (0) = S(0) dot theta \
  V_theta (1)(omega_k) = S(1)(omega_k) dot theta = A theta
$
Moreover
$
  M theta = vec(-V_theta (0), V_theta (1))
$

#example[
  Let $theta_1 = 1$ and $theta_0 = -S_1(0)$: this means we are buying one item of security $1$ and
  "selling" enough of $B$ to be able to buy $S_1$ without using any of our money
  (since $V_theta (0) = 0$).
  Since we have nothing at $t = 0$ we are essentially *borrowing* at the safe rate to buy $S_1$ and
  at $t=1$ we will have to buy back our debt.
]

== Law of one price
This is a weak requirement to make sure that markets work as intended.
We start with some definitions.

#definition(title: "Spaces of payoffs and cashflows")[
  Let the *space of traded payoffs* be
  $
    A = {z in RR^k | z = A theta, theta in RR^(k+1)}
  $
  and the *space of traded cashflows* be
  $
    M = {x in RR^(k+1) | x = M theta, theta in RR^(k+1)}
  $
]

#definition(title: "Law of one price (LOP)")[
  Given $theta', theta'' in RR^(N+1)$ such that $A theta' = A theta''$, then
  $V_(theta ') (0) = V_(theta'')(0)$.
]
This basically means that to get the same amount of the same revenue we have to pay the same amount
of money.

If in a real market we notice that there exists a violation of this rule (i.e. there exists $theta'$
and $theta''$ such that $A theta' = A theta''$ but $V_(theta') != V_(theta'')$) we can short the
most expensive strategy and buy the better one so that we immediately generate cash, then at time
$t=1$ we close all of our positions but by definition we will get the same payoff on both
strategies.

#remark[
  If $"rank"(A) = k$ then LOP holds. This makes sure that there are no redundant securities whose
  payoff can be obtained by a linear combination of the others.
  $
    A(theta' - theta'') = 0
  $
]

#proposition[
  LOP holds iff
  $
    A theta = 0 ==> V_theta (0)
  $
]

These tell us that if we want to get a zero payoff it will cost us zero.

#definition(title: "Linear Pricing Functional (LPF)")[
  $
    pi (z) = { V_theta (0) | A theta = z}
  $
  such that
  1. $pi(z)$ is single-valued (i.e. is a function)
  2. $pi(z)$ is linear
]

#proposition[
  LOP holds $<==> exists$ an LPF.
]

#definition(title: "Stochastic Discount Factor (SDF)")[
  The SDF is a random vector $m$ such that
  $
    S_j (0) & = EE[m S_j (0)] wide forall j in {1, ..., N} \
       B(0) & = EE[m B(1)]
  $
]
The SDF represents how the cost of a security today is influenced by its expected value tomorrow.

However, since $B(1)$ is constant and equal to $1+r$ we can write
$
  1 = (1+r) EE(m) ==> EE[m] = 1/(1+r)
$

#remark[
  1. $m$ is an SDF iff
    $
      V_theta (0) = EE [m V_theta (1)] wide forall theta in RR^(N+1)
    $
  2. $exists m ==> exists "LPF"$
]
#proof[
  We prove 2.: we define
  $
    pi(z) & = EE[m z]          & wide & z in A \
          & = E[m A theta]     & wide & "for some" theta \
          & = E[m V_theta (1)] \
          & = V_theta (0)
  $
  which is our LPF since the expectation is linear and
]

#theorem(title: "Equivalent characterizations of LOP")[
  The following states are equivalent:
  1. LOP holds;
  2. $exists$ an LPF $pi$;
  3. $exists$ an SDF $m$;
]

#proof[
  / 1. $==>$ 3.: Consider $A$ and define an inner product on it as
    $angle.l z', z'' angle.r = EE[z' z'']$, so that we have an Hilbert space.
    We want to show that $pi(z) = E[m z]$.
    Define $A_0 = { z in A | pi(z) = 0}$ (i.e. the kernel of $A$) and
    $A_0^perp = {y in A | EE[y z] = 0 "for all" z in A_0}$ (being the orthogonal space to the
    kernel).
    Then we can decompose $A = A_0 plus.circle A_0^perp$.

    Take any $y in A_0^perp$ such that $y != 0$, which in turns implies that $pi(y) = 0$.
    Set $w = y/(pi(y))$ so that $pi(w) = 1$.
    Then, take any $z in A without A_0$ and write it as
    $
      z = pi(z) w + underbrace((z - pi(z) w), pi(dot) = 0 ==> in A_0)
    $
    now we multiply by $w$ and take the expectation
    $
      EE[w z] = pi(z) EE(w^2) + cancel(EE[w (z pi(z) w)])
    $
    and we can cancel the second term since $w in A_0^perp$ and $z pi(z) w in A_0$, then
    $
      pi(z) = EE[ w/(EE[w^2]) z]
    $
    and we define $m$ as $w/(EE[w^2])$.
]
