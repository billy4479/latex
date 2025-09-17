#import "lib/template.typ": template
#import "lib/theorem.typ": *
#show: template.with(
  title: "Mathematical Modelling for Finance",
  author: "Giacomo Ellero",
  date: "A.Y. 2025/2026",
)

#show: great-theorems-init

= Introduction
Stochastic processes are mathematical tools to model uncertainty and randomness.
We will discuss two types of applications: modelling of stochastic phenomena and computational
algorithms which need a probabilistic approach.

== Formal definition

More in particular, stochastic processes are probabilistic models for random quantities which
_evolve over time_. Formally a stochastic process is a collection of random variables:
$
  {X_t | t in T} quad "or (in short)" (X_t)_(t in T)
$
where $T$ is the index set, and
$
  X_t : Omega -> cal(X)
$

The index space $T$ usually is one of $[0, + infinity]$ (_continuous time_) or ${1,2,...}$
(_discrete time_).
Meanwhile $cal(X)$ can be either uncountable (e.g. $RR^d$, giving _continuous space_) or finite or
countable which gives a _discrete space_.

As an example we can consider $cal(X) = \R$, $T = [0, +infinity]$ and each realization $X_t$ is a
possible trajectory in the plane $cal(X)$-$T$. This means that each $X_t$ is a function from $T$ to
$cal(X)$.

#example(title: "Gambler's ruin")[
  A gambler plays a game where he wins $1$ with probability $p$ and loses with probability $1-p$.

  He starts with $x_0$ money and stops when he reaches $0$ or a prefixed $N$.
] <ex:gamblers-ruin>

#model[
  We denote $(X_t)_(t in T)$ the stochastic process with $cal(X) = {0, 1, ..., N}$ and
  $T = {0, 1, ...} = NN$.
  Each $X_t$ is the "trajectory" that the money that the gambler owns takes.
]

= Discrete-time Markov chains

This is a way to model discrete-time stochastic processes with $n$ random variables.
First we need to specify the law (i.e. the joint distribution)
$
  cal(L) (X_0, ..., X_n)
$

However, when $n$ is very large it is convenient to decompose it using conditional distributions:
#lemma(title: "Sequential decomposition")[
  Given a random vector $(X_0, ..., X_n)$ on $cal(X)^(n+1)$ we have
  $
    cal(P)(X_0, ..., X_n) = cal(P)(X_0 = x_0) product^(n-1)_(i = 0) cal(P)(X_(i+1) = x_(i+1) |
      X_i = x_i, ..., X_0 = x_0)
  $
]

#proof[
  Follows from the definition of conditional probability: we get a telescopic product.
]

#corollary(title: "Simulating stochastic processes")[
  To simulate $(x_0, ..., x_n) tilde cal(L)(X_0, ..., X_n)$ we can
  - $X_0 tilde cal(L)(X_0) -> x_0$
  - $X_1 tilde cal(L)(X_1 | X_0 = x_0) -> x_1$
  - ...and so on
]

However this is usually too complex, since the number of random variables we depend on keeps
increasing.

#definition(title: "Markov chain")[
  A discrete-time stochastic process is a Markov chain if
  $
    cal(P)(X_(t+1) = x_(t+1) | X_t = x_t, ..., X_0 = x_0) = cal(P)(X_(t+1) = x_(t+1) | X_t = x_t)
  $
  for all $t in NN$ and $forall (X_0, ..., X_(t+1)) in cal(X)^(t+1)$.
]

The intuition is that what happened in the system in the past no longer influences the next state,
we just need a snapshot of the current state of the system to be able to make predictions about the
next state.

This basically means that $X_(t+1) perp (X_0, ... , X_(t-1)) | X_t$, i.e. $X_(t+1)$ is independent
from all previous states once we know $X_t$.

Going back to @ex:gamblers-ruin we see that it can be modelled using a Markov chain, since the
probability of the gambler's money at the next state $t + 1$ to be $x_(t+1)$ is
$
  cases(
    p & " if" x_{t+1} = x_t + 1,
    1-p & " if" x_{t+1} = x_t - 1,
    0 & " otherwise",
  )
$

=== Chapman-Kolmogorov equations

We define the *transitional probability* $P_(i j)$, which is the probability of going to state $j$
from state $i$:
$
  P_(i j) = cal(P)(X_(t+1) = j | X_t = i) wide i, j in cal(X)
$
Note tat we can construct a *transition matrix* $P$ of all the combinations of transitional
probabilities in $cal(X)$.

A common problem is to compute the probability that a certain event $j$ occurs after $n$ steps:
$
  P^n_(i j) = cal(P)(X_(t+n) = j | X_t = i)
$

#proposition(title: "Chapman-Kolmogorov equations")[
  The $n$-step transition probability satisfy
  $
    P^(n+m)_(i j) = sum_(k in cal(X)) P_(i k)^n P_(k j)^m wide i, j in cal(X); n, m >= 0
  $
]<prop:chapman-kolmogorov>
#proof[
  We have
  $
    P_(i j)^(n + m) & = cal(P)(X_(n+m) = j | X_0 = i) \
    & = sum_(k in cal(X)) cal(P)(X_(n+m) | X_n = k, X_0 = i) cal(P)(X_n = k | X_0 = i) \
    & = sum_(k in cal(X)) cal(P)(X_(n+m) = j | X_n = k) cal(P)(X_n = k | X_0 = i) \
    & = sum_(k in cal(X)) P_(i k)^n P_(k j)^m
  $
  by conditioning on $X_n$ and applying Markov property.
]

#corollary()[
  The $n$ steps transitional matrix $P^n$ coincides with
  $
    P^n = product^n_(i = 1) P
  $
  as in normal matrix exponentiation.
]

=== Marginals

Define
$
  alpha_i^((t)) = cal(P)(X_t = i)
$
then, if we know the distribution of $X_0$, i.e. the value of $alpha_i^((0))$ for all $i in cal(X)$
we can compute the marginals at any step as
$
  alpha^((t)) = alpha^((0)) P^t
$
where we are interpreting $alpha^((t))$ and $alpha^((0))$ as row vectors with one entry for each
$i in cal(X)$.

== Classification of states and recurrence

We start to explore the long-run behavior of a Markov chain.

- A state $j$ is *accessible* from $i$ if $P^t_(i j) > 0$ for some $t in T$
- Two states $i$, $j$ *communicate* if $i$ is accessible from $j$ and $j$ is accessible from $i$

#lemma()[
  Communication between two states is an equivalence relation, therefore we can divide $cal(X)$ in
  equivalence classes.
]

If all states communicate with each other we say that the Markov chain is *irreducible*.

An equivalence class $C$ is *closed* if the chain cannot escape from $C$, i.e.
$
  i in C ==> j in C quad forall j "accessible from" i
$

Define the probability of from state $i$ to return to state $i$ as
$
  f_i & = cal(P)(X_t = i "for some" t>=1 | X_0 = i) \
      & = cal(P)(union.big_(t >= 1) {X_t = i} | X_0 = i)
$<eq:def-fi>
A state $i in cal(X)$ is *recurrent* if $f_i = 1$ and *transient* if $f_i < 1$.

In @ex:gamblers-ruin we have that state $0$ and state $N$ are recurrent, while all the others
are transient.

We also define
$
  S_k = "time of the" k"-th return to" i "of" (X_t)_(t >= 0) wide k>=0
$
and we set $S_k = infinity$ if $(X_t)_(t >= 0)$ returns to $i$ less than $k$ times.
Formally, we define $S$ recursively: $S_0 = 1$ and
$
  S_k = min {t >= S_(k-1) + 1 | X_t = i }
$
and we set $min nothing.rev = infinity$.
We also define the length of the $k$-th tour as
$
  T_k = S_k - S_(k-1)
$

#lemma()[
  Let $k >= 1$. Conditional on $S_(k-1) < infinity$, the random variable $T_k$ is independent of
  $(X_0, ..., X_(S_(k-1)))$ and it is equal in distribution to $T_1$.
]<lemma:t-indep>
#proof[ Skip. Intuitively it's because of the time-homogeneity of Markov chains.]

This means that basically $T_1$ are iid random variables.

Let $V_i$ denote the number of visits to $i$:
$
  V_i = sum_(t=0)^infinity bb(1)(X_t = i)
$
so that $V_i$ is a random variable with values in $NN union {oo}$.

#proposition()[
  For each $i in cal(X)$, we have
  $
    cal(P)(V_i > r | X_0 = i) = f_i^r wide r >= 0
  $
  where $f_i$ is defined as @eq:def-fi.
]<prop:prob-vi>
#proof[
  Follows by induction from @lemma:t-indep.
]

This means that $V_i = oo$ almost surely if $i$ is recurrent and $V_i tilde "Geom"(1-f_i)$ if $i$ is
transient (recall the
#link("https://en.wikipedia.org/wiki/Geometric_distribution")[geometric distribution]).

#proposition[
  A state $i$ is recurrent if and only if
  $
    sum^oo_(t=0) P^t_(i i) = oo
  $
  and transient if and only if
  $
    sum^oo_(t=0) P^t_(i i) < oo
  $
]<prop:sum-pt-recurrent>
#proof[
  We have that
  $
    EE[V_i | X_0 = i] = sum_(t=0)^oo EE[bb(1)(X_t = i) | X_0 = i] = sum_(t=0)^oo P^t_(i i)
  $
  where we have used the definition of $V_i$ and the definition of expectation.
  Then $EE[V_i | X_0 = i] = oo$ if and only if $i$ is recurrent, by @prop:prob-vi.
]

#proposition[
  If $i$ and $j$ communicate either they are both transient or both recurrent.
]
#proof[
  Assume $i$ is recurrent. By @prop:sum-pt-recurrent we have that $sum^oo_(t=0) P^t_(i i) = oo$.
  Now, since $i$ and $j$ communicate, there exists some $ell, r > 0$ such that $P^ell_(i j) > 0$ and
  $P^r_(i j)$. Thus
  $
    P_(j j)^(ell + t + r) >= P_(j i)^ell P^t_(i i) P^r_(i j) wide t >= 0
  $
  and
  $
    sum_(n = 0)^oo P^n_(j j) >= sum_(t = 0)^oo P_(j j)^(ell + t + r)
    >= P_(j i)^ell P^r_(i j) sum_(n = 0)^oo P^t_(i i) = oo
  $
  meaning that $j$ is also recurrent.
]

#corollary[
  If a Markov chain is irreducible, then either all states are transient or all recurrent. In these
  cases we say that the whole chain is transient or recursive.
]

#corollary[
  If the set of outcomes $cal(X)$ is finite, then some state must be recurrent, thus all states in a
  finite irreducible chain are recurrent.
]

== Random walks in $d$ dimension

In this case $abs(cal(X)) = +oo$, therefore it is not clear whether states are transient or
recurrent.

#example(title: [Random walk on $ZZ$])[
  Consider a drunken man walking a long a straight line. Assume that all steps are of size $1$ and
  that the man goes right with probability $1-p$ independently of the previous steps.
]

#model[
  The location of the man $X_t$ after $t$ steps is a Markov chain with state space $cal(X) = ZZ$ and
  transitional probabilities
  $
    P_(i j) = cases(
      p & wide text("if") j = i + 1,
      1-p & wide text("if") j = i - 1,
      0 & wide text("otherwise")
    )
  $
  In this case all states communicate with each other, so there is just one class, thus either all
  states are transient or all states are recurrent.
]

#theorem[
  The random walk on $ZZ$ is recurrent if $p = 1/2$ and transient otherwise.
]

#proof[
  By @prop:sum-pt-recurrent we can look at $sum_(n = 0)^oo P^n_(i i)$ to determine if the chain is
  transient or recurrent.
  Without loss of generality, we can assume that $i = 0$ (since there is only one equivalence
  class).

  Note that $P_(0 0)^n = 0$ if $n$ is odd by the definition of the random walk, then
  $sum_(n = 0)^oo P^n_(0 0) = sum_(n = 0)^oo P^(2n)_(00)$.

  For every $n in NN$ we have
  $
    P^(2n)_(00) & = cal(P)(X_(2n) | X_0 = 0) \
                & = cal(P)(Z_(2n) = n) wide "with" Z_(2n) tilde "Bin"(2n, p) \
                & = binom(2n, n) p^n q^n \
                & = ((2n)!)/(n! n!) p^n q^n
  $
  where $q = 1-p$.

  We give the following two lemmas from analysis 1 without proof, where
  the symbol #sym.asymp denotes "is asymptotic to", i.e. if $a_n asymp b_n$ as $n -> oo$ then
  $lim_(n -> oo) a_n / b_n = 1$.

  #lemma[
    Consider two sequences $a_n$ and $b_n$ with values in $[0, oo)$. If $a_n asymp b_n$ as
    $n -> oo$ then $sum_(n = 0)^oo a_n = +oo <==> sum_(n = 0)^oo b_n = +oo$
  ]

  #lemma(title: "Stirling")[
    $
      n! asymp sqrt(2 pi n) (n/e)^n
    $
  ]

  Using the second lemma we obtain
  $
    P^(2n)_(00) & asymp (sqrt(2 pi 2 n))/(sqrt(2 pi n))^n (((2n)/e)^(2n))/((n/e)^(2n)) p^n q^n & wide "as" n -> oo \
    & = 1/sqrt(pi) n^(-1/2) 2^(2n) p^n q^n \
    & = 1/sqrt(pi) n^(-1/2) rho^n & wide "where" rho = 4 p q
  $
  and, by the first lemma, the asymptotic behavior of this series is the same of $P^n_00$.

  - If $p == 1/2$ then $rho = 1$ and
    $
      sum^oo_(n = 1) rho^n n^(-1/2) = sum^oo_(n = 1) n^(-1/2) = + oo
    $
    and the random walk is recurrent.
  - If $p != 1/2$ then $rho = 4p(1-p) < 1$ and
    $
      sum^oo_(n = 1) rho^n n^(-1/2) < sum^oo_(n = 1) rho^n = 1/(1-rho) < + oo
    $
    and the random walk is transient.
]

#example(title: [Symmetric random walk on $ZZ^d$])[
  A random walk on $ZZ^d$ is a Markov chain with state space $cal(X) = ZZ^d$ and transitional
  probabilities
  $
    P_(i j) = cases(
      1/(2d) & wide "if" norm(i - j) = 1,
      0 & wide "otherwise"
    )
  $
]

#theorem(title: [Random walk on $ZZ^d$])[
  The symmetric random walk on $ZZ^d$ is recurrent if $d <= 2$ and transient if $d >= 3$.
]

== Convergence to stationarity

=== Stationary distributions

Sometimes a Markov chain converges to stationarity: this means that, regardless of the starting
point $k$, the distribution of $X_t$ converges to a fixed distribution $pi$.
$
  cal(P) (X_t = j | X_0 = k) = P^t_(k j) -> pi_j wide "as" t -> +oo, med forall k, j in cal(X)
$<eq:limiting-distrib>
If this holds we say that $pi$ is the *limiting distribution* of the Markov chain and
$(pi_i)_(i in cal(X))$ are the limiting probabilities.

If @eq:limiting-distrib holds, then, by @prop:chapman-kolmogorov we have
$
  pi_j & = lim_(t -> oo) P_(k j)^t = lim_(t -> oo) sum_(i in cal(X)) P_(k i)^(t-1) P_(i j) \
  & = sum_(i in cal(X)) (lim_(t -> oo) P_(k i)^(t - 1)) P_(i j) = sum_(i in cal(X)) pi_i P_(i j)
$<eq:limiting-distrib-stationary>
(we can switch limit and sum since $cal(X)$ is finite and we are assuming the limit exists).

#definition(title: "Stationary distribution")[
  A distribution $pi$ on $cal(X)$ is stationary for a Markov chain if
  $
    pi_j = sum_(i in cal(X)) pi_i P_(i j) wide forall j in cal(X)
  $
]<def:stationary-distrib>

The definition of stationary distribution can be rewritten in matrix form as $ pi P = pi $
where $pi$ is a $1 times abs(cal(X))$ row vector.

We see from @eq:limiting-distrib-stationary that being stationary is a necessary condition for $pi$
to be a limiting distribution.

We can interpret @def:stationary-distrib as
$
  X_0 tilde pi ==> X_t tilde pi wide forall t >= 0
$

#theorem(title: [Existance and uniqueness of $pi$])[
  1. If $cal(X)$ is finite, a stationary distribution always exists.
  2. If $(X_t)_(t >= 0)$ is irreducible there is at most one stationary distribution.
]

#proof[Not required.]

=== Convergence in distribution

#definition(title: "Aperiodicity")[
  A Markov chain is aperiodic if, for all $i in cal(X)$, the greatest common divisor of the set
  ${t >= 1 | P^t_(i i) > 0}$ is $1$.
]

In short, it means that there are no cycles.

#theorem(title: "Convergence theorem")[
  Let $(X_t)_(t >= 0)$ be an irreducible and aperiodic Markov chain with stationary distribution
  $pi$.
  Then
  $
    P^t_(i j) -> pi_j wide "as" t -> oo, med forall i, j in cal(X)
  $
]

Since $cal(P) (X_t = j) = sum_(j in cal(X)) P^t_(i j) cal(P) (X_0 = i)$, the convergence theorem
implies that, regardless of the initial distribution of $X_0$, we have $cal(P)(X_t = j) = pi_j$ as
$t -> oo$.

This also tells us that, if the chain is aperiodic and irreducible, stationarity is necessary
*and sufficient* for $pi$ to be a limiting distribution, in this case we say that the chain
"converges to stationarity" (or "to equilibrium").

#remark[This is a convergence in distributions, not of fixed values.]

TODO: stopped before 1.4.3
