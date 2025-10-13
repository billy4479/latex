#import "lib/template.typ": template
#import "lib/theorem.typ": *
#import "lib/utils.typ": *

#show: template.with(
  title: "Stochastic processes",
  author: "Giacomo Ellero",
  date: "A.Y. 2025/2026",
)

#show: thm-init

#show "RV": [random variable]
#show "iid": [i.i.d.]

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
    prob(X_0, ..., X_n) = prob(X_0 = x_0) product^(n-1)_(i = 0) prob(
      X_(i+1) = x_(i+1) |
      X_i = x_i, ..., X_0 = x_0
    )
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
    prob(X_(t+1) = x_(t+1) | X_t = x_t, ..., X_0 = x_0) = prob(X_(t+1) = x_(t+1) | X_t = x_t)
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
  P_(i j) = prob(X_(t+1) = j | X_t = i) wide i, j in cal(X)
$
Note tat we can construct a *transition matrix* $P$ of all the combinations of transitional
probabilities in $cal(X)$.

A common problem is to compute the probability that a certain event $j$ occurs after $n$ steps:
$
  P^n_(i j) = prob(X_(t+n) = j | X_t = i)
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
    P_(i j)^(n + m) & = prob(X_(n+m) = j | X_0 = i) \
    & = sum_(k in cal(X)) prob(X_(n+m) | X_n = k, X_0 = i) prob(X_n = k | X_0 = i) \
    & = sum_(k in cal(X)) prob(X_(n+m) = j | X_n = k) prob(X_n = k | X_0 = i) \
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
  alpha_i^((t)) = prob(X_t = i)
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
  f_i & = prob(X_t = i "for some" t>=1 | X_0 = i) \
      & = prob(union.big_(t >= 1) {X_t = i} | X_0 = i)
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
and we set $min nothing = infinity$.
We also define the length of the $k$-th tour as
$
  T_k = S_k - S_(k-1)
$<eq:ktour>

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
    prob(V_i > r | X_0 = i) = f_i^r wide r >= 0
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
    P^(2n)_(00) & = prob(X_(2n) | X_0 = 0) \
                & = prob(Z_(2n) = n) wide "with" Z_(2n) tilde "Bin"(2n, p) \
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
  prob (X_t = j | X_0 = k) = P^t_(k j) -> pi_j wide "as" t -> +oo, med forall k, j in cal(X)
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
]<thm:convergence>

Since $prob (X_t = j) = sum_(j in cal(X)) P^t_(i j) prob (X_0 = i)$, the convergence theorem
implies that, regardless of the initial distribution of $X_0$, we have $prob(X_t = j) = pi_j$ as
$t -> oo$.

This also tells us that, if the chain is aperiodic and irreducible, stationarity is necessary
*and sufficient* for $pi$ to be a limiting distribution, in this case we say that the chain
"converges to stationarity" (or "to equilibrium").

#remark[This is a convergence in distributions, not of fixed values.]

Define the number of visits to state $i$ after $n$ iterations as
$
  V_i (n) = sum^n_(t = 1) bb(1) (X_t = i)
$<eq:def-vi>
and the average excursion time from $i$ as
$
  m_i = EE [T_1 | X_0 = i] wide "with" T_1 = min {t >= 1 | X_t = i}
$
as in @eq:ktour.

#theorem(title: [Asymptotic frequencies])[
  Let $(X_t)_(t >= 0)$ be an irreducible MC. Then
  1. Regardless of the starting distribution of $X_0$
    $
      (V_i (n))/n -> 1/m_i "almost surely as" n -> oo
    $
  2. If $pi$ is a stationary distribution for $(X_t)_(t >= 0)$, then
    $
      1/m_i = pi_i
    $
]<thm:asym-freq>

#proof[
  TODO: page 22
]

#theorem(title: [Ergodic theorem])[
  Let $(X_t)_(t >= 0)$ be an irreducible MC with stationary distribution $pi$.
  Then, for any bounded function $g: X -> RR$, we have
  $
    1/n sum^n_(t = 1) g(X_t) -> sum_(i in cal(X)) pi_i g(i) eq.colon EE_pi [g] wide "as" n->oo
  $
]

#proof[
  Assume $cal(X)$ is finite.

  By definition of $V_i$ in @eq:def-vi and by @thm:asym-freq we get
  $
    1/n sum^n_(t = 1) g(X_t) = sum^n_(t = 1) (V_i (n)) / n g(i) -> sum_(i in cal(X)) pi_i g(i) wide "as" n->oo
  $
]

This theorem is basically the Law of Large Numbers for MCs: in terms of approximated expectations
$EE_pi [g]$ we can treat MC states as iid RVs.

== Hitting times and probabilities

#definition(title: [Hitting time and probability])[
  Let $C subset cal(X)$.
  The hitting time of $C$ is
  $
    tau_C = min {t >= 0 | X_t in C}
  $
  while its hitting probability is
  $
    h(i) = prob(tau_C < oo | X_0 = i)
  $
]

Note that for any $i in cal(X) without C$ we have
$
  h(i) & = sum_(j in cal(X)) prob (tau_C < oo | X_1 = j, X_0 = i) prob(X_1 = j | X_0 = i) \
  & = sum_(j in cal(X)) prob (tau_C < oo | X_0 = j) prob(X_1 = j | X_0 = i) \
  & = sum_(j in cal(X)) h(j) P_(i j)
$

Therefore we have a set of equations we can use to compute ${h(i)}_(i in cal(X))$:
$
  h(i) = cases(
    sum_(j in cal(X)) h(j) P_(i j) wide & "if" i in cal(X) without C \
                                 1 wide & "if" i in C
  )
$

TODO: add section 1.6.1 in lecture notes

== Reversibility

#definition(title: [Reversible MC])[
  A MC $(X_t)_(t >= 0)$ with transitional probabilities $P_(i j)$ is reversible if, for some
  distribution $pi$,
  $
    pi_i P_(i j) = pi_j P_(j i) wide forall i, j in cal(X)
  $
]

#proposition[
  If a MC is reversible with distribution $pi$, then it is also $pi$-stationary.
]

#proof[
  We have
  $
    sum_(i in cal(X)) pi_i P_(i j) = sum_(i in cal(X)) pi_j P_(j i) = pi_j sum_(i in cal(X)) P_(j i)
  $
  then $(X_t)_(t <= 0)$ is $pi$-stationary.
]

We have two possible interpretations of reversibility:
/ Detailed-vs-Global balance: Note that $pi_i P_(i j)$ is the probability of observing
  $(X_t, X_(t+1)) = (i, j)$. Reversibility implies the "exchange" of probabilities between each
  state to be balanced, therefore we say that the chain is _detailed balanced_ w.r.t. $pi$.

  In contrast, stationarity can be written as
  $
    sum_(i in I) pi_i P_(i j) = sum_(i in I) pi_j P_(j i)
  $
  where the left term can be interpreted as the total probability going "into $j$", while the right
  side can be seen as the total probability going "out of $j$". In accordance with this intuition we
  can say that the chain is _globally balanced_ w.r.t. $pi$.

/ Time reversibility: If a MC is reversible then we cannot tell if we are running the chain
  "forwards" or "backwards". Formally, let $Y_0 = X_n, Y_1 = X_(n - 1), ..., Y_n = X_0$, then, if $X_t$
  is reversible, $(X_0, ..., X_n)$ and $(Y_0, ..., Y_n)$ have the same distribution.


== Examples

On the lecture notes, in chapter 2, we can find 3 examples of discrete time MCs.

We report the one about Hidden Markov Models: in this model at each time $t$ we observe a signal
$S_t$ which we assume is coming from some underlying MC. To construct this model we need a MC
$(X_t)_(t >= 0)$ with starting distribution $alpha$, a set of possible signals $cal(S)$ and
a function which tells us the probability that, given each state of the MC, a certain signal is
observed
$
  prob(S_t = s | X_t = j) = f(s | j) wide s in cal(S), j in cal(X)
$
where independence holds
$
  S_t perp (X_i, S_i)_(i != t) | X_t
$

This is just the basic mathematical structure, more examples can be found on the lecture notes.

= Continuous-time Markov chains

This time we consider stochastic processes where $t in [0, +oo)$ but discrete space (i.e. $cal(X)$
finite or countable).

== Tools

=== Exponential distribution

Recall that a random variable $X tilde "Exp"(lambda)$ with rate $lambda > 0$ if its pdf is
$
  f(x) = cases(lambda e^(-lambda x) & wide x>0, 0 & wide x <= 0)
$
and the corresponding cdf is
$
  F(x) = cases(1-e^(-lambda x) & wide x>0, 0 & wide x <= 0)
$

The mean and the variance are both equal to $lambda^(-1)$.

#definition(title: "Memoryless property")[
  A random variable $X$ valued in $(0, oo)$ is memoryless if
  $
    prob(X>s+t | X>t) = prob(X>s)
  $
]

Intuitively the memoryless property has the following interpretation: if an event hasn't occurred
yet at some time $t$, the probability that happens in the next $s$ units of time is the same as if
we started "looking for" the event now.

#proposition[
  $X tilde "Exp"(lambda)$ is memoryless.
]

=== Hazard rates

When $X$ represents the lifetime of some item or the time until an event occurs we can introduce the
hazard rate function $r(t)$ defined as
$
  r(t) = f(t) / (1-F(t))
$
where $f$ and $F$ are the pdf and the cdf of $X$. The hazard rate function represents the
probability of the event happening at time $t$ given that it has not happened yet before $t$.

The survival function of a RV $X$ is denoted as
$
  macron(F) (t) = prob(X > t) = 1 - F(t)
$

#proposition(title: "hrf characterize distributions")[
  Let $X$ be a positive valued random variable and $r$ its hazard rate function.
  Then
  $
    macron(F)(t) = e^(-integral_0^t r(s) dif s)
  $
]<prop:hrf-characterization>

#proof[TODO: page 44]

The hazard rate function for the exponential distribution is constant and equal to $lambda$. This is
what we expect from any memoryless distribution.
As the hazard rate function characterizes the distribution, the exponential distribution is the only
memoryless distribution.

#show "hrf": [hazard rate function]

#proposition(title: "First event")[
  Given $(X_i)_(i = 1, ..., n)$ independent rvs with hrf $r_i$ we have that the random variable
  defined as
  $
    X colon.eq min_(i = 1, ..., n) X_i
  $
  has hrf of
  $
    r(t) = sum^n_(i = 1) r_i (t)
  $
]
#proof[
  By definition of $X$ we have
  $
    macron(F) = prob(X > t) = prob(union.big_(i = 1)^n {X_i > t})
    = product_(i = 1)^n prob(X_i > t) = product_(i = 1)^n macron(F)_i (t)
  $
  Then, by @prop:hrf-characterization we have
  $
    macron(F)(t) = product^n_(i = 1) exp (- integral_0^t r_i (s) dif s) = exp (-integral_0^t r(s) dif s)
  $
  with $r(s) = sum^n_(i = 1) r_i (s)$, meaning that $r(s)$ hrf of $X$
]

#proposition(title: "Hazard race")[
  Given $(X_i)_(i = 1, ..., n)$ independent rvs with hrf $r_i$ we have that the random variable
  defined as
  $
    I colon.eq limits("arg min")_(i = 1, ..., n) med X_i
  $
  satisfies
  $
    prob(I = i | X = t) = (r_i (t)) / (sum_(j=1)^n r_j (t))
  $
  where $X$ is defined as in the previous proposition.
]

#proof[
  TODO: part two, page 46
]

#corollary[
  Let $X_i tilde "Exp"(lambda_i)$ independent for $i = 1, ..., n$. Then the RVs
  $
    X colon.eq min_(i = 1, ..., n) X_i wide "and" wide
    I colon.eq limits("arg min")_(i = 1, ..., n) med X_i
  $
  have distributions
  $
    X tilde "Exp"(sum^n_(i = 1) lambda_i) \
    prob(I = i) = lambda_i / (sum^n_(j = 1) lambda_j)
  $

  Moreover, $X perp I$.
]

== Markov property

#definition(title: "Markov property")[
  A continuous-time stochastic process $(X(t))_(t in [0, +oo])$ with discrete space $cal(X)$
  satisfies the Markov property if
  $
    prob(X(t+s) = j | X(s) = i, X(u) = x(u) "for" 0 <= u <= s) \
    = prob(X(t+s) = j | X(s) = i)
  $
]

A continuous-time MC (CTMC) is *time homogeneous* if the transition probabilities
$
  P_(i j)(t) colon.eq prob(X(t + s) = j | X(s) = i)
$
do not depend on $s$. We will always consider time-homogeneous CTMCs unless otherwise stated.

#proposition(title: "Chapman-Kolmogorov equations")[
  The transition probabilities satisfy
  $
    P_(i j) (s + t) = sum_(k in cal(X)) P_(i k) (s) P_(k j) (t)
  $
]

#proof[
  Same as @prop:chapman-kolmogorov.
]

When $abs(cal(X)) < oo$ we can rewrite it as
$
  P(t + s) = P(t) P(s)
$
where $P$ denote the transition probability matrix.

=== Generator/Jump rates

Unlike in discrete time we no longer have any minimal discrete unit of time e.g. $t = 1$. Instead,
to reason about the behavior of CTMCs we look at the behavior of $(P(t))_(t in [0, epsilon))$ for
some small $epsilon > 0$.

#definition(title: "Jump rate")[
  We define the jump rate (or instantaneous transition rate) from $i$ to $j$ of a CTMC as
  $
    Q_(i j) colon.eq lim_(h -> 0) (P_(i j)(h))/h
  $
]<def:jump-rates>

The jump rate can be interpreted as the "hazard rate" at which the MC currently in state $i$ jumps
to $j$ in the next infinitesimal instant.

#example(title: [Poisson Process])[
  The one-dimensional Poisson Process, which we denote as $(X(t))_(t in [0, oo)) tilde "PP"(lambda)$
  is a CTMC with $cal(X) = NN$ and jump rates
  $
    cases(
      Q_(i, i+1) = lambda & wide forall i in cal(X),
      Q_(i, j) = 0 & wide "for all other cases"
    )
  $
]<ex:poisson-process-1d>

== Kolmogorov differential equations

We want to compute the transition probabilities now, i.e. the probability that starting from $i$ and
after a certain time $t$, we end up in $j$. This is quite a bit harder than in the discrete case,
since now we don't know how many transition happen in the time interval $t$, in theory we could have
infinitely many.

Let us define $Q_(i i) = - sum_(j != i) Q_(i j)$ so that the matrix $Q$ is a full
$cal(abs(X)) times abs(cal(X))$ matrix, called the _generator matrix_.

#lemma[
  $
    Q = P'(0)
  $
  or equivalently
  $
    Q_(i j) = lr(dif / (dif t) P_(i j) (t) |)_t(0)
  $
]
#proof[
  See page 51, idea is that it is easily shown that $Q_(i j) = P'_(i j)$ for $i != j$, while if $i =
  j$, since $sum_(j in cal(X)) P_(i j) = 1$ we have $P_(i i) = 1 - sum_(j != i) P_(i j)$ and taking
  derivatives we obtain the result.
]

#theorem(title: [Kolmogorov forwards and backwards equations])[
  Let $X$ be a CTMC with finite $cal(X)$ and with a well-defined $Q$.
  Then the following equations are satisfied:
  / Backwards:
  $
    P'_(i j)(t) = sum_(k != j) Q_(i k) P_(k j) (t) - nu_i P_(i j) = (Q P(t))_(i j)
  $
  / Forwards:
  $
    P'_(i j)(t) = sum_(k != j) Q_(k j) P_(i k) (t) - nu_i P_(i j) = (P(t) Q)_(i j)
  $
]<thm:kolmogorov-differential>

#proof[
  TODO: page 51
]

These equations can be hard to solve, however they always allow a solution of the form
$
  P(t) = e^(t Q) = sum^oo_(n = 0) (t Q)^n / n!
$
as in matrix exponentiation.
It can be shown that this series always converges and solves the equations (no proof required).

== Jump chain and holding time

We will assume that the trajectory $t mapsto X(t)$ satisfies the following _cadlad_ assumptions:
$
  lim_(h -> 0) X(t + h) & = X(t) \
  lim_(h -> 0) X(t - h) & "exists"
$
this rule out trajectories which have an uncountable number of discontinuity points. However, this
is weaker than continuity, since otherwise when $cal(X)$ is discrete we only allow for constant
trajectories.

Under these assumptions chains can be represented by the *jump chain* $(Y_n)_(n = 0, 1, 2, ...)$
where $Y_n$ represents the $n$-th state visited by the chain $X_t$. Similarly we can define the
*holding times* $(T_n)_(n = 0, 1, 2, ...)$ where $T_n$ represents the amount of time spent in the
$n$-th visited state $Y_n$.

$
  X(t) = i <==> cases(
    T_0 + ... + T_(n-1) <= t <= T_0 + ... + T_n \
    Y_n = i
  )
$<eq:equi-def-ctmc>

Moreover, we can show (see page 55) that, by the Markov property and time homogeneity of the chain
$(T_0 | Y_0 = i) tilde "Exp"(nu_i)$ for some $nu_i$ which can depend on the state. This is because
we can show that $T_0 | Y_0$ satisfies the memoryless property.

When $X(t)$ makes a jump out of $i$ it will go to $j$ with some probability which we will denote as
$
  K_(i j) = prob(Y_1 = j | Y_0 = i)
$
Then the matrix $K$ is a matrix of transition probabilities and $(Y_n)$ is a discrete time Markov
chain. This means that, given $K$ and $(nu_n)_(n = 0, 1, 2,...)$, the CTMC spends
$T tilde "Exp"(nu_i)$ time in state $i$, then jumps to state $j$ with probability $K_(i j)$.
(mathematical formulation at eq 3.35 in lecture notes)

Mathematically, we can write the joint distribution of the jumping chain and holding times as
$
  cases(
    (Y_n)_(n = 0, 1, ...) "is a DTMC with transitional probabilities" K,
    T_n | Y_n = i tilde "Exp"(nu_i) "for every" i in cal(X),
    T_n perp ((Y_i, T_i)_(i != n) | Y_n)
  )
$<eq:jump-holding-distrib>

=== Connections between $(nu, K)$ and $Q$

#lemma[
  Let $X_t$ be a CTMC defined through jumping and holding times.
  Then, the jump rates $Q$ are well defined and
  $
    nu_i & = sum_(j != i) Q_(i j)& wide i in cal(X)\
    K_(i j) & = Q_(i j) / (sum_(ell != i) Q_(i ell)) & wide i, j in cal(X) "and" i != j
  $
]

#proof[
  We will prove that
  $
    Q_(i j) = nu_i K_(i j)
  $
  from which, we can easily prove the lemma, since $sum_(i != j) K_(i j) = 1$.

  Assume $i != j$, then we have
  $
    P_(i j) & = prob (X(h) = j | X(0) = i) \
    & >= prob (T_0 < h, Y_1 = j, T_1 > h | Y_0 = i) \
    & = prob (T_0 < h | Y_0 = i) prob (Y_1 = j | Y_0 = i) prob (T_1 > h | Y_1 = j) \
    & = (1 - e^(- nu_i h)) K_(i j) e^(-nu_j h)
  $
  for $h > 0$, where the first step is the definition of CTMC, the second one is @eq:equi-def-ctmc,
  and the last two steps are due to the property of the jumping chain and holding times described
  in @eq:jump-holding-distrib.

  Thus, by definition of $Q_(i j)$ we have
  $
    Q_(i j) = lim_(h -> 0) (P_(i j)(h))/h >= lim_(h -> 0) (1 - e^(- nu_i h))/h K_(i j) e^(nu_j h) =
    nu_i K_(i j)
  $

  We also have
  $
    P_(i i) = prob (X(h) = i | X(0) = i) >= prob (T_0 > h | Y_0 = i) = e^(- nu_i h)
  $
  again by @eq:equi-def-ctmc and @eq:jump-holding-distrib. From this inequality we get that
  $
    sum_(j != i) Q_(i j) = lim_(h -> 0) (1 - P_(i i)(h))/h <= lim_(h -> 0) (1 - e^(- nu_i h))/h = nu_i
  $

  Now we can combine $sum_(j != i) Q_(i j) <= nu_i$ with $Q_(i j) >= nu_i K_(i j)$ to get that
  $sum_(j != i) Q_(i j) = nu_i$. Finally, we can combine $sum_(j != i) Q_(i j) = nu_i$ with
  $Q_(i j) >= nu_i K_(i j)$ to obtain $Q_(i j) = nu_i K_(i j)$ as desired.
]

#remark(title: [Equivalent characterizations of CTMCs])[
  By now, we have shown three equivalent characterizations of CTMCs:
  1. Jump chains and holding times (@eq:equi-def-ctmc and @eq:jump-holding-distrib)
  2. Jump rates (@def:jump-rates)
  3. Kolmogorov differential equations (@thm:kolmogorov-differential)

  We have proven (1.) $==>$ (2.) $==>$ (3.). Proof that (3.) $==>$ (1.) is omitted.
]

== Limiting behavior of CTMCs

We want to see what happens in
$
  lim_(t -> oo) P(t)
$

#definition(title: "Stationary distribution")[
  $pi$ is a stationary distribution for a CTMC $X_t$ if
  $
    pi P(t) = pi
  $
]

#proposition[
  $pi$ is a stationary distribution if and only if
  $
    pi Q = underline(0)
  $
  (a vector of zeros).
]

#proof[
  Note that $pi$ is stationary if and only if $dif/ (dif t) pi P(t) = 0$.

  Assume that $pi Q = 0$, then we can use Kolmogorov equations to get
  $
    dif / (dif t) pi P(t) = pi P'(t) = pi Q P(t) = 0
  $
  which means that $pi P(t)$ is constant and since $P(0) = pi$ we conclude.

  Now assume that $pi$ is stationary, we have
  $
    0 = dif / (dif t) pi P(t) = pi P'(t) wide forall t >= 0
  $
  therefore at $t = 0$ we have $0 = pi P'(t) = pi Q$.
]

By expanding $pi Q = 0$ we get the *balance equations*:
$
  nu_j pi_j = sum_(i != j) pi_i Q_(i j)
$
called *global balance*. We can also impose a stronger *detailed balance*
$
  pi_j Q_(j i) = pi_i Q_(i j)
$

Both of these equations can be interpreted as "flows of probabilities" in the stationary state.

#lemma[
  Let $X$ be an irreducible CTMC.
  Then
  $
    P_(i j) (t) > 0
  $
  (strictly positive)
]
#proof[Skip.]

#theorem(title: [Convergence theorem for CTMCs])[
  Let $X$ be an irreducible CTMC with stationary distributino $pi$, then
  $
    P_(i j) (t) -> pi_j
  $
]
#proof[Skip.]

== Example: Poisson processes

#definition(title: [Independent increment])[
  A stochastic process $N = (N(t))_(t in [0, +oo])$ has independent increment if $forall n >= 1$ and
  $forall t_1 <= t_2 <= ... <= t_n$ the random variables
  $
    N(t_1), wide N(t_2) - N(t_1), wide ..., wide N(t_n) - N(t_(n-1))
  $
  are independent.
]

#definition(title: [Stationary increment])[
  A stochastic process $N = (N(t))_(t in [0, +oo])$ has stationary increment if $forall n >= 1$ and
  $forall t, s > 0$ the random variables
  $
    N(t + s) - N(s)
  $
  does not depend on $s$.
]

#definition(title: [Counting process])[
  A stochastic process $N = (N(t))_(t in [0, +oo])$ is a counting process if
  1. $N(0) = 0$;
  2. $N(t)$ is an $NN$-valued random variable $forall t$;
  3. $t mapsto N(t)$ is almost surely right-continuous and non-decreasing.
]

Then, given a counting process, *inter-arrival times* are the sequence $T_0 ,T_1, ...$ defined as
$
  N(t) > n <==> T_0 + ... + T_n <= t
$
#definition(title: [Poisson Process (PP)])[
  A counting process $N = (N(t))_(t in [0, oo])$ is a PP with rate $lambda > 0$, i.e.
  $N tilde "PP"(lambda)$ iff one of the following equivalent conditions holds:
  / Infinitesimal definition: $N$ has independent increments and
    $
      cases(
        prob (N(t+h) = N(t) = 1 | N(t) = i) = lambda h + o(h) wide "as" h -> 0,
        prob (N(t + h) - N(t) > 1) = o(h)
      )
    $

  / Arrivals times: the inter-arrival times $T_0, T_1, ...$ satisfy
    $
      T_0, T_1, T_2, ... attach(tilde, t: "i.i.d.") "Exp"(lambda)
    $

  / Poisson Increments: $N$ has independent increments and
    $
      N(t + s) - N(s) tilde "Poisson"(lambda t)
    $
]

In 1 dimension this is a special case of CTMC with $cal(X) = NN$ where we jump to the right with
rate $lambda$.

#remark[
  Recall that $"Poisson"(lambda_1) * "Poisson"(lambda_2) = "Poisson"(lambda_1 + lambda_2)$.
  This means that the sum of two independent rvs with Poisson distribution with parameters
  $lambda_1, lambda_2$ is a rv with Poisson distribution and parameter $lambda_1 + lambda_2$.
]

=== Non-homogeneous generalization

#definition(title: [Non-Homogeneous Poisson Process])[
  A stochastic process $N = (N(t))_(t in [0, oo)$ is a NHPP with intensity function
  $
    lambda(t) : [0, +oo) -> [0, +oo)
  $
  if one of the following conditions holds:
  1. $N$ has independent increments and
  $
    N(t + s) - N(s) tilde "Poisson"( integral_s^(t + s) lambda(y) dif y)
  $
  2. $N$ has independent increments and
  $
    cases(
      prob (N(t + h) - N (t) = 1) = lambda (t) h + o (h),
      prob (N(t + h) + N(t) > 1) = o(h)
    )
  $
]

In the NHPP case the inter-arrival times $T_0, T_1, ...$ are no longer independent nor
exponentially distributed.

=== General domains generalization

So far we have considered events happening in time, i.e. $cal(D) = [0, +oo)$. Now we consider the
general case where our domain is $cal(D) subset.eq RR^d$ for $d >= 1$.

Given a domain $cal(D)$, we define the set of _point patterns_ as
$
  macron(cal(D)) = { D in cal(P)(cal(D)) | D "is finite" }
$

Then, a *point process* is a random object with values in $macron(cal(D))$, i.e. a measurable
function
$
  N: Omega -> macron(cal(D))
$
where $(Omega, F, prob)$ is some probability space.
Equivalently, a point process can be written as
$
  N = (N(A))_(A subset.eq cal(D))
$
where $N(A)$ is the number of points in $A$.

#definition(title: [General Domain Poisson Process])[
  A point process $N = (N(A))_(A subset.eq cal(D))$ is a Poisson Process with intensity measure
  $lambda$, where $lambda$ is a measure on $cal(D)$, if one of the following equivalent definitions
  holds
  1. $N(A) prop N(B)$ for all $A, B subset.eq cal(D)$ such that $A inter B = nothing$;
  2. $N(A) tilde "Poisson"(lambda(A))$ for all $A subset.eq cal(D)$.
]

When $cal(D)$ is general, there is no natural notion of inter-arrival times as $cal(D)$ may not be
totally ordered.

=== Properties of PP models

#proposition(title: [Superposition])[
  Let $N_1 = (N_1 (A))_(A subset.eq cal(D))$ and $N_2 (N_2 (A))_(A subset.eq cal(D))$ be two
  independent PPs on a domain $cal(D)$ with intensity measures $lambda_1$ and $lambda_2$, then
  $N_3 = N_1 + N_2$ is a also a PP on $cal(D)$ with intensity measure
  $lambda_3 = lambda_1 + lambda_2$.
]

#proposition(title: [Thinning])[
  Let $N tilde "PP"(lambda)$ on domain $cal(D)$.
  Suppose that each point in $N$ is either of type 1 or 2, with probability $p$ or $1-p$
  independently of the others. Then, we define $N_1$ and $N_2$ to be the point process which
  considers only the points of the associated type: $N_1 tilde "PP"(lambda_1)$ and
  $N_2 tilde "PP"(lambda_2)$ where $lambda_1 = lambda p$ and $lambda_2 = lambda (1-p)$.
]

#remark[
  It is possible to show that (under regularity assumptions) any point process with independent
  increment is a PP with
  $
    lambda (A) = EE [N(A)]
  $
]
