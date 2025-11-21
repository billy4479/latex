#import "lib/template.typ": *
#import "lib/theorem.typ": *
#import "lib/utils.typ": *

#show: template.with(
  titleString: "Stochastic processes",
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

Define the probability of returning to state $i$, starting from state $i$, as
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
and we set $min varnothing = infinity$.
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
  #set enum(numbering: "a)")
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
  #set enum(numbering: "a)")
  1. Fix $i in cal(X)$. If $i$ is transient, then $m_i = oo$ and $lim_{n -> oo} V_i (n) = V_i$ is
    finite (by @prop:prob-vi), therefore $lim_(n -> oo) V_i (n)/n = 0 = 1/m_i$.

    Assume now that $X_0 = i$ and $i$ is recurrent. Then, since $T_1, T_2, ...$ are iid, by the
    strong law of large numbers we have that
    $
      S_k / k ->^"a.s." m_i wide "as" k -> oo
    $

    Moreover, by definition of $(S_k)_(k >= 0)$ and $V_i$, we have
    $
      S_(V_i (n)) <= n <= S_(V_i (n) + 1) \
      ==> S_(V_i (n)) / (V_i (n)) <= n/(V_i (n)) <= S_(V_i (n) + 1) / (V_i (n))
    $

    By recurrence we have that $V_i (n) -> oo$ almost surely as $n -> oo$, this means that
    $
      m_i &= lim_(k -> oo) S_k / k = lim_(n -> oo) S_(V_i (n)) / (V_i (n)) \
      &<= lim_(n -> oo) n/(V_i (n)) <= lim_(n -> oo)S_(V_i (n) + 1) / (V_i (n) + 1) \
      &= lim_(k -> oo) S_k / k = m_i
    $
    which implies $lim_(n -> oo) n/(V_i (n)) = m_i$ as desired.
  2. By part a) we have that $lim_(n -> oo) EE[(V_i (n))/n] = m_i$ (by some magic??) then
    $
      1/m_i = lim_(n -> oo) EE[(V_i (n))/n] = lim_(n -> oo) (sum^n_(t = 1) EE[bb(1) (X_t = i)])/n
      = lim_(n -> oo) (sum^n_(t = 1) pi_i)/n = pi_i
    $
    as desired.
]

#theorem(title: [Ergodic theorem])[
  Let $(X_t)_(t >= 0)$ be an irreducible MC with stationary distribution $pi$.
  Then, for any bounded function $g: cal(X) -> RR$, we have
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

Note that this theorem _does not_ require aperiodicity. Indeed aperiodicity is needed for the
convergence of the average "time" spent on each state (which is what the ergodic theorem says).

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
    sum_(j in cal(X)) h(j) P_(i j) wide & "if" i in cal(X) without C,
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
    T_0 + ... + T_(n-1) <= t <= T_0 + ... + T_n,
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
  Let $X$ be an irreducible CTMC with stationary distribution $pi$, then
  $
    P_(i j) (t) -> pi_j
  $
]
#proof[Skip.]

Note that we do not require periodicity here (as we did in the convergence theorem for DTMCs) since
periodicity itself doesn't really make sense for CTMCs: since holding times are random themselves
there is not such thing as periodicity.

= Processes with continuous time and space

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

== Poisson processes

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
  $<eq:non-homo-pp-inc>
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
  1. $N(A) prop N(B)$ for all $A, B subset.eq cal(D)$ such that $A inter B = varnothing$;
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

== Brownian Motion <sec:brownian-motion>

The Brownian Motion (BM) is defined as the limit of a random walk on $ZZ$: consider
$delta x, delta t > 0$ and define a continuous-time stochastic process $X$ as
$
  X_t = delta x Y_(ceil(t / (delta t)))
$
This process makes jumps of size $delta x$ either up or down (with
probability $1/2$) every $delta t$.

Therefore we can write
$
  Y_n = Z_1 + ... + Z_n wide "where"
  quad cases(prob(Z_i = 1) = 1/2, prob(Z_i = -1) = 1/2, Z_i perp Z_j)
  quad forall i in {1, ..., n}
$
This means that
$
  & EE[Y_n]  & = & n EE[Z_1]  & = 0 \
  & var[Y_n] & = & n var[Z_1] & = n \
$
which gives us
$
  & EE[X_t] = 0 \
  & var[Y_n] = (delta x)^2 ceil(t/(delta t))
$
and by taking $delta x = O(sqrt(delta t))$ we get
$
  lim_(delta t -> 0) var(X_t) = lim_(delta t -> 0) sigma^2 delta t ceil(t / (delta t)) = sigma^2 t
$
for some $sigma >0$.

Moreover, since $Z_1, ..., Z_n$ are iid, by the central limit theorem we get
$
  X_t ->^d N(0, sigma^2 t) wide "as" delta x -> 0, forall t > 0
$
Then, we fix $T > 0$ and $delta x = sigma sqrt(delta t)$ such that
$
  ( X_t )_(t in [0, T]) ->^d ( B_t )_(t in [0, T]) wide delta t -> 0
$
converges in distribution to the Brownian Motion with variance $sigma^2$.
The sequence of distributions over trajectories converges to a limiting distribution over
trajectories.

#definition(title: [Brownian Motion])[
  A continuous-time stochastic process $X = (X_t)_(t in [0, oo))$ on $cal(X) = RR$ is a Brownian
  Motion with variance $sigma^2$ if
  1. $prob (X_0 = 0) = 1$
  2. $prob (t mapsto X_t "is continuous" forall t in [0, oo)) = 1$
  3. The process has stationary and independent increments
  4. $X_t tilde N(0, sigma^2 t)$ for every $t in [0, oo)$
]<def:brownian-motion>

Brownian motion can also be defined on $RR^d$, where each component $X_t^((i))$ of the random vector
$X_t$ is a one dimensional BM.

#theorem(title: "Wiener")[
  A distribution over the space of functions $t mapsto X_t$ from $[0, oo)$ to $RR$ which
  satisfies @def:brownian-motion exists.
]

=== Properties

#proposition(title: [Invariances of BM])[
  Let $X tilde "BM"(sigma)$. Then
  1. (*Rescaling*) Let $a, b > 0$ and $Y_t = a X_(t/b)$ for all $t$.
    Then $(Y_t) tilde "BM"((a sigma)/sqrt(b))$
  2. (*Time reversal*) Let $Y_t = X_(1 - t) - X_1$ for all $t$. Then $(Y_t) =^d (X_t)$
  3. (*Inversion*) Let $Y_0 = 0$ and $Y_t = t X_(1/t)$ for all $t$. Then $(Y_t) tilde "BM"(sigma)$.
]

#proof[Skip.]

Moreover, the following properties of the trajectories of a BM are satisfied with probability 1:
1. (*Continuity*):
  $
    prob (t mapsto X_t "is continuous" forall t in [0, oo)) = 1
  $
2. (*Nowhere differentiability*):
  $
    prob (t mapsto X_t "is not differentiable" forall t in [0, oo)) = 0
  $
3. (*Recurrence*):
  $
    prob (t mapsto X_t "crosses 0 infinitely many times" forall t in [0, oo)) = 0
  $
4. (*Recurrence near zero*): for any $epsilon > 0$
  $
    prob (t mapsto X_t "crosses 0 infinitely many times" forall t in [0, epsilon)) = 0
  $


== Gaussian Processes

This is, in some way, a "generalization" BM.
While the canonical case is $T = [0, +oo)$ and $cal(X) = RR$, the general case is $T = RR^m_+$ and
$cal(X) = RR^d$.

#definition(title: [Gaussian Process (GP)])[
  $X = (X_t)_(t in T)$ is a Gaussian Process if, for every finite $k in NN$ and every collection
  $t_(1:k) in T^k$, the random vector $X_(t_(1:k)) = (X_(t_1), ..., X_(t_k))$ has multivariate
  Gaussian distribution (MVG).
]

This is equivalent to saying that $X$ has MVG finite dimensional distribution.

#proposition[
  $X tilde "BM"(sigma)$ is a Gaussian Process.
]

#proof[
  For $t_(1:h) in [0, +oo]^h$ we have that
  $
    X_(t_(1:h)) = (X_(t_1), ..., X_(t_h))
  $
  can be written as
  $
    X_(t_(1:h)) = M z wide "for" z = vec(X_(t_1), X_(t_2) - X_(t_1), dots.v, X_(t_h) - X_(t_(h-1)))
    "and" M "is an appropriate" h times h "matrix"
  $
  Then, since MVG is closed under linear transformation we can conclude.
]

#remark[
  If $X, Y$ are two stochastic processes with continuous trajectories and
  $
    X_(t_(1:k)) = Y_(t_(1:k)) wide forall k in NN
  $
  then
  $
    X =^d Y
  $
]

=== Mean and covariance

Let, for all $t, s in T$,
$
     m(t) & = EE [X_t] \
  C(t, s) & = cov (X_t, X_s)
$

Then, if $X$ is a Gaussian Process, $m, C$ uniquely characterize the processes.

#example(title: [Brownian Motion])[
  Let $X tilde "BM"(sigma)$. Then
  $
    m(t) = EE[X_t] = 0
  $
  and
  $
    C(t, s) & = EE[X_t X_s] \
            & = EE[X_t (X_t +(X_s - X_t))] \
            & = EE[X_t^2] + EE[X_t (X_s - X_t)] \
            & = sigma^2 t + EE[X_t] EE[X_s - X_t] \
            & = sigma^2 t
  $
]

#example(title: [Brownian Bridge])[
  Let $X tilde "BM"(sigma)$ and
  $
    (Y_t)_(t in [0, 1]) = (X_t)_(t in [0, 1]) | X_1 = 0
  $
  Since MVGs are closed under conditioning, $Y tilde "GP"$ too.

  In this case we have
  $
    cases(
      m(t) = EE[Y_t] = EE[X_t | X_1 = 0] = 0 wide &,
      C(t, s) = sigma^2 t (1 - s) wide & 0 <= t < s <= 1
    )
  $
]

#definition(title: [Brownian Bridge])[
  A Brownian Bridge with variance variance $sigma^2$ ending at $Y_s = y$ is a Gaussian Process with
  $T = [0, s]$ and
  $
    cases(
      m(t) = t/s y wide & t in [0, s],
      C(t, t') = sigma^2 t (s - t') wide & 0 <= t < t' <= s
    )
  $
]

#figure(
  image("./assets/stochastic-processes/brownian-bridge.png"),
  caption: [Trajectories of a one-dimensional Brownian bridge],
)

#lemma[
  If $X tilde "GP"(0, C)$, then
  $
    Y_t = X_t + m(t)
  $
  satisfies $Y tilde "GP"(m, C)$.
]

This means we can focus on zero-mean GPs without loss of generality.
Then, the only key parameter is $C$. A function $C$
$
  C: T times T -> RR
$
is a valid covariance parameter if is a symmetric positive (semi) definite (SPD) function.
Any valid $C$ induces a valid GP: SPD functions in this contexts are called _kernels_.


#figure(
  image("./assets/stochastic-processes/spd-examples.png"),
  caption: [
    In the top row: 3 examples of one-dimensional SPD functions with different regularity conditions
    at $0$. On the bottom row: the resulting trajectories of GPs with the above $C$ functions.
  ],
)

== Diffusion Processes

The starting point is the infinitesimal definition of BM, which can also be written in the following
equivalent way:
$X tilde "BM"(sigma)$ is the only continuous Markov Process on $RR$ such that the increments
$Delta_(t, h) := X_(t+h) + X_t$ satisfy the following properties as $h -> 0$:
1. (zero drift)
  $
    EE[Delta_(t, h) | X_t = x] = 0 + o(h)
  $
2. (instantaneous variance of $sigma^2$)
  $
    EE[Delta_(t, h)^2 | X_t = x] = sigma^2 t + o(h)
  $
3. (no jumps)
  $
    prob (abs(Delta_(t, h)) > epsilon | X_t = x) = o (h)
  $

We can generalize the above definition as follows:

#definition(title: [Diffusion process])[
  A continuous Markov Process $X$ with continuous trajectories is a diffusion process with drift
  function $mu(x, t)$ and instantaneous variance (volatility) $sigma^2 (x, t)$ if, as $h -> 0$, the
  following hold:
  1. Drift:
    $
      EE[Delta_(t, h) | X_t = x] = mu (x, t) h + o(h)
    $
  2. Volatility
    $
      EE[Delta_(t, h)^2 | X_t = x] = sigma^2 (x, t) t + o(h)
    $
  3. No jumps
    $
      prob (abs(Delta_(t, h)) > epsilon | X_t = x) = o (h)
    $
]

If the above holds, we say that the stochastic process $X$ solves the stochastic differential
equation (SDE)
$
  dif X_t = mu(X_t, t) dif t + sigma (X_t, t) dif B_t
$

We can compare this SDE with an ODE (let $t mapsto X_t$ be deterministic):
$
  (dif X_t)/(dif t) = mu (X_t, t)
$
which is equivalent to
$
  lim_(h -> 0) (X_(t + h) - X_t)/h = mu(X_t, t)
$

Meanwhile, in the SDE case (there $t mapsto X_t$ is _not_ deterministic) we have that
$
  & lim_(h -> 0) EE[(X_(t + h) - X_t)/h mid(|) X_t = x]   &    = mu(x, t) \
  & lim_(h -> 0) EE[(X_(t + h) - X_t)^2/h mid(|) X_t = x] & = sigma(x, t)
$
Note that the second equation is satisfied in the deterministic case only if $sigma(x, t) = 0$
anywhere.

Meanwhile, the notation $dif B_t$ comes from the fact that, for some small $h > 0$ we can write
$
  X_(t + h) approx X_t + mu(X_t, t) + sigma (X_t, t) sqrt(h) Z
$
where $Z tilde N(0, 1)$ independent of the rest is the noise term, which is scaled by a larger
$sqrt(h)$ factor.

Then
$
  X_(t + h) = X_t + mu(X_t, t) + sigma (X_t, t) (B_(t + h) + B_t)
$
where $B tilde "BM"(1)$ is the "driving" Brownian motion.

=== Transition kernels

Let $(X_t)$ be a time-homogeneous, continuous-time Markov process on $cal(X) = RR$.
We define the transition kernel $P^t (x, y)$ with $x, y in RR, t > 0$ as the density of $X_t$ at $y$
given that $X_0 = x$, i.e. $P^t (x, y)$ is such that
$
  prob (X_t in A | X_0 = x) = integral_A P^t (x, y) dif y wide A subset.eq RR
$

#example(title: [Transition Kernel of a BM])[
  For $X tilde "BM"(sigma)$, we have that
  $
    P^t (x, y) = 1 / sqrt(2 pi t sigma^2) exp (- (x-y)^2 / (2 t sigma^2))
  $
]

The transition kernel can also be seen as an operator on functions: for every $f: RR -> RR$ we
define $P^t f : RR -> RR$ as
$
  P^t f (x) = integral f(y) P^t (x, y) dif y = EE[f(X_t) | X_0 = x]
$
where the following property also holds:
$
  P^t P^s f = P^(t + s)
$

= Monte-Carlo methods

These are algorithms which rely on repeatedly sampling at random to obtain some result of interest.

== Pseudo-Random Number Generators

=== Uniform distribution

Pseudo-random number generators (PRNGs) produce a _deterministic_ way to produce a sequence of
numbers in $[0, 1]$ which _imitates_ a sequence of iid uniform random variables $cal(U)_[0, 1]$.

PRNGs need a _seed_ $X_0$ which is the initial value for this sequence and it is "secret": given
$(X_1, ..., X_n)$ but not $X_0$ it should be impossible to predict $X_(n+1)$.

#example(title: [Linear congruential generator])[
  Given a seed $X_0$, consider the sequence
  $
    X_(i + 1) = (a X_i + c) op(%) m
  $
  defined by induction, where $a, c, m in NN$ are chosen such as $a < 0 < m$ and $0 <= c < m$.
  Note that $m$ is the "modulus" which means that after $m$ samples, $X_m = X_0$, therefore $m$
  should be chosen big enough.

  More sophisticated LCGs may introduce extra permutation steps.
]

There are many tests we could make to make sure that the above algorithm yields actually an uniform
distribution.

=== Other distributions

Given $y tilde cal(U)_[0, 1]$ we can generate a pseudo-random variable $x$ which mimics another
distribution using the cdf $F(x) = integral_(-oo)^x P(z) dif z$ of that distribution:
$
  x = F^(-1) (y) "with" y tilde cal(U)_[0, 1] "has the desired distribution"
$

#example(title: [Exponential distribution])[
  Given $y tilde cal(U)_[0,1]$,
  $
    x = - 1/lambda log y
  $
  is distributed as $"Exp"(lambda)$.
]
#proof[
  We know that the cdf of the exponential distribution is $F(x) = 1 - e^(- lambda x)$.
  Then, we can invert it as follows:
  $
    e^(-lambda x) & = 1 - F(x) \
        -lambda x & = log (1 - F(x)) \
                x & = - 1/lambda log(1-F(x))
  $
  which gives us $F^(-1)(y) = - 1/lambda log (1-F(y))$.
]

#example(title: [Gaussian distribution: Box-Muller method])[
  Given $y_1, y_2 tilde U_[0,1]$ independent, then
  $
    x_1 & = sqrt(- 2 log (y_1)) cos(2 pi y_2) \
    x_2 & = sqrt(- 2 log (y_2)) sin(2 pi y_2)
  $
  are independent and distributed as $cal(N)(0, 1)$.

  We can then scale them such that
  $
    z = mu + x sigma tilde N(mu, sigma)
  $
]

#proof[
  This is just a sketch.

  The key idea is that, given $x_1, x_2 tilde N(0, 1)$,
  $
    x_1^2 + x_2^2 tilde "Exp"(1/2)
  $

  Then, we write the combined pdf in polar coordinates, and integrate it to obtain the cdf and we
  invert it.
]

== Motivation

Our goal is to compute the integral of a function $f$ in $D$ dimensions on a bounded domain where we
are allowed $N$ evaluations of $f$ itself.

Using classical methods we would use an $N$ elements Riemann sum or some other more sophisticated
method. With these methods the error is $O(1/N^(k/D))$ (where $k$ depends on the method chosen,
$k in {1, ..., 4}$), however this means that most likely $D >> k$ and that the error is exponential
in the number of dimensions.

When using a MC method instead we sample $x_i$ iid with $i in {1, ..., N}$ and let the approximated
integral $I_N$
$
  I_N = 1/N sum_i f(x_i)
$
By the central limit theorem, $I_n -> I$ as $N -> oo$, where $I$ is the true integral, and
$
  norm(I_N - I) tilde 1/sqrt(N)
$
This is actually worse than classical methods when $D = 1$, however it becomes quickly better in
more dimensions.

#example(title: [Poisson process])[
  We sample $T_i tilde "Exp"(lambda)$ and let $t_(i+1) = t_i + T_i$, then
  $(t)_(i) tilde "PP"(lambda)$. Therefore this is very easy to simulate, we can just draw from the
  exponential distribution, which is way more efficient than discretizing time.

  In the inhomogeneous case this is quite harder, however, defining the _integrated rate function_
  as
  $
    Lambda (t) = integral_0^t lambda(u) dif u
  $
  we get that, given $t_n = t$, the next inter-event time $t_(n+1) = t + x$ has cdf
  $
    F(x) = 1 - exp(- (Lambda (t+x) - Lambda(t)))
  $
]

#solution[
  We start by discretizing time:
  $
    prob(t_(n+1) > t + x) & = product^(x/(dif t))_(k = 1) (1 - lambda(t + k dif t) dif t) \
    & = exp (sum^(x/(dif t))_(k = 1) log (1 - lambda(t + k dif t) dif t) ) \
    & = exp (sum^(x/(dif t))_(k = 1) - lambda(t + k dif t) dif t + o(dif t^2)) \
    & = exp (- integral_t^(t+x) lambda (u) dif u) \
    & = exp (- (Lambda(t+x) - Lambda(t))) \
  $
  where in the second step we Taylor expanded the logarithm and in the third one we used the
  definition of Riemann integral.

  This gives us that
  $
    prob (t_(n+1) < t + x) = F(x) = 1 - exp(-(Lambda(t + x) - Lambda(t)))
  $

  Then
  $
    t_(n+1) = Lambda^(-1) (E + Lambda (t_n)) wide "with" E tilde "Exp"(1)
  $
  which gives us an easy way to simulate the process. However, this still assumes we can compute
  $Lambda^(-1)$, which is not always the case.

  If $Lambda$ is not easy to invert we can instead use the *thinning method*.
  Consider a function $mu$ easy to invert such that $mu(t) >= lambda(t)$ for all $t$.
  Then, generate events using the dominating rate function $mu(t)$ and each event is accepted with
  probability $lambda(t) / mu (t)$. We can show that the set of accepted events forms a Poisson
  process with the desired distribution.
]

== Simulating CTMCs - Gillespie algorithm

1. Initialize $t = 0$ and choose the initial state $X(0)$.
2. Let $a_i (t)$ be the transition rate at time $t$ for state $i$.
3. Let $a_"tot"(t) = sum_i a_i (t)$.
4. Draw the next transition time $tau$ from $"Exp"(a_"tot" (t))$.
5. Draw the state identity from probabilities $p_i = (a_"tot" (t))/a_i$.
6. Set $t <- t + tau$ and the state of the system to the selected one.
7. Go to step 2.

== Metropolis-Hastings algorithm

We want to build an irreducible Markov chain such that its stationary distribution converges to a
desired distribution. Then we can simulate the MC with Monte-Carlo methods and then use the result
to simulate the desired probability:
$
  angle(f(x))_"MC" = 1/N_s sum^(N_s)_(i = 1) f(x_i)
$
where $(x_i)_(i)$ are $N_s$ samples from the distribution obtained by the algorithm. Then
$angle(f(x))_"MC" tilde angle(f(x)) = integral f(x) P(x) dif x$ as $N_s -> oo$ (by the LLN).

=== Motivation

This algorithm was invented to approximate sampling from the Boltzmann distribution:
$
  P_B (x) = 1/Z exp (- E(x) beta) wide "with" cases(
    Z = integral exp(E(x) beta) dif x,
    beta = (k T)^(-1)
  )
$
where $k$ is the Boltzmann constant, $T$ is the (constant) temperature, and $E(x)$ is the energy
associated with state $x$ of the system. The issue here is to compute the normalization factor $Z$,
as computing the integral over all the possible states of the system is virtually impossible.

=== Definition

#definition(title: [Metropolis-Hastings])[
  1. Choose an initial state $x_0$.
  2. Choose a set of "moves" associated with probabilities $q(x -> x')$ such that
    $
      sum_(x') q(x -> x') = 1
    $
  3. Draw a _proposed_ move from $q$:
    1. If $P_B (x') q(x' -> x) >= P_B (x) q(x -> x')$ we accept the move with probability 1.
    2. Else we accept the move with probability
      $
        (P_B (x') q(x' -> x))/(P_B (x) q(x -> x'))
      $
  4. Go to step 3.
]

Note that in this case to sample from $P_B$ we don't need to know $Z$, as it cancels with the one
from the other $P_B$.

=== Properties

The probability to accept a move with probability
$
  min(1, (P_B (x') q(x' -> x))/(P_B (x) q(x -> x')))
$
and if we assume symmetric probabilities, i.e. $q(x -> x') = q(x' -> x)$ we can simplify the
acceptance probability to the ratio of the Boltzmann probabilities.
Moreover, in systems with an energy function the ratio of probabilities is
$
  (P_B (x')) / (P_B (x)) = exp ( -beta(E(x') - E(x)))
$

We write the probability of $x -> x'$ as
$
  W(x -> x') = q(x -> x') min(1, (P_B (x') q(x' -> x))/(P_B (x) q(x -> x')))
$

=== Convergence

The proposed Markov chain is irreducible and aperiodic, this means that the convergence theorem
guarantees that it will converge to a stationary distribution $P_M$.

$
  P_M (x, t + 1) & = sum_(x') P_M (x', t) W(x' -> x) \
  & = P_M (x, t) + sum_(x' != x) P_M(x', t) W(x' -> x) - P_M (x, t) W(x' -> x)
$

To prove convergence we want to show that the derivative of the $D_"KL"$ divergence is always
negative, therefore the divergence is monotonically decreasing:
1. Compute the $D_"KL"$ divergence
2. Compute it's derivative
3. Use the Forward Kolmogorov Equation to get
$
  (dif P_M (x, t))/(dif t) = sum_(x' != x) P_M (x', t) W(x' -> x) - P_M (x, t) W(x -> x')
$
4. Use the fact that, in the stationary state, $P_M^*$ must obey to detailed balance
$
  P_M^* (x') W(x' -> x) = P_M^* (x) W(x -> x') wide forall x, x'
$

TODO: see photo of the board

The issue here is that the convergence can be very slow. Moreover, if the temperature is very low we
can easily get stuck in a local minima and not explore the whole distribution.

=== Example: Ising model

This is a simplified model for ferromagnetic material. There are $N$ atoms with a spin
$S_i in {-1, 1}$ which are located on a $D$ dimensional grid, here we will consider $D = 2$.

The energy of the system is defined as
$
  E(S) = -J sum_(angle(i, j)) S_i S_j
$
where in this case the sum goes through over all the pairs of $(i, j)$ which are neighbors on the
grid (in $D = 2$ each atom has 3 neighbors). $J > 0$ is the strength of the ferromagnetic
interactions.

To minimize energy we want all spins oriented in the same direction.

==== Goal

Our goal is to compute the following quantities depending on the temperature $T$:
$
  angle(E) & = sum_S E(S) P_B (S) wide          &        "average energy" \
  angle(M) & = sum_S 1/N sum_i S_i P_B (S) wide & "average magnetization" \
$
the issue here is that we cannot compute the sum over all possible states $S$.

==== The algorithm

The allowed moves are flipping a single spin: we select an atom at random and we accept to flip its
spin with probability
$
  cases(
    1 wide & "if" Delta E < 0,
    exp(- (Delta E) / T) & "otherwise"
  ) wide "where" Delta E "is the difference in energy"
$

In $D = 2$, $Delta E in { -8, -4, 0, 4, 8 }$. At low temperature we expect our system to be close to
the global minima $E = -2 N$ (where the spins are all 1 or -1), while at high temperature we expect
$angle(E) -> 0$ (as the Boltzmann distribution becomes a uniform distribution).

=== Problems with Metropolis-Hastings algorithm

The classic MH algorithm has various drawbacks: while it works well with simple energy landscapes
and far from critical point (like phase transitions), the algorithm is extremely slow near phase
shifts and can fail to escape local minima.

==== Wolff algorithm

This is a variation of the classic MH algorithm which belongs to the class of cluster algorithms.

The algorithm picks a random spin to flip called "seed", then starting from the seed it looks for
neighbours of the seed with the same spin: each neighbour is added to the cluster with probability
$P_"add"$ and the process repeats until all neighbours are checked.

Moreover, we can compute that detailed balance is obeyed if and only if
$
  (q(x -> x') A(x -> x')) / (q(x -> x') A(x -> x')) &= (1 - P_"add")^(m-n) (A(x-> x'))/(A(x' -> x))\
  & = exp(-beta(E(x') - E(x))) \
  & = exp(-2 beta(m - n)) \
  ==> (A(x-> x'))/(A(x' -> x)) &= (e^(2 beta) (1 - P_"add"))^(n - m)
$
where
- $A(x -> x')$ is the acceptance probability for $x -> x'$.
- $m$ is the number of bonds that are broken by flipping $x -> x'$ while $n$ is the number broken by
  flipping $x' -> x$.
- $E(x') - E(x) = 2(m - n)$.
Therefore by choosing $P_"add" = 1 - e^(-2 beta)$ we get that we can choose $A = 1$ for all $x, x'$
so that the cluster is always accepted.

==== Varying temperature algorithms

These are algorithms which help to escape local minima.

The idea is to simulate the physical process of annealing, where an object is cooled very slowly to
enhance physical properties.

The simulation starts with a very high temperature $T_"max"$ and every $n_T$ steps the temperature
is reduced: $T <- T/alpha$, so that as the system cools down it settles into a low-energy state
which is hopefully the global minimum.
This method however depends heavily on the cooling schedule which must be chosen empirically.

Another option is to treat temperature as another variable in the system which can change based on a
random walk: $W(x, beta -> x, beta')$.

We can further refine this model by running $N$ replicas of the system in parallel, each one at a
fixed temperature $T_n$. Each replica evolves independently using the standard MH algorithm but
periodically after $M$ steps we swap the entire configuration of two replicas with adjacent
temperature.

=== Example: Edward-Anderson model

This is a model similar to the Ising model, however in this case the interactions between neighbours
are random:
$
  J_(i j) tilde N(0, J) wide E(S) = - sum_((i, j) "neighbours") J_(i j) S_i S_j
$
this leads to a phenomena called "frustration" where the system cannot find a configuration which
satisfies all interactions simultaneously which in turns leads to a very rugged energy landscape.

To measure "order" we can no longer use magnetization, therefore we use the overlap between states:
$
  q_(alpha beta) = 1/N sum_i S_i^alpha S_i^beta
$
where $S_i^alpha$ and $S_i^beta$ are the spins of $i$ in replica $alpha$ and $beta$ respectively.

= Differential equations

== Ordinary Differential Equations (ODEs)

We will learn how to approximate a system of ODEs:
$
  (dif u) / (dif t) = F(u(t), t)
$
(recall that higher order ODEs can be rewritten as a first order system of ODEs, see analysis 3).
Recall that if $F(u, t) = alpha(t) u + beta(t)$ we say that the ODE is linear and can be solved
analytically, while id $F(u, t)$ is independent of $t$ we say that the ODE is autonomous.
If $F$ is $L$-Lipschitz there exists an unique $u(t)$ which solves the initial value problem.

TODO: there was some other stuff about fixed points, stability, chaos etc.

The idea is to discretize time, in this case a constant one: $t_n = n k$, $k$ is fixed.
Assume we have already computed a sequence of values $v_n tilde u(t_n)$, then we can find our
approximate derivative as $f_n := F(v_n, t_n)$.

A *linear $s$-step method* will compute $v_(n + s)$ as a function of $v_(n+j)$ and $f_(n+j)$ for
$j = 0, ..., s-1$.

=== Euler method

This is the simplest and older method:
$
  v_(n + 1) = v_n + k f_n
$

This is an example of a one-step method ($s = 1$) which is also *explicit*: we compute the new value
from past values of $v$ and $f$.

We can also find some variations of Euler's method:
/ Backwards Euler method: This is an *implicit* method.
  $
    v_(n + 1) = v_n + k f_(n + 1) \
    ==> v_(n + 1) - k (dif u)/(dif t) (t_(n+1)) = v_n
  $
  To solve the non-linear equation which arises we use some numerical method (like Newton-Raphson).

/ Trapezoid rule: This is also an *implicit* method.
  $
    v_(n + 1) = v_n + k/2 (f_n + f_(n+1))
  $
  This method considers the average between the current and the next slope. This is the most
  accurate of the three but still involves using a numerical method to compute $f_(n + 1)$

=== More steps

The *midpoint rule* is a two-step explicit method:
$
  v_(n + 1) = v_(n - 1) + 2 k f_n
$
Since we need more than one step in the past we need either multiple initial conditions or we need
to use a one-step method to compute $v_1$.

There are many other methods, usually of 4th order, named after Adams, which take some kind of
weighted sum over past derivatives to find the right slope. Some are also implicit.

The most *general $s$-step linear formula* can be written as
$
  sum^s_(j = 0) alpha_j v_(n + j) = k sum^s_(j = 0) beta_j f_(n + j)
$
where we can assume wlog that $alpha_s = 1$.
If $beta_s = 0$ we have an explicit formula, while if $beta_s != 0$ we have an implicit one.

#example[
  For Euler method we have
  $ cases(s &= 1, alpha_1 &= 1, alpha_0 &= -1, beta_0 &= 1, beta_1 & = 0) $
]

We also introduce two *characteristic polynomial*
$
    rho (z) & = sum^s_(j = 0) alpha_j z^j \
  sigma (z) & = sum^s_(j = 0) beta_j z^j
$
and a *time-shift operator*:
$
   Z v_n & = v_(n + 1) \
  Z u(t) & = u(t + k)
$

Then, using this notation we can rewrite the multi-step formula as
$
  rho(Z) v_n - k sigma (Z) f_n = 0
$<eq:general-multi-step>

We also introduce the *local discretization error*.
We start by defining the local discretization operator:
$
  cal(L) := rho(Z) - k cal(D) sigma(Z) wide cases(
    delim: #none, "where" cal(D) "is the time",
    "differentiation operator"
  )
$
Then, the local discretization error is
$
  cal(L) u(t_n) = rho(Z) u(t_n) - k sigma(Z) (dif u (t_n))/(dif t)
$

The idea is then to Taylor expand over $k$: we want that $cal(L) u(t_n) = O(k^(p+1))$ with $p$ as
big as possible, i.e. $C_0 = ... = C_p = 0$ and $C_(p + 1) != 0$, where $C_n$ are the coefficients
of the Taylor expansion, which can be computed as
$
  C_m = sum^s_(j = 0) j^m / m! alpha_j - sum^s_(j = 0) j^(m - 1) / (m - 1)! beta_j
$

For one-step methods we can compute that Euler method has an accuracy $p = 1$, while for the
trapezoid rule we have $p = 2$, which we can prove to be the best possible result for $s = 1$.

To achieve an accuracy (or order) of $p$ we need to satisfy $p + 1$ equations ($C_j = 0$ for
$j = 0, ..., p$). An $s$-steps method has $2s$ parameters if explicit and $2s + 1$ if implicit,
therefore, _in theory_, we can achieve an order of $p = 2s - 1$ or $p = 2s$ for explicit and
implicit methods respectively.

However, some resulting formulas can be unstable! It is possible to prove that the maximum accuracy
we can achieve while still preserving stability is $p = min(2s, s + 2)$ for implicit formulas, while
$p = s$ for explicit formulas. This means that, when $s$ is large enough, we have the freedom to
choose some parameters arbitrarily.

The family of Adams formulas always have $alpha_s = 1, alpha_(s - 1) = -1$ and $alpha_j = 0$ for all
$j = 0, ..., s - 2$:
$
  v_(n + s) = v_(n + s - 1) + k sum^k_(j = 0) beta_j f_(n + j)
$
This basically is a generalization of the Euler method where we take a weighted sum over the past
slopes.

See the lecture notes for a table of coefficients of this family of formulas.

=== Stability

There are two main way to compute stability:
- *Stability*: Fix $t > 0$ and let $k -> 0$. Does $v_n$ stay bounded?
- *Eigenvalue stability*: Fix $k > 0$ and let $t -> oo$. Does $v_n$ stay bounded?

As $k -> 0$ we get that @eq:general-multi-step reduces to
$
  rho (Z) v_n = sum^s_(j = 0) alpha_j v_(n + j) = 0
$
this means that we have a stable formula if all the equations are bounded as $n -> oo$.

We get that if $z^n$ is a root of $rho(z)$, then $v_n = z^n$ is a solution for the above equation,
while if $z$ has multiplicity $m > 1$, then $v_n in {n z^n, ..., n^(m - 1) z^n}$ is also a solution.
$
  sum^s_(j = 0) alpha_j z^(n + j) = z^n sum^s_(j = 0) alpha_j z^j = 0
$

#proposition[
  A linear multi-step formula is stable if and only if all the roots of $rho(z)$ satisfy
  $abs(z) <= 1$ and if $abs(z) = 1$ then $z$ is a simple root (multiplicity of 1).
]

This is due to the above reasoning: indeed it is easy to see that if the root is larger than $1$ in
absolute value, as $n -> oo$ the term diverges to infinity.

#theorem(title: [Dahlquist stability frontier])[
  The order of accuracy $p$ of a stable linear multi-step formula satisfies
  $
    p <= cases(
      s + 2 wide & "if" s "is even",
      s + 1 wide & "if" s "is odd",
      s wide & "if the formula is explicit"
    )
  $
]

==== Stability regions

Now we look into *stability regions*, that is the set of values of $k$ where the formula is stable.
To find it we want to write $z$ as a function of $k$, and check when $abs(z) < 1$ (note that we
might want $k in CC$).

TODO: how to compute stability regions when $dv(u, t) = a u$ for a constant $a$.

See the lecture notes to see the stability regions of some of the most common methods, note that, in
general, implicit methods have a larger stability region compared to explicit ones.

==== Eigenvalue stability

This idea generalizes even in more complex ODEs:
1. Start with
  $
    dv(u, t) = F(u, t)
  $
2. Linearize around a particular solution $u^*$
  $
    dv(u, t) = M(t) u
  $
  where $M$ is the Jacobian matrix
  $
    M_(i j) (t) = pdv(F_i, u_j) (u^*, t)
  $
3. Freeze $M(t) = M^*$.
4. Diagonalize $M^*$.
5. All eigenvalues $lambda$ of $M^*$ should be such that $k lambda$ is inside the stability region.

We say that a formula is $A(alpha)$ stable if for the angle $alpha in (0, pi/2)$ the stability
region includes the infinite sector of the complex plane
${rho e^(i theta) | theta in (-alpha, -alpha - pi/2)}$.
We say that a formula is $A(0)$-stable if there exists some $alpha > 0$ such that it is
$A(alpha)$-stable.

=== Runge Kutta

This is another family of linear multi-step formulas which take into account multiple evaluations of
the function $u$ per step. They use a high order Taylor expansion to compute the estimate.

==== Adaptive methods

The idea is to start with a high $k$ and estimate the error: when the error is above or below a
certain threshold we scale $k$ to make the algorithm either faster or more accurate.

A popular way to estimate the error is to run the algorithm twice, in parallel. One copy will be
running at $k$ and one at $k/2$ and check for the difference between the two. Another option is to
run RK4 along with RK5.

== Stochastic Differential Equations (SDEs)

This is a way to incorporate the knowledge of noise within differential equations.
$
  dd(X_t) = mu (X_t, t) dd(t) + sigma (X_t, t) dd(B_t)
$
where $B_t$ is the standard Brownian motion.
This can also be written as
$
  dv(X, t) = mu (X, t) + sigma (X, t) eta (t)
$
where $eta$ is white noise.

We now want to find a way to simulate this Brownian motion. The answer is, as expected, to
discretize time:
$
  X_(n + 1) = X_n + sigma sqrt(dd(t)) z_n wide "with" z_n tilde N(0, 1)
$
where $dd(t)$ is a discrete time step (in the previous section we used $k$ for this).
We can easily show that $X_(n)$ defined as above is distributed as $N(0, sigma^2, t_n)$.

Of course, we no longer have a notion of accuracy, since there is no "true" path to follow.

The "standard" Brownian motion, defined in @sec:brownian-motion, has several variances to it: the
"standard" one has $mu (x, t) = 0$ and $sigma (x, t) = sigma^2$, however these could actually be
arbitrary functions of $x$ and $t$, in particular if $sigma(x, t)$ is independent of $x$ we say that
the noise is *additive*, if it depends on $x$ it is *multiplicative*.

We can simulate these processes with methods like Euler-Maruyama
$
  X_(n + 1) = X_n + mu (X_n, t_n) dd(t) + sigma (X_n, t_n) sqrt(dd(t)) z_n wide "with" z_n tilde N(0, 1)
$
note that higher order methods (like stochastic RK) also exist.

#theorem(title: [Fokker-Plank equation])[
  $
    pdv(P(x, t), t) = - pdv(, x) (mu (x, t) P(x, t)) + 1/2 pdv(, x, 2) (sigma^2 (x, t) P(x, t))
  $
  This is also known as Kolmogorov forwards equation.
]

This equation describes the evolution of the probability over time.

#proof[
  No fucking way, look at the slides, part 9.
]

There is also the backwards equation but I don think it really matters.

We define the probability flux $J$ as the difference between the probability of going through $x$
from below and from below at time $t$ per unit time.
$
  pdv(P(x, t), t) = - pdv(J (x, t), x)
$
