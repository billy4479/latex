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
    P(X_0, ..., X_n) = P(X_0 = x_0) product^(n-1)_(i = 0) P(X_(i+1) = x_(i+1) | X_i = x_i, ...,
      X_0 = x_0)
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
    P(X_(t+1) = x_(t+1) | X_t = x_t, ..., X_0 = x_0) = P(X_(t+1) = x_(t+1) | X_t = x_t)
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
  P_(i j) = P(X_(t+1) = j | X_t = i) wide i, j in cal(X)
$
Note tat we can construct a *transition matrix* $P$ of all the combinations of transitional
probabilities in $cal(X)$.

A common problem is to compute the probability that a certain event $j$ occurs after $n$ steps:
$
  P^n_(i j) = P(X_(t+n) = j | X_t = i)
$

#proposition(title: "Chapman-Kolmogorov equations")[
  The $n$-step transition probability satisfy
  $
    P^(n+m)_(i j) = sum_(k in cal(X)) P_(i k)^n P_(k j)^m wide i, j in cal(X); n, m >= 0
  $
]
#proof[
  We have
  $
    P_(i j)^(n + m) & = P(X_(n+m) = j | X_0 = i) \
    & = sum_(k in cal(X)) P(X_(n+m) | X_n = k, X_0 = i) P(X_n = k | X_0 = i) \
    & = sum_(k in cal(X)) P(X_(n+m) = j | X_n = k) P(X_n = k | X_0 = i) \
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
  alpha_i^((t)) = P(X_t = i)
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
  f_i & = P(X_t = i "for some" t>=1 | X_0 = i) \
      & = P(union.big_(t >= 1) {X_t = i} | X_0 = i)
$
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

TODO: start from lemma 2, page 13
