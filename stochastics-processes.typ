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

== Discrete-time Markov chains

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
    p & "if" x_{t+1} = x_t + 1,
    1-p & "if" x_{t+1} = x_t - 1,
    0 & "otherwise",
  )
$
