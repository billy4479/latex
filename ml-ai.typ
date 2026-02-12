#import "lib/template.typ": *
#import "lib/theorem.typ": *
#import "lib/utils.typ": *

#show: template.with(
  titleString: "Machine Learning &\nArtficial Intelligence",
  author: "Giacomo Ellero",
  date: "A.Y. 2025/2026",
)

#show: thm-init

= Supervised learning

Let the training set be
$
  S = ((x^mu, y^mu))_(mu in [m]) wide cases(
    delim: #none, "where" x in cal(X)\, y in cal(Y),
    "and" m in NN "is the number of samples"
  )
$
Usually $cal(X) in RR^N$ is the input set, while $cal(Y)$ is the label set which could be ${-1, 1}$,
some categories e.g. ${"cat", "dog", "human", ...}$ (we assign a number to each label in this case,
usually using a one-hot encoded vector).

== Probabilistic approach

Assume that $(X^mu, Y^mu)$ are random variables, but in this case $mu = 1, ...$ is infinite, however
we have only observed a finite number of realizations of these variables (e.g. $1$ to $m$). Then we
are given the $m + 1$ realization but just for $X^(m + 1)$ and we want to describe the probability
distribution of $Y^(m + 1)$.
$
  prob(Y^(m + 1) = y | (X^mu, Y^mu) = (x^mu, y^mu) "for" mu in [m], X^(m + 1) = x) = med ?
$
for brevity we will write $prob(y | S, x)$.

=== Classical ML Theory

This is a *frequentist* approach: we assume that samples are i.i.d. and that there exists a true
distribution $cal(D)$. This means that $S tilde D^m$.
$
    cal(D)_x (x) & = sum_(y in cal(Y)) cal(D) (x, y) wide &    "marginal" \
  cal(D) (y | x) & = (cal(D)(x, y)) / (cal(D)_x (x)) wide & "conditional"
$

This means that $prob(y | S, x) = cal(D) (y | x)$.

We also add a deterministic assumption: $exists f: cal(X) -> cal(Y)$ such that
$cal(D) (y | x) = bb(1)_(y = f(x))$, implying $f(x) = argmax_y cal(D)(y | x)$.

Given a candidate $h: cal(X) -> cal(Y)$ we measure the error as
$
  R_(cal(D))(h) = prob_(cal(D)_x) (h(x) != f(x)) = EE_(cal(D)_x) [bb(1)_(h(x) != f(x))]
$
This is called the *true risk*, but it is unknowable. We focus on the *empirical risk* instead.
$
  R_S (h) = 1/m sum_(mu in [m]) bb(1)_(h(x^mu) = y^mu)
$

We want to minimize the empirical risk, we want to find an algorithm
$
  "ERM": (cal(X) times cal(Y))^m -> cal(Y)^cal(X)
$
where $cal(Y)^cal(X)$ is the set of functions from $cal(X)$ to $cal(Y)$.
We want that
$
  "ERM"(S) in argmin_h R_S (h) = h_S
$
(if there are multiple minima we just pick one).

However considering the whole $cal(Y)^cal(X)$ can be misleading, since then we can easily construct
a function which classifies correctly just the training sample (but nothing else) which will have
$R_S = 0$. To avoid this problem we consider a different $cal(H) subset cal(Y)^cal(X)$ and we look
for minimizers of $"ERM"$ just within $cal(H)$.

=== PAC-bounds

We want that, $forall epsilon, delta in (0, 1)$
$
  prob_(cal(D)^m) ["error measure" <= epsilon] >= 1 - delta
$

We say that an hypothesis space $cal(H)$ is PAC-learnable if
$
  & exists cal(A): (cal(X) times cal(Y))^m -> cal(H), \
  & exists m_(cal(H)): (0, 1)^2 -> NN \
  "s.t." & \
  & forall (epsilon\, delta) in (0\, 1)^2 \
  & forall cal(D)_x \
  & forall f "realizable in" cal(H) \
  ==>&
  m >= m_cal(H) (epsilon, delta) => prob_(cal(D)^m) [R_(cal(D)) (cal(A)(S)) <= epsilon] >= 1-delta
$
where $m_cal(H)$ is a function that, given the required $epsilon$ and $delta$ gives us the desired
number of samples.

This is very powerful in theory, however the realizability assumption usually does not hold,
realizability means that
$
  exists h^* in cal(H) wide "s.t." R_(cal(D))(h^*) = 0
$

#theorem[
  Every finite hypothesis class $cal(H)$ is PAC-learnable, with $cal(A) = "ERM"_cal(H)$ and
  $
    m_(cal(H))(epsilon, delta) = ceil((log(abs(cal(H))/delta))/epsilon)
  $
]

#proof[
  We will work on the equivalent expression
  $
    prob_(cal(D)^m) [R_(cal(D)) (h_S)) > epsilon] <= delta
  $
  and set a series of upper bounds until we reach $abs(cal(H)) e^(-m epsilon)$ and then we impose
  $<= delta$ so that we get the result.

  Let us define the set of "bad" hypothesis and the set of misleading training set:
  $
    cal(H)_B & = {h in cal(H) | R_(cal(D)) (h) > epsilon} \
           M & = {S | exists h in cal(H)_B, R_S (h) = 0} \
             & = union.big_(h in cal(H)) {S | R_S (h) = 0}
  $
  We obtain that $h_S in cal(H)_B => S in M$. Then
  $
    prob_(cal(D)^m) [R_(cal(D)) (h_S)) > epsilon] & = prob_(cal(D)^m) [h_S in cal(H)_B] \
    & <= prob_(cal(D)^m) [S in M] \
    & = prob_(cal(D)^m) [union.big_(h in cal(H)) {S | R_S (h) = 0}] \
    & <= sum_(h in cal(H)_B) prob_(cal(D)^m) [R_S (h) = 0] \
    & = sum_(h in cal(H)_B) product^m_(mu = 1) prob_(cal(D)^m) [h(x^mu) = f(x^mu)] \
    & = sum_(h in cal(H)_B) (prob_(cal(D)^m) [h(x^mu) = f(x^mu)])^m \
    & < sum_(h in cal(H)_B) (1 - epsilon)^m \
    & <= abs(cal(H)) (1 - epsilon)^m \
    & <= abs(cal(H)) e^(-m epsilon)
  $
]

#theorem[
  An hypothesis class $cal(H)$ is PAC-learnable if and only if its $"VCdim"(cal(H)) = d$ is finite, with
  $cal(A) = "ERM"_cal(H)$ and
  $
    m_(cal(H))(epsilon, delta) = ceil((log 1/delta + d log 1/epsilon)/epsilon)
  $
]

