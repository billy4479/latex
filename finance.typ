#import "lib/template.typ": template
#import "lib/utils.typ": *
#import "lib/theorem.typ": *

#show: template.with(
  titleString: "Mathematical Modelling for Finance",
  author: "Giacomo Ellero",
  date: "A.Y. 2025/2026",
)

#show: thm-init

= One-period models

== Describing one-period markets

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
$<eq:cashflow-matrix>
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

=== Law of one price
This is a weak requirement to make sure that markets work as intended.
We start with some definitions.

#definition(title: "Spaces of payoffs and cashflows")[
  Let the *space of traded payoffs* be
  $
    A = {z in RR^k | z = cal(A) theta, theta in RR^(k+1)}
  $
  and the *space of traded cashflows* be
  $
    M = {x in RR^(k+1) | x = cal(M) theta, theta in RR^(k+1)}
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
  If $"rank"(cal(A)) = k$ then LOP holds. This makes sure that there are no redundant securities
  whose payoff can be obtained by a linear combination of the others.
  $
    cal(A) (theta' - theta'') = 0
  $
]

#proposition[
  LOP holds iff
  $
    cal(A) theta = 0 ==> V_theta (0) = 0
  $
]

These tell us that if we want to get a zero payoff it will cost us zero.

==== Linear Pricing Functional (LPF)

#definition(title: "Linear Pricing Functional (LPF)")[
  The Linear Pricing Functional is a correspondence $pi: A -> RR$
  $
    pi (z) = { V_theta (0) | cal(A) theta = z}
  $
  such that
  1. $pi(z)$ is single-valued (i.e. is a function)
  2. $pi(z)$ is linear
]

Given a payoff $z in A$, the LPF gives us the price at $t = 0$ of the portfolio that generates that
payoff.

#proposition[
  LOP holds $<==> exists$ an LPF.
]

#proof[
  / LPF implies LOP: Trivial, since the LPF is single-valued we have that $pi(0) = 0$ which gives us
    the LOP by the previous proposition.

  / LOP implies LPF: Consider $theta'$ and $theta''$ such that $cal(A) theta' = cal(A) theta''$
    then, by LOP,
    $
      V_theta' (0) = V_theta'' (0) ==> pi(cal(A) theta') = pi (cal(A) theta'') ==> V_theta' (0) =
      V_theta'' (0)
    $
    which tells us that $pi$ is single-valued. Linearity can be also be proven with some algebra,
    see Proposition 15 in lecture notes.
]

==== Stochastic Discount Factor (SDF)

#definition(title: "Stochastic Discount Factor (SDF)")[
  The SDF is a random vector $m$ such that
  $
    S_j (0) & = EE[m S_j (1)] wide forall j in {1, ..., N} \
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
    pi(z) & = EE[m z]           & wide & z in A \
          & = EE[m A theta]     & wide & "for some" theta \
          & = EE[m V_theta (1)] \
          & = V_theta (0)
  $
  which is our LPF since the expectation is linear.
]

#theorem(title: "Equivalent characterizations of LOP")[
  The following states are equivalent:
  1. LOP holds;
  2. $exists$ an LPF $pi$;
  3. $exists$ an SDF $m$;
]

#proof[
  / 1. $==>$ 3.: Consider $A$ and define an inner product on it as
    $angle(z', z'') = EE[z' z'']$, so that we have an Hilbert space.
    We want to show that $pi(z) = E[m z]$.
    Define $A_0 = { z in A | pi(z) = 0}$ (i.e. the kernel of $A$) and
    $A_0^perp = {y in A | EE[y z] = 0 "for all" z in A_0}$ (being the orthogonal space to the
    kernel).
    Then we can decompose $A = A_0 plus.o A_0^perp$.

    Take any $y in A_0^perp$ such that $y != 0$, which in turns implies that $pi(y) = 0$.
    Set $w = y/(pi(y))$ so that $pi(w) = 1$.
    Then, take any $z in A without A_0$ and write it as
    $
      z = pi(z) w + underbrace((z - pi(z) w), pi(dot) = 0 med ==> med in A_0)
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

#remark[
  - Under the LOP, $m$ can be both positive and negative;
  - The $m$ we have constructed is such that $m in A$.
]

#proposition(title: "The SDF is unique")[
  Under the LOP, $exists! med m in A$ which we will call $m^*$.
]

#proof[
  Suppose there exists $m', m'' in A$ both SDFs.
  Then
  $
    EE[m'(m'' - m')] = EE[m''(m'' - m')]
  $
  This is because $(m'' - m') in A$ (by linearity of $A$). But both $m'$ and $m''$ are SDFs so they
  correctly price every element of $A$ and, under the LOP, these are equal.
  $
    ==> EE[(m' - m'')^2] = 0 ==> m' = m''
  $
]

Consider $m = m^* + epsilon$ with $epsilon in A^perp$ (this means that $m in.not A$, i.e. it cannot
be bought). This $m$ is still an SDF since
$
  EE[(m^* + epsilon) x] = EE[m^* x] + underbrace(EE[epsilon x], = 0)
$

==== State-Price Vectors (SPV)

#definition(title: "State-Price Vectors (SPV)")[
  A vector $psi in RR^K_(++)$ such that
  $
    S_j (0) = sum^K_(k = 1) psi (omega_k) S_j (1) (omega_k)
    quad
    "and"
    quad
    sum^K_(k = 1) psi (omega_k) = 1/(1+r)
  $
  where
  $
    psi = vec(psi(omega_1), psi(omega_2), dots.v, psi(omega_K))
  $
]

Note that we can easily obtain a positive SDF from $psi$:
$
  m(omega_k) = psi(omega_k) / (cal(P)(omega_k))
$

We can interpret it as "$psi_k$ is the right amount of money to get tomorrow if $omega_k$ happens".
This is some kind of insurance: "how much should I spend to ensure against $omega_k$".

#definition(title: "Risk-Neutral Probabilities (RNP)")[
  A RNP is a probability measure $cal(Q)$ such that $cal(Q)(omega_k) = q_k > 0$ for all $k in K$ and
  $sum^K_(k=1) q_k = 1$. Moreover
  $
    S_j(0) & = EE^(cal(Q)) [(S_j (i))/(1 + r)] \
           & = sum^K_(k = 1) (q_k S_j (1) (w_k))/(1+r)
  $
  or equivalently
  $
    EE^cal(Q) [(S_j (1) - S_j (0))/(S_j(0))] = r
  $<eq:exp-rnp>
]

In @eq:exp-rnp, the argument of the expectation is the "return per unit invested" and this equation
basically tells us that the expected gain is $r$, as in the risk-free security.

Note that this $cal(Q)$ is a way for us to model that all investors are risk neutral. Of course
investors are _not_ risk neutral, however, this will come in handy later.

To summarize, we have:
- $
    m(omega_k) = (psi(omega_k))/cal(P)(omega_k)
  $
- $
    psi(omega_k) = (cal(Q)(omega_k))/(1+r)
  $
- $
    m(omega_k) = 1/(1+r) (cal(Q)(omega_k))/(cal(P)(omega_k))
  $

=== Fundamental Theorem of Finance

==== First Fundamental Theorem of Finance

#definition(title: "Arbitrage strategy")[
  This is a strategy $theta$ such that:
  1. $V_theta (0) <= 0$
  2. $V_theta (1) (omega_k) >= 0 wide forall k$
  3. At least one of $V_theta (0) > 0$ or $exists overline(k) "s.t." V_theta (1) (omega_overline(k)) > 0$
]

This basically means that there are ways to trick the market to make money out of nothing, either by
shorting it or by having some magic "free" lottery ticket.

#theorem(title: "(First) Fundamental Theorem of Finance")[
  The following statements are equivalent:
  1. No-Arbitrage conditions
  2. $exists$ SPVs
  3. $exists$ RNPs
  4. $exists$ strictly positive SDFs.
]

#proof[
  #show "NA": [No-Arbitrage]

  The equivalence of 2, 3, and 4 is trivial, we can easily show it from what we saw in the previous
  section.

  We will show that no-arbitrage is equivalent to the existence of SPVs.

  / 2. $==>$ 1.: By the existence of an SPV we have that $forall theta$
    $
      V_theta (0) = sum^K_(k = 1) psi (omega_k) V_theta (1) (omega_k)
    $
    Then, to have an arbitrage opportunity we need to have that $V_theta (0) <= 0$, but all the
    terms in the sum are either $> 0$ (like $psi$) or $>= 0$ (like $V_theta (1)$) and we have ruled
    out arbitrage condition 3.1.
    Similarly, for condition 3.2, we would need at least one $omega_k$ such that
    $V_theta (1)(omega_k) > 0$, but then the sum would be stricly positive.

  / 1. $==>$ 2.:
    Now we assume NA holds.
    Recall the definition of cashflow matrix (@eq:cashflow-matrix):
    $
      vec(delim: "[", -S(0), A) theta = vec(delim: "[", -V_theta (0), V_theta (1))
    $
    We see that we have an arbitrage condition if and only if
    $
      exists theta : M theta > 0
    $

    Let $cal(M)$ be the linear space generated by the columns of $M$, i.e.
    $
      cal(M) = { x in RR^(K+1) | x = M theta, theta in RR^(N+1)}
    $
    Then, NA holds if and only if
    $
      cal(M) inter RR^(K + 1)_+ = {0}
    $

    Consider the unit simplex:
    $
      Delta = { y in RR^(K + 1) mid(|) sum_(i in 0)^K y_i = 1 }
    $

    We notice that $cal(M) inter Delta = nothing$, which implies that there exists a
    separating hyperplane:
    $
      exists F: RR^{K+1} -> RR "linear" wide "s.t." F(x) < F(y) med forall x in cal(M), forall y in Delta
    $

    #figure(
      image("./assets/finance/unit-simplex.png", width: 25%),
      caption: "Unit simplex.",
    )

    We claim that $F(x) = 0$ $forall x in cal(M)$. If not, then $exists overline(x) in cal(M)$ such
    that $F(overline(x)) > 0$ (wlog) and since $F$ is linear
    $F(lambda overline(x)) = lambda F(overline(x)) > 0$ $forall lambda > 0$. However $F$ is
    continuous which means that on $Delta$ (which is closed) attains a maximum. This means that
    there exists $overline(lambda)$ such that
    $
      F(overline(lambda), overline(x)) > max_(y in Delta) F(y)
    $
    but this contradicts the fact that $F$ is a separating hyperplane.

    Then, we have
    $
      F(x) = 0 <==> phi_0 x_0 + sum^K_(k = 1) phi_k x(omega_k) = 0
    $
    $forall x in cal(M)$ where $phi$ is a basis of our choice to represent $F$.

    But $x in cal(M)$ if
    $
      exists theta : x = M theta = vec(
        -V_theta (0), V_theta (1) (omega_1), dots.v, V_theta (1) (omega_K)
      )
    $
    which means we can rewrite as
    $
      -phi_0 V_theta (0) + sum_k phi_k V_theta (1) (omega_k) = 0
    $
    for all $theta in R^(N+1)$ and with $phi_j > 0$.

    Therefore we have
    $
      V_theta (0) = sum^K_(k = 1) phi_k / phi_0 V_theta (1) (omega_k)
    $
    and we can set
    $
      psi(omega_k) = phi_k / phi_0
    $
    and we conclude the proof.
]

==== Complete Markets

#definition(title: [Hedging])[
  $x in RR$ can be perfectly hedged if $exists theta$ such that $V_theta (1) = A theta = x$.
]

The interpretation of $x$ is some kind of risk. I am hedged if there is some way I can invest the
money today such that tomorrow I will be able to cover $X$.

Of course $x$ is a random variable: it depends on $omega$. We call it a *contingent claim*
$
  X = vec(x(omega_1), dots.v, x(omega_K))
$

#definition(title: [Complete Market])[
  $
    forall X in RR^K med exists theta in RR^(N + 1) quad "s.t." A theta = X
  $
]

This means that every contingent claim can be hedged. Note that this is constrained by the amount of
money we can invest, since covering all possible risks is likely very expensive.

#proposition(title: [Characterization of Completeness])[
  A market is complete if and only if the columns of $A$ generate $RR^K$, i.e.
  $
    "rank"(A) = K <==> "the market is complete"
  $
]

#remark[
  1. LOP + Completeness $<==> "rank"(A) = K = "rank"(M)$ since we have a LPF
  2. NA + Completeness $==> "rank"(A) = "rank"(M) = K$
  3. LOP + Completeness $<==> exists ! m$ SDF
]<rmk:completeness-impl>
#proof[
  1. We have
    $
      sum_k pi(omega_k) S_j (1) (omega_k) - S_j (0) = 0
    $
    but then
    $
      M = vec(delim: "[", S(0), A)
    $
    which means that the first row is linearly dependent from the others and we get $"rank"(M) = K$.

  2. This comes from the fact that NA $==>$ LOP.

  3. We know that all the SDFs can be written as
    $
      m + m^* + epsilon, quad epsilon in A^perp
    $
    but then if $A$ generates $RR^K$ we get that $A^perp = {0}$ and we have an unique $m$.
]

==== Second Fundamental Theorem of Finance

#theorem(title: [Second Fundamental Theorem of Finance])[
  The following statements are equivalent:
  1. No-Arbitrage + Completeness
  2. $exists !$ SPV
  2. $exists !$ RNP
  2. $exists !$ strictly positive SDF
]

#lemma[
  Let $Psi$ be the set of SPVs.
  If $Psi != nothing$ then
  $
    cal(M)^perp = "span"{vec(1, psi), psi in Psi}
  $
]
#proof[
  To show that $cal(M)^perp supset.eq "span"{vec(1, psi), psi in Psi}$
  we use the definition of SPV (TODO) to get that
  $
    mat(1, psi^T) = cal(M) = (0, ..., 0)
  $

  To show that $cal(M)^perp subset.eq "span"{vec(1, psi), psi in Psi}$ we take any
  $phi in cal(M)^perp$ such that
  $
    phi(alpha) = alpha phi + vec(1, psi)
  $
  for some $psi in Psi$ and some vector $alpha$.
  Then, there exists $overline(alpha) > 0$ such that $phi(overline(alpha)) >> 0$.
  (The notation $>>$ means that all components are strictly greater). But then we can write
  $
    phi & = 1/overline(alpha) phi(overline(alpha)) - 1/overline(alpha) vec(1, psi) \
    & = (phi_0(overline(alpha)))/overline(alpha) 1/(phi_0(overline(alpha))) phi(overline(alpha)) - 1/overline(alpha) vec(1, psi) \
  $
  TODO: huh? complete here
]

With this lemma we can now prove the second fundamental theorem of finance:
#proof[
  / 1. $==>$ 2.: We can use @rmk:completeness-impl to compute that $dim(cal(M)^perp) = 1$, then this
    means that (by the lemma above) for any $psi, psi' in Psi$ and $alpha in RR$ we have
    $
      vec(1, psi) = alpha vec(1, psi')
    $
    but (TODO: why??) $alpha$ must be equal to $1$, which means that $psi = psi'$.
  / 2. $==>$ 1.: There exists an unique SPV, then $"rank"(cal(M)) = K = dim(A)$.
  TODO: what?
]

== Mean-Variance Theory

We are still in the context of one-period models, where $t in {0, 1}$, and assume that we have $N$
securities, _all risky_.

We use a slightly different notation: $S_j$ is the price at time $0$ of asset $j$, while $x_j$ is
its payoff at time $1$.
We have that $x_j in cal(L)^2 (Omega, F, cal(P))$, where $cal(L)^2$ is the space of distributions
with finite variance, are the values which $S_j (1)$ can take.

Then we define the *gross return rate* as
$
  R_j = x_j / S_j
$

Also recall the definition of the variance-covariance matrix:
$
  Sigma_(i j) = "cov"(R_i, R_j)
$
we will assume that the matrix is non-singular, i.e. $abs(Sigma) != 0$, therefore it is invertible.
This constraint tells us that it is not possible to create a strategy with no risk.

Define the *portfolio weights* as $(w_j)_(j in {1, ..., N})$ and we require that $sum_j w_j = 1$,
these should be interpreted as the fraction of my wealth which is invested in each asset.
Note that eventually I need to spend all of my money, therefore if I want to short sell something I
want to spend all the money that I earn at $t = 0$ from short selling, therefore we are ruling out a
complete short-sell position.

Fix a certain average return we desire (e.g. $10%$) and call it $overline(E)$, we assume we don't
like risk, therefore I like investments with a lower variance.
Therefore we end up with a quadratic minimization problem:
$
  min_w w^T Sigma w wide "s.t." w^T dot E = overline(E)
$<eq:mv-min>
where $E$ is the vector of the expectations $E_j = EE[R_j]$. We assume that $Sigma$ is known.
Eventually we will want to find the optimal portfolio for each possible $overline(E)$.

=== Hansen-Richard

#let rstar = $R^*$
#let restar = $R^e^*$
#let rmv = $R^"MV"$

This is an approach to solve @eq:mv-min.

If $abs(Sigma) != 0$ then $x_1, ..., x_N$ are linearly independent, which in turns means that LOP
hold.
Since LOP holds $exists$ LPF and $exists$ SDF.

Note also that the second-moment matrix (or Gram matrix) $E[x x^T]$, where
$E[x x^T]_(i j) = EE[x_i x_j]$, is also non singular.

As we know, the SDF $m^* = theta^* dot x in A$, which means that $theta^*$ is a valid strategy.
We want to find this $theta^*$ from
$
  EE[(theta^* x) x_j] = S_j, wide j in 1, ..., N
$
or equivalently
$
                 & EE[(theta^*)^T (x x^T)] \
               = & (theta^*)^T EE[x x^T] = S^T \
  <==> theta^* = & EE^(-1)[x x^T] S \
      <==> m^* = & S^T EE^(-1)[x x^T] x
$
where we know that we can invert $EE[x x^T]$ since it is non-singular.
$S$ is the vector of all the prices $S = [S_1 (0), ..., S_N (0)]^T$.

==== Definitions

Let us define two subsets of the space of payoffs $A = "span"(x_1, ..., x_N)$.
#definition(title: [$A_1$ and $A_0$])[
  Define the space of returns $A_1$ and the space of excess returns $A_0$ as
  $
    A_1 & = {R in A | pi(R) = 1} \
    A_0 & = {R^e in A | pi(R) = 0}
  $
]

The interpretation we can give to each one of these sets is the following:
/ Space of returns: $A_1$ is the space where the gross return lie. Indeed, every gross return is
  defined as the ratio between its payoff $y$ and its initial price $pi(y)$. Then
  $
    pi(y/pi(y)) = 1/pi(y) pi(y) = 1
  $
  which tells us that all the elements of $A_1$ can be written as a gross return for some $y in A$.

  $A_1$ is affine.

/ Space of excess returns: $A_0$ is the set of traded payoffs with zero initial price. Since we know
  that $S_k (0) != 0$ for all $k$ we get that $A_0 subset.neq A$.

  $A_0$ is linear.

  Each element of $R^e in A_0$ is an excess returns: $exists R, R' in A_1$ such that
  $R^e = R - R' in A_0$. This is due to the fact that, since all $w$ sum up to 1, the difference
  between any of them is zero, then $A_0$ is the space of returns of the differences of $w$.

We now define two special elements of these two sets.

#definition(title: [#rstar and #restar])[
  Define $rstar$ and $restar$ as follows
  $
     rstar & = m^* /pi(m^*) in A_1 \
    restar & = "proj"[1 | A_0] in A_0
  $
]

#restar is the closest excess return which gives us $1$ by investing $0$, this is a obvious arbitrage
condition, therefore it does not exists, but we look for the closest one.

#proposition(title: [Properties of #rstar and #restar])[
  1. $EE[restar] = EE[m^*]/EE[(m^*)^2]$
  2. $m^* = rstar/EE[(rstar)^2]$
  3. $EE[rstar R] = EE[(rstar)^2]$ for all $R in A_1$
  4. $EE[rstar R^e] = 0$ for all $R^e in A_0$
  5. $EE[restar n] = E[n]$ for all $n in A_0$, in particular
  $
    EE[(restar)^2] = EE[restar]
  $<eq:restar-second-moment>
]<prop:properties-rstar>
#proof[
  TODO: see proposition 52
]

#remark(title: [Variance of $R^e$])[
  Thanks to @eq:restar-second-moment we have
  $
    var[R^e] = EE[R^e](1 - EE[R^e])
  $
  Moreover, $EE[R^e] != 0$, which implies $var[R^e] > 0$.
]
#proof[
  For the first identity we have
  $
    var[R^e] & = EE[(R^e)^2] - EE[R^e]^2 \
             & = EE[R^e] - EE[R^e]^2 \
             & = EE[R^e](1 - EE[R^e]^2)
  $

  TODO: second part.
]

==== Decomposition

#theorem(title: [Decomposition of $A$])[
  The space of traded payoffs $A$ decomposes orthogonally as
  $
    A = angle(alpha rstar) plus.o A_0
  $
  where $angle(alpha rstar) = "span"(rstar)$.
]

#proof[
  Let $y in A$, with initial price $pi(y) in RR$. We add and subtract the same quantity
  $pi(y) rstar$ from $y$:
  $
    y = pi(y) rstar + (y - pi(y) rstar)
  $

  Note that
  - $pi(y) rstar in angle(alpha rstar)$
  - Taking the price of $y - pi(y) rstar$ we get
    $
      pi(y - pi(y) rstar) = pi(y) - pi(y) underbrace(pi(rstar), =1)
      = pi(y) - pi(y) = 0
    $
    which means $y - pi(y) rstar in A_0$.

  Now we need to prove that this is an orthogonal decomposition, i.e. we want to show that
  $EE[(alpha rstar) R^e] = 0$ for any $R^e in A_0$. Indeed
  $
    EE[(alpha rstar) R^e] = alpha EE[rstar R^e] = alpha EE[m^* / pi(m^*) R^e ] =
    alpha / pi(m^*) EE[m^* R^e] = 0
  $
  by definition of $rstar$ and of SDF.
]

#theorem(title: [Decomposition of $A_0$])[
  The space $A_0$ decomposes orthogonally as
  $
    A_0 = angle(beta restar) plus.o {n in A_0 | EE[restar n] = 0}
  $
  or equivalently
  $
    A_0 = angle(beta restar) plus.o {n in A_0 | EE[n] = 0}
  $
  (since $n perp restar$).
]

#proof[
  Let $z in A_0$ and $beta = EE[z] / EE[restar]$,
  We add and subtract the same quantity from $z$:
  $
    z = beta restar + (z - beta restar)
  $

  First, note that $z - beta restar in A_0$ since it is the linear combination of two elements of
  $A_0$.
  Then we prove that $EE[restar (z - beta restar)] = 0$:
  $
    EE[restar (z - beta restar)] & = EE[restar z] - beta EE[restar^2] \
                                 & = EE[z] - beta EE[restar] \
                                 & = EE [z] - EE[z] / EE[restar] EE[restar] \
                                 & = EE[z] - EE[z] = 0
  $
  where we have used point 5 of @prop:properties-rstar.
]

#corollary[
  The space of traded payoffs decomposes orthogonally as
  $
    A & = angle(alpha rstar) plus.o angle(beta restar) plus.o {n in A_0 | EE[n] = 0} \
    & = {alpha rstar + beta restar + n | alpha, beta in RR, n in A_0, EE[n] = 0}
  $<eq:decomposition-of-a>
]

#proof[
  Immediate from the two previous theorems.
]

#corollary(title: [Characterization of elements of $A_1$])[
  The space of returns $A_1$ can be written as
  $
    A_1 = {rstar + w restar + n | w in RR, n in A_0, EE[n] = 0}
  $
]
#proof[
  Let $x in A$ with $pi(x) != 0$, then $R_x = x/pi(x)$.
  Since $x in A$, it can be written as
  $
    x = R_x pi(x) = pi(x) rstar + beta restar + n'
  $
  according to @eq:decomposition-of-a. Then we divide both sides by $pi(x)$ to get
  $
    R_x = rstar + beta/pi(x) restar + 1/pi(x) n'
  $
  and to conclude we set $w = beta/pi(x)$ and $n = 1/pi(x) n'$.
]

==== The frontier without a risk-free asset

#theorem(title: [Characterization of the MV frontier])[
  $rmv in A$ is on the mean-variance frontier if and only if
  $
    rmv = rstar + w restar
  $
]<thm:char-mvfront>

#proof[
  We know that any $R in A_1$ can be written as
  $
    R = rstar + w restar + n quad "with" w in RR, n in A_0, EE[n] = 0
  $

  Fix $k = EE[R]$: to do so, we uniquely identify $w$ as
  $
    w = (k - EE[restar] - cancel(EE[n])) / EE[restar]
  $

  Now we minimize the variance of $R$:
  $
    var[R] & = var[rstar + w restar] + var [n] + cancel(2 cov[rstar + w restar, n]) \
           & >= var[rstar + w restar]
  $
  where we have cancelled the covariance since the two terms are orthogonal.
  Note that equality holds if and only if $n = 0$, therefore $rmv = rstar + w restar$ has the
  desired value of $k$ while displaying the lowest possible variance.
]

In the above proof, $n$ represents the *idiosyncratic risk*: the risk which can be avoided.

Since now we have $w$ which is the optimal return we work backwards to find the portfolio which
gives that return.

#show "mvfront": [mean-variance frontier]

#theorem(title: [Two-fund Separation Theorem])[
  $rmv$ is on the mean variance frontier if and only if there exists $R'$ and $R''$ on
  the mvfront and $alpha in RR$ such that
  $
    rmv = alpha R' + (1-alpha) R''
  $
]<thm:two-fund>

#proof[
  - Let $R'$ and $R''$ belong to the mvfront, we show that $rmv$ is also on the mvfront.

    From @thm:char-mvfront we know that
    $
       R' & = rstar + w' restar \
      R'' & = rstar + w'' restar
    $
    then
    $
      rmv & =alpha R' + (1-alpha) R'' \
      & = alpha rstar + alpha w' restar + rstar - alpha rstar + w '' - alpha w '' restar \
      & = rstar + (alpha w' + (1 - alpha) w'') restar
    $
    and we can define $tilde(w) colon.eq alpha w' + (1 - alpha) w'')$ which is the value of $w$ for
    $rmv$.

  - Let $rmv$ be on the mvfront, we shot what $R', R'', alpha$ exist.

    By @thm:char-mvfront we know that $rmv = rstar + w restar$ for some $w in RR$.
    Now take any $tilde(R) = rstar + tilde(w) restar$ on the mvfront with $tilde(w) != 0$ and set
    $R' = rstar$ and $R'' = tilde(R)$.

    Then
    $
      restar = 1/tilde(w) (R'' - R')
    $
    and
    $
      rmv = rstar + w/tilde(w) (tilde(R) - rstar) = alpha R' + (1- alpha) R''
    $
    where $alpha = 1 - w/tilde(w)$.
]

With some magic algebra tricks we can show that the mvfront is a hyperbola in the $sigma[R]-EE[R]$
plane, see figure 4.1 in the lecture notes.

=== Proxies for the risk-free asset

Until now we have considered the case where there is no risk-free asset, however, before analyzing
the case where we introduce one, we look at three criteria which can be used as risk-free proxies:
alternatives when the risk free asset does not exist.

1. The global minimum portfolio return, that displays the lowest possible variance;
2. The zero-beta (i.e. uncorrelated) portfolio on the mvfront that displays a zero covariance with a
  fixed starting portfolio on the frontier;
3. The constant-mimicking portfolio return, which is the normalized projection of the risk free
  asset on the space of traded payoffs.

We now analyze these possibilities one by one.

==== Global minimum variance portfolio return

The global minimum variance portfolio return solves the following optimization problem
$
  min_(w in RR) var[R^* + w R^e^* + n] & = min_(w in RR) var[R^* + w R^e^*] \
  & = min_(w in RR) var[R^*] + w^2 var[R^e^*] + 2w cov[R^*, R^e^*] \
$
where we can cancel the terms with $n$ since it is orthogonal to both $R^*$ and $R^e^*$ and since
$EE[n] = 0$.

Note that
$
  cov[R^*, R^e^*] = cancel(EE[R^* R^e^*]) - EE[R^*] EE[R^e^*]
$
which can be different from zero.


We conclude that the first order condition of the minimization problem is
$
  2w var[restar] - 2 EE[rstar] EE[restar] = 0
$
Then, we can compute $w_("MIN")$ by using @eq:restar-second-moment:
$
  w_("MIN") & = (EE[rstar] EE[restar])/ var[restar]
              = (EE[rstar] EE[restar])/ (EE[(restar)^2] - (EE[restar])^2 ) \
            & = (EE[rstar] EE[restar])/ (EE[restar] (1 - EE[restar]))
              = EE[rstar] / (1 - EE[restar])
$
therefore
$
  R_("MIN") = rstar + EE[rstar] / (1 - EE[restar]) restar
$
is the global minimum variance portfolio return.

#remark[
  $
    EE[R_"MIN"] = w_("MIN")
  $
]
#proof[
  TODO: remark 62
]

#definition(title: "Efficient return")[
  A return $rmv$ on the mvfront is efficient if $EE[rmv] > EE[R_("MIN")]$.
]

==== Zero-beta portfolio

#let zcr = $z c [R]$

Given any $R != R_("MIN")$ there exists an unique portfolio $zcr$ which in uncorrelated from $R$ on
the frontier.
Assuming that $R$ is on the mvfront, we can decompose it as usual and get that
$zcr = rstar + w_zcr restar$ imposing that
$
  cov (R, zcr) = 0
$
and from some algebra (see page 45 in lecture notes) we get
$
  w_zcr = (w EE[rstar] EE[restar] - var[rstar])/(w var[restar] - EE[rstar] EE[restar])
$

#remark[
  Any other return with the same expected return of $R$ is still uncorrelated from $zcr$.
]

An intuitive way to find $zcr$ is to start from $R$, draw the tangent line to the frontier passing
through it, follow the line until $sigma = 0$, then move horizontally until we intercept the
frontier again (see figure 4.2 in lecture notes).

==== Constant mimicking portfolio return

This is the traded return which is closest to $1$:
$
  "proj"[1 | A]
$
and its return is
$
  R_("CMR") = "proj"[1|A]/pi("proj"[1|A])
$

Recall that $cal(L)^2$ (i.e. the space of distributions with finite variance) can we decomposed as
the sum of $A^perp$, $"span"(rstar)$ and $A_0$, therefore we can write
$
  1 = "proj"[1|A^perp] + "proj"[1|rstar] + "proj"[1|A_0]
$
and (after computing the least squares) we get
$
  1- "proj"[1|A^perp] = EE[rstar]/EE[(rstar)^2] rstar + restar = "proj"[1|A]
$
by our decomposition. Finally
$
  pi("proj"[1|A]) = EE[rstar]/EE[(rstar)^2] != 0
$
as $pi(rstar) = 1$ and $pi(restar) = 0$ and the fact that it is $!= 0$ comes from the assumption of
no risk-neutrality.

We get
$
  R_("CMR") & = ("proj"(1|A))/(pi("proj"(1 | A )))= rstar + (EE[(rstar)^2]) / (EE [rstar]) restar \
  w_("CMR") & = (EE[(rstar)^2]) / (EE [rstar]) \
  EE[R_("CMR")] & = (EE[(rstar)]^2 + EE[(rstar)^2] EE[restar]) / (EE [rstar]) \
$

Moreover, it can be shown (see remark 65 in lecture notes), that $EE[R_"CMR"] > EE[R_"MIN"]$.

=== Frontier with riskless asset

Introduce a riskless asset $B$ with $R_f = B(1)/B(0) > 0$.
We can now define a variant of every object we defined before, note that in general these new
version of $rstar, restar$, etc are different from the ones we found without the risk-free asset.
The decompositions of $A$, $A_1$ and $rmv$ still hold.

#proposition(title: [$R_f$ is on the mvfront])[
  $R_f$ is on the mvfront and it can be decomposed as
  $
    R_f = rstar + R_f restar
  $
]

#proof[
  $R_f$ is obviously on the mvfront since $var[R_f] = 0$.

  Since $R_f$ is on the mvfront, there must exist $tilde(w)$ such that
  $
    R_f = rstar + tilde(w) restar
  $

  By the existence of $R_f$ we deduce that $1 in A$, therefore there must exist $alpha$ such that
  $
    1 = alpha rstar + restar
  $
  since $restar = "proj"[1 | A_0]$.

  Moreover, we have
  $
    1 / R_f & = pi(1) = EE[m^*] \
            & = EE[m^* (alpha rstar + restar)] \
            & = alpha EE [m^* rstar] + EE[m^* restar] \
            & = alpha
  $
  which means
  $
    1 = 1/R_f rstar + restar
  $
  which is equivalent to
  $
    R_f = rstar + R_f restar
  $
  as desired.
]

#proposition[
  $EE[rmv] - R_f > 0$ if and only if $alpha < 0$ according to @thm:two-fund.
]

#proof[
  We have $rmv = (1-alpha) R_f + alpha rstar$ and taking the expectation we get
  $
    EE[rmv] & = (1 - alpha) R_f + alpha EE[rstar] \
            & = R_f + alpha (EE[rstar] - R_f)
  $
  then $EE[rmv] - R_f = alpha(EE[rstar] - R_f)$.
  Moreover, since $R_f = EE[R_f] = EE[rstar] + R_f EE[restar]$, we get
  $
    EE[rstar] - R_f & = EE[rstar] - EE[rstar] - R_f EE[restar] \
                    & = - R_f EE[restar] \
                    & = - R_f EE[(restar)^2] < 0
  $
  by @eq:restar-second-moment.
  We conclude that $EE[rmv] - R_f > 0$ iff $alpha < 0$.
]

It can be shown again with some algebra that the mvfront is two lines which touch in $(R_f, 0)$, see
Figure 4.3 in lecture notes.

==== Optimal Risky Portfolio

#let rorp = $R^"ORP"$

#definition(title: [Optimal Risky Portfolio return])[
  Assume $R_f < EE[R^"MIN"]$ and consider the tangent from $(0, R_f)$ to the frontier of risky-only
  assets in the $sigma[R]-EE[R]$.
  We call optimal risky portfolio return $rorp in A_1$ such that $(sigma[rorp], EE[rorp])$ are the
  coordinates of the point of tangency.
]

#proposition[
  Assume that $R_f < EE[R^"MIN"]$. Then the frontier when the riskless asset is traded coincides
  with the tangent on the $sigma[R]-EE[R]$ plane from $(0, R_f)$ to the mvfront with risky asset
  only.
  As a consequence $rorp$ is the unique return that belongs to both frontiers.
]

#proof[
  TODO: Proposition 71
]

#remark[
  By @thm:two-fund we can write any $R in A_1$ on the frontier iff
  $
    R = (1 - alpha) R_f + alpha rorp
  $
]<rmk:two-fund-orp>

== Beta-pricing equations

A beta-pricing equation relates the expected return of a security with its systematic risk, i.e. the
risk that investors still need to face to after having followed a proper diversification strategy
(like the one presented in the previous chapter).

Assuming the risk-free asset is not traded, a general beta-pricing equation takes the form of
$
  EE[R] = gamma + sum^L_(ell = 1) beta_(R, ell) lambda_ell wide R in A_1
$
where $gamma$ is a constant representing a "proxy" for the risk-free asset. The underlying idea is
that the return of each asset is governed by the sum of some underlying functions $f_1, ..., f_ell$:
for each factor $ell = {1, ..., L}$, $beta_(R, ell)$ represents the amount of "risk" for $R$, while
$lambda_ell$ represents the right remuneration per unit-risk.

We will only investigate *single factor* beta equations, which take the form of
$
  EE[R] = gamma + beta_(R, f) lambda
$
this means that
$
  beta_(R, f) = cov[f, R]/var[f]
$
The idea is that $beta_(R, f)$ is the fraction of total risk (represented by $var[f]$) which is
"due" to $R$ (represented by $cov[f, R]$).

=== Relationship with SDFs

#theorem[
  Assume $var[f] != 0$. Then, there exist $lambda, gamma in RR$, $gamma != 0$ such that
  $
    EE[R] = gamma + beta_(R, f) lambda wide "with" cases(
      beta_(R, f) = cov[R, f]/var[f],
      R in A_1
    )
  $
  if and only if $exists a, b in RR$ with $a + b EE[f] != 0$ such that
  $
    m = a + b f wide "is an SDF"
  $
]

#proof[
  We prove each implication separately.

  / SDF $==>$ Beta: Assume $exists a, b in RR$ with $a + b EE[f] != 0$ such that $m = a + b f$ is an
    SDF.
    This means that $forall R in A_1$ we have $EE[(a + b f) R] = 1$ and by linearity of the
    expectation we get
    $
      a EE[R] + b (cov[f, R] + EE[f] EE[R]) = 1
    $<eq:proof-beta-sdf-1>
    By assumption, we know that $a + b EE[f] != 0$, therefore we can define
    $
       gamma & = 1/(a + b EE[f]) \
      lambda & = - b var[f] gamma
    $
    and by solving for $EE[R]$ and substituting $gamma, lambda$ where needed we obtain the result.
  / Beta $==>$ SDF: Assume $EE[R] = gamma + beta_(R, f) lambda$ for all $R in A_1$ with
    $gamma, lambda != 0$ and $gamma != 0$. We want to find $a, b in RR$ such that $m = a + b$ is an
    SDF.

    We use @eq:proof-beta-sdf-1 and substitute the assumption that $EE[R] = gamma + beta_(R, f)
    lambda$ obtaining
    $
      & a (gamma + beta_(R, f) lambda) + b (cov[f, R] + EE[f](gamma + beta_(R, f) lambda) &= 1 \
      ==> & (a + b EE[f]) (gamma + beta_(R, f) lambda) + b cov[f, R] & = 1 \
      ==> & gamma (a + b EE[f]) + beta_(R, f) (lambda (a + b EE[f]) + b var[f]) &= 1
    $
    where the last implication is by the definition of $beta_(R, f)$.

    Note that $beta_(R, f) != 0$, as otherwise $EE[R] = gamma$ for all $R in A_1$, which is against
    the assumption of no risk neutrality.

    Then, we must (TODO: why?) have that
    $
      cases(
        lambda (a + b EE[f]) + b var[f] = 0,
        gamma (a + b EE[f]) = 1
      )
    $
    and by solving the system for $a, b$ we obtain the result.
]


#corollary[
  Let $tilde(f) := "proj"[f | A]$ such that $pi(tilde(f)) != 0$.
  Define $R' = tilde(f) / pi(tilde(f))$.
  Then $exists gamma != 0$ such that
  $
    EE[R] = gamma + beta_(R, R')(EE[R'] - gamma) wide "with" beta_(R, R') = cov(R, R')/var(R')
  $
  if and only if there exist $a, b in RR$ such that $a + b EE[R] != 0$ and
  $
    m = a + b R' wide "is an SDF"
  $
]

=== TODO: MV return without risk-free asset
=== TODO: MV return with a risk-free asset

== Capital Asset Pricing Model

In this chapter we will assume that all risky assets are in a fixed supply: for all
$j in {1, ..., N}$, $macron(theta)_j$ is the fixed supply of shares of $j$, while $S_j
macron(theta)_j$ is the market cap of $j$. The total market cap is defined as
$sum_(j = 1)^N S_j macron(theta)_j$.

The risk-free asset instead is in _zero-net-supply_, this means that I can only borrow if someone
else is lending. Mathematically
$
  sum_(i = 1)^I W^i (0) (1 - alpha^i) = 0
$
where $I$ is the set of all "players", $W^i (0)$ is the wealth of player $i$, and the equation comes
from @rmk:two-fund-orp. This in turns means that the aggregate wealth, defined as
$
  W(0) = sum^I_(i = 1) alpha^i W^i (0)
$
is fully invested in (risky) stocks.

For risky assets we have instead
$
  S_j macron(theta)_j = sum^I_(i = 1) alpha^i W^i (0) w_j^i
$
where the left is the supply for $j$, while the right is the demand. The term $w_j^i$ indicates the
ratio of wealth of $i$ which is invested in $j$: $w_j^i = theta_j^i / W^i (0)$, which means that
clearly its sum over $j$ is $1$.

Then, summing up the above equation over $j$ we get
$
  sum_(j = 1)^N S_j macron(theta)_j & = sum^N_(j = 1) sum^I_(i = 1) alpha^i W^i (0) w_j^i \
  & = sum^I_(i = 1) alpha^i W^i (0) = W(0)
$
which gives us
$
  omega_j^i = (S_j macron(theta)_j) / (sum^N_(j = 1) S_j macron(theta)_j) = w_j^M
$
this means that all the investors invest in the same manner.

By the beta-pricing equation we get the CAPM equation.
$
  EE[R] = R_f beta_(R R^M) (EE[R^M] - R_f)
$

= Discrete-Time Multi-Period Market Models

Each time step is $t in {0, Delta t, 2 Delta t, ..., T}$, the event space is
$Omega = {omega_1, ..., omega_k}$ (finite) where $omega_k in Omega$ will only be revealed at time
$T$.

We now want to understand the actions which investors are going to take in the intermediate time
steps $t$ such that $Delta t <= t <= T - Delta t$.

Consider $cal(A) in cal(P)(Omega)$ be a partition of $Omega$. We say that a partition $cal(A)$ is
*finer* than another partition $cal(A)'$ if
$
  A in cal(A) ==> exists A' in cal(A)' "s.t." A subset.eq A'
$

Let us also introduce the *information structure* $cal(P)$ defined as
$
  cal(P) = { P_t }^T_(t = 0)
$
where each $P_t$ is a collection of partitions of $Omega$. We want $cal(P)$ to have the following
properties:
1. $P_0 = { Omega }$, which is the least fine partition.
2. $P_(t_Delta t)$ is finer than $P_t$ for all $t = Delta t, ..., T - 2 Delta t$, this is the
  concept of learning "with memory"
3. $P_T = {{omega_1}, ..., {omega_k}}$ is the finest partition.

We introduce the process of *filtration*: the sequence $cal(F)_t$ is a sequence of $sigma$-algebras
generated by $P_t$. At $t = 0$ we have $cal(F)_0 = { emptyset, Omega }$.
