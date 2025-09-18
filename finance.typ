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

=== Linear Pricing Functional (LPF)

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

=== Stochastic Discount Factor (SDF)

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

=== State-Price Vectors (SPV)

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

== Fundamental Theorem of Finance

=== First Fundamental Theorem of Finance

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

=== Complete Markets

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

=== Second Fundamental Theorem of Finance

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
