#import "lib/template.typ": *
#import "lib/utils.typ": *
#import "lib/theorem.typ": *

#show: template.with(
  titleString: "Mathematical Modelling for Finance",
  author: "Giacomo Ellero",
  date: "A.Y. 2025/2026",
  bigHeading: false,
)

#show: thm-init

#let proj = math.op("proj")

#pagebreak()

= Linear Algebra & Stats

/ Matrix-Vector Multiplication:
  $
    mat(delim: "[", a, b; c, d) mat(delim: "[", x; y) = mat(delim: "[", a x + b y; c x + d y)
  $

/ Matrix multiplication: For entry $i j$ in the result matrix we have to do the dot product of the
  row $i$ of the first matrix and the column $j$ of the second one.

/ Determinant:
  - $2 times 2$: $det \( A \) = a d - b c$.

  - $3 times 3$:
    Compute with the definition (recall that signs are $+$, $-$ and $+$ for a 3x3) or use Sarrus Rule
    $
      det mat(delim: "[", a, b, c; d, e, f; g, h, i)
      = a ( e i - f h ) - b ( d i - f g ) + c ( d h - e g )
    $

/ Full Rank:
  For an $n times n$ matrix there holds $"rank"(A) = n <==> det(A) != 0$.

/ Matrix Inversion ($2 times 2$):
  $ A^(- 1) = frac(1, a d - b c) mat(delim: "[", d, - b; - c, a) $

/ Variance decomposition:
  $ V(X) = EE[X^2] - (EE[X])^2 $

/ Covariance:
  $
    cov[X, Y] = EE[X Y] - EE[X] EE[Y]
  $

= One-Period Market Fundamentals

== Definitions
/ Asset Payoff $S_j (1)$: A random variable vector representing the value of securities at time
  $t = 1$ across different states $omega$.

/ Portfolio $theta$: A vector representing the number of units held of each security.

/ Market Completeness: A market is complete if every possible payoff $X in bb(R)^N$ can be
  replicated by a portfolio $theta$ (i.e. $S(1) dot.op theta = X$).
  This is equivalent to saying that the payoff matrix $cal(A)$ has full rank.

/ Law of One Price (LOP): If two portfolios have the same
  payoff in every state, they must have the same initial price.

/ Arbitrage Opportunity: A trading strategy $theta$ that
  satisfies either:

  + $V_0 \( theta \) lt.eq 0$ and $V_1 \( theta \) gt.eq 0$ (in all
    states), with strict inequality in at least one state.

  + $V_0 \( theta \) < 0$ and $V_1 \( theta \) gt.eq 0$ (in all states).

/ State Price Vector ($psi$): A vector of strictly positive
  prices for the Arrow-Debreu securities (pays 1 in state $i$, 0
  otherwise). LOP holds if a solution exists; No Arbitrage holds if a
  *strictly positive* solution exists.

== Finding Arbitrage Opportunities

#strong[Reasoning:] If the No-Arbitrage condition is violated, you must
construct a specific portfolio $theta$ that generates risk-free profit.

=== Violation of LOP (Redundant Assets)

/ What: We have $S_3 (1)$ which can be written as a linear combination of $S_1 (1)$ and
  $S_2 (1)$, but $S_3 (0) > alpha S_1 (0) + beta S_2 (0)$.

/ Detection: If $det(A) != 0$ LOP holds, if $det(A) != 0$ we look for linearly dependent columns.
  If we find any, for LOP to hold we need their initial price to be the same.

/ Arbitrage strategy:
  + Find the replication weights $alpha, beta$.
  + Compare the costs: is $S_3 (0) > alpha S_1 (0) + beta S_2 (0)$?
  + Sell the expensive one $S_3$ and buy $alpha$ of $S_1$ and $beta$ of $S_2$.

=== Violation of No Arbitrage
/ Detection: You solve the system $S_1^T psi = S_0$ and find a state price $psi$ such that for some
  $k$ we have $psi_k < 0$.

/ Meaning: The market is \"paying you\" to accept a payout in state $k$.

/ Arbitrage Strategy: You want to buy state $k$. Find the portfolio $theta$ that
  solves $S_1 theta = upright(bold(e))_k$ (where $upright(bold(e))_k$ has 1 in state $k$ and 0
  elsewhere).

/ Result: The cost of this portfolio is $V_0 = psi_k < 0$ (instant profit), and at $t = 1$ you
  receive 1 if state $k$ occurs (or 0 otherwise), so you never lose money.

= Markowitz Mean-Variance (Matrix Approach)

== Definitions

/ Mean-Variance Frontier: The set of portfolios that minimize
  variance for a given level of expected return.

/ Global Minimum Variance (GMV) Portfolio: The portfolio on the
  frontier with the absolute lowest variance
  ($w_(G M V) prop Sigma^(- 1) upright(bold(1))$).

/ Efficient Frontier: The upper branch of the hyperbola (or the
  CML with risk-free asset) where investors maximize return for a given
  risk level.

/ Tangent (Market) Portfolio: The unique portfolio of risky
  assets that, when combined with the risk-free asset, lies on the
  Capital Market Line (CML) tangent to the risky frontier.

== The Efficient Frontier

=== Risky only
Compute the 4 Constants using $mu$ and $Sigma^(- 1)$:
$
  A = upright(bold(1))^T Sigma^(- 1) mu \, quad B = mu^T Sigma^(- 1) mu \, quad C = upright(bold(1))^T Sigma^(- 1) upright(bold(1)) \, quad D = B C - A^2
$

Then the optimal weights $w^* (k)$ are
$
  w^* (k) = g + h k wide "with" cases(
    display(g = 1 / D \( B Sigma^(- 1) upright(bold(1)) - A Sigma^(- 1) mu \)),
    display(h = 1 / D \( C Sigma^(- 1) mu - A Sigma^(- 1) upright(bold(1)) \))
  )
$

*Frontier Equation (Hyperbola)*
$ sigma^2 = frac(C k^2 - 2 A k + B, D) $

=== With risk-free
<formula-with-risk-free-r_f>
/ Excess return vector:
  $
    mu_e = mu - R_f upright(bold(1))
  $

/ Frontier Equation (Line/CML):
  $
    bb(E) \[ R \] = R_f + sqrt(H) sigma wide "with" H = mu_e^T Sigma^(- 1) mu_e
  $

= Hansen-Richard
#let rstar = $R^*$
#let restar = $R^e^*$
#let rmv = $R^"MV"$

== Key Definitions

/ Stochastic Discount Factor (SDF):
  A random variable $m$ such that for any asset with payoff $X$ and price $P$,
  $P = EE[ m X ]$. It relates to state prices by
  $m (omega) = (psi ( omega )) / (p (omega))$.

/ Orthogonal Projection:
  $proj [ n divides A]$ is the vector within a subspace $A$ (e.g., the span of traded
  assets) that is closest to vector $n$ in the mean-square sense.

/ Prices and returns: Let $S = [S_1 (0), ..., S_n (0)]^T$ and $x = [S_1 (1), ..., S_n (1)]^T$ ($x$
  is a random vector).

/ Spaces:
  $
      A & = angle(x_1, ..., x_n) wide   & "Space of traded payoffs" \
    A_1 & = {R in A | pi(R) = 1} wide   &        "Space of returns" \
    A_0 & = {R^e in A | pi(R) = 0} wide & "Space of excess returns" \
  $

== Computing $R^(*)$ and $R^(e^*)$
Instead of inverting covariance matrices, we use projections to find the efficient frontier
components.

/ Find $m^*$:
  $m^*$ is the unique SDF such that $m^* in A$.
  $
    m^* = S^T EE[x x^T] x
  $

/ Find other SDFs:
  All other SDFs can be written as $m = m^* + epsilon$ for $epsilon in A^perp$. To characterize
  $A^perp$ we solve $EE[epsilon^T S] = 0$ for all $S in A$.

/ Finding $R^(*)$: $rstar$ is always
  $
    R^(*) = (m^*)/ (EE [(m^*)^2])
  $

/ Finding $R^(e^*)$ (with riskless):
  $
    restar & = proj[1 | A_0] \
    & = proj[1 | A_1] - proj[1 | angle(rstar)]
    & = 1 - EE[rstar]/EE[(rstar)^2] rstar
  $

/ Finding $restar$ (without riskless):
  $
    restar & = proj[1 | A_0] \
           & = proj[1 | A_1] - proj[1 | angle(rstar)] \
           & = A theta_A - EE[rstar]/EE[(rstar)^2] rstar
  $
  where $theta_A$ is defined as (minimize square loss)
  $
    theta_A & = argmin_(theta in RR^N) EE[(1 - A theta)^2] \
            & = (EE[A^T A])^(-1) EE[A^T bold(1)]
  $


/ Frontier: Any frontier return is
  $
    R^("MV") & = R^(*) + w R^(e^*) \
             & = (1 - alpha) R_f bold(1) + alpha rstar
  $
  where
  $
      alpha & = (k - R_f)/(EE[rstar]- R_f) \
    w_"min" & = EE[rstar]/(1 - EE[restar])
  $
  where $k$ is the desired expected return.

/ Risk-free proxies:
  $
    R_"min" & = rstar + (EE[rstar])/(1 - EE[restar]) restar wide & "minimum variance"\
    R_"cmr" & = rstar + EE[(rstar)^2]/EE[rstar] restar wide & "constant mimicking"
  $

= Beta Pricing

== Definitions

/ Beta Pricing Equation:
  $
    EE[R] = gamma + sum^L_(ell = 1) lambda_ell beta_(R, ell)
  $
  where $gamma$ is a constant representing a "proxy" for the risk-free asset. The underlying idea is
  that the return of each asset is governed by the sum of some underlying functions $f_1, ..., f_ell$:
  for each factor $ell = {1, ..., L}$, $beta_(R, ell)$ represents the amount of "risk" for $R$, while
  $lambda_ell$ represents the right remuneration per unit-risk.

  We usually consider just one factor $f$, therefore the single factor beta equation is
  $
    EE[R] = gamma + lambda beta_(R, f)
  $

/ Beta: Sensitivity of an asset's return $R$ to a factor $f$.
  $
    beta = cov[f, R]/var[f]
  $
  where $R in A_1$ and $f$ is a certain risk factor.


// / Power Utility (CRRA):
//   $
//     u \( w \) = cases(
//       display(frac(w^(1 - gamma), 1 - gamma)) wide & "if" gamma != 1,
//       log w wide & "for" gamma = 1,
//     )
//   $
//   $gamma$ is the coefficient of relative risk aversion.

== Compute parameters

+ Find $a, b in RR$ such that an SDF $m = a + b f$.
+ Compute
  $
     gamma & = 1/(a + b f) \
    lambda & = -b var[f] gamma = EE[f] - gamma
  $

Let $R_"MV"$ be on the Mean-Variance frontier, then
$
  EE[R] = cases(
    R_f + beta_(R, R_"MV") (EE[R_"MV"] - R_f) wide & "with riskless",
    EE["zc"(R)] + beta_(R, R_"MV") (EE[R_"MV"] - EE["zc"(R)]) wide & "without riskless"
  )
$
where $"zc"(R)$ is such that $cov("zc"(R), R) = 0$.


#pagebreak()

= Multiperiod

== Definitions

/ Notation: We denote the set of "layer" as $cal(P)_t$, this is the set of all possible scenario
  (node) $f^t_k$ which can realize at time $t$. Conditioning on $cal(P)_t$ means we know which state
  we are in at time $t$.

/ Martingale Property: The expected value of the next observation is equal to the (discounted
  previous value.

/ Risk-Neutral Measure ($bb(Q)$): A probability measure under which the discounted price process is
  a martingale
  $
    S_j (t) = EE^QQ [(S_j (t + 1))/(1 + r(t)) mid(|) cal(P)_t]
  $

/ Self-financing:
  A strategy $theta$ is self financing if
  $
    V_theta (t + 1) = theta_0 (t) B(t + 1) + theta_1 (t) S_1 (t + 1)
  $

/ American Option: A derivative that can be exercised at any
  time $t lt.eq T$. Its value is the maximum of the immediate payoff and
  the continuation value.

/ Barrier Option: A path-dependent option. _Knock-out_ becomes worthless if the barrier is crossed;
  _Knock-in_ only becomes active if the barrier is crossed.

/ Running Maximum ($M_T$): The maximum price observed up to time $T$:
  $ M_T = max_(0 lt.eq t lt.eq T) S (t) $

== Binomial model

There are just two assets: a riskless security $B$ with rate $r$ and a risky asset $S$.

/ Values of $S$:
  $
    S(t + 1) = cases(
      S(t) u wide & "with probability" p,
      S(t) d wide & "with probability" 1-p,
    )
  $
  Therefore
  $
    prob (S(t) = S u^k d^(t - k)) = binom(t, k) p^k (1 - p)^(t - k)
  $

/ No Arbitrage: We need $d < 1 + r < u$, otherwise we have an arbitrage opportunity.
/ Completeness: Same as NA.

/ Risk neutral probabilities:
  $
    QQ (S(t + 1) = S(t) u) = q = (1 + r - d) / u - d
  $
  then
  $
    QQ(S(t) = S u^k d^(t - k)) = binom(t, k) q^k (1 - q)^(t - k)
  $

== Computing $QQ$

/ General case: For each node solve the system
  $
    cases(
      display(S(t) = 1/(1+r) sum_k S(omega_k) QQ(omega_k)),
      display(sum_k QQ(omega_k) = 1)
    )
  $
  Then we can find the probability of a certain path by multiplying the probability at each node
  $QQ("path") = q_(t = 1) dot.op q_(t = 2) dot.op ...$.

/ Binomial model:
  $
    q = ((1 + r) - d)/(u - d)
  $
  Then, letting $k$ be the number of "up" movements,
  $
    QQ(omega) = q^k (1 - q)^(T-k)
  $

== Market properties

/ Arbitrage free: If $exists QQ$, then the market is arbitrage free.

  If there is an arbitrage opportunity then there exists at least one one-period submarket with an
  arbitrage opportunity in it. Find it by checking in which one $QQ$ would be negative and then use
  the same techniques as in the one-period case to find an explicit arbitrage opportunity.

  In binomial models we have an arbitrage if $1 + r < d$ or $1 + r > u$.

/ Completeness: If $QQ$ is unique then the market is complete. We can also check that each submarket
  is complete.

== Pricing European option

Note that $c(t) = V(t) / (1 + r)$.

/ Risk neutral valuation:
  + Compute $q$.
  + Compute the terminal payoff $c(T)$ for each $omega$.
  + Starting from $t = T - 1$ compute
  $
    c(t) = 1/(1 + r) EE^QQ [c_omega (t + 1) | cal(P)_t]
  $

/ Replication:
  We look for a portfolio $theta^*$ which perfectly replicates the derivative.

  Starting at $t = T$, we recourse backwards and at each $f^t_k$ we solve the
  following linear system for the vector $theta(t - 1) (f_k^(t - 1))$
  $
    cal(A)(t - 1) (f^(t - 1)_k) dot.op theta(t - 1)(f_k^(t - 1)) = V_theta (t)
  $
  imposing $V_theta (T) = V_X (T)$, where $cal(A)(t - 1) (f^(t - 1)_k)$ is the cashflow matrix at
  time $t-1$ in node $f^(t - 1)_k$.

  In the case of the binomial model we have
  $
    mat(
      delim: "[",
      (1 + r)^t, S(t - 1)(f^(t - 1)_k) u;
      (1 + r)^t, S(t - 1)(f^(t - 1)_k) d;
    )
    vec(delim: "[", theta_0 (t - 1) (f_k^(t - 1)), theta_1 (t - 1) (f_k^(t - 1)))
    = V_theta (t)
  $

/ Hedging: In a market with one riskless and one risky security we have
  $
        V_X (t) & = EE^QQ [tilde(V)_X (t + 1) mid(|) cal(P)_t] \
    theta_1 (t) & = (cov^QQ [tilde(V)_X (t + 1), Delta tilde(S)_1 (t) mid(|) cal(P)_t])/(var^QQ
                  [Delta tilde(S)_1 (t) | cal(P)_t]) \
    theta_0 (t) & = tilde(V)_X (t) - theta_1 (t) tilde(S)_1 (t)
  $
  where
  $
    tilde(V)_X (t) = (V_X (t)) / (B(t)), wide
    tilde(S)_1 (t) = (S_1 (t)) / (B(t)), wide
    Delta tilde(S)_1 (t) = (S_1 (t + 1)) / B(t + 1) - (S_1 (t)) / B(t)
  $

  In the binomial model
  $
    theta_1 (t) = (V_X (t + 1 | S(t + 1) = S_t u) - V_X (t + 1 | S(t + 1) = S_t d)) / (S_t (u - d))
  $

== Pricing American option

$
  tilde(V) (t) = sup_(t <= tau <= T) EE^QQ [X(tau)/B(tau) mid(|) cal(P)_t]
$

The optimal $tau$ is
$
  tau^* (omega) = min {t | tilde(V) (t) (omega) = tilde(X) (t) (omega)}
$
therefore we exercise the option as soon as the value of the option is equal to the underlying
payoff.

$
  tilde(V) (t) = max {tilde(X)(t), #h(0.75em) EE^QQ [tilde(V)(t + 1) | cal(P)_t]}
$

/ Continuation value:
  This is the value the holder gains if they decide to wait until $t + 1$.
  $
    "CV"(t) = B(t) dot.op EE^QQ [tilde(V) (t + 1) | cal(P)_t]
  $

/ Hedging:
  Let $C(t)$ be the cumulative consumption in the interval $[0, t)$. The writer wants to find the
  super-replicating portfolio-consumption pair $Phi$ with minimal cost. (We introduce the
  consumption since the Early Exercise Premium decreases with time). We get that
  $tilde(V)_(Phi^*) (t) = tilde(V)(t)$.

  $
    tilde(V) (t) & = max{tilde(X)(t), #h(0.75em) EE^QQ [tilde(V)_X (t + 1) mid(|) cal(P)_t]} \
    theta_1^* (t) & = (cov^QQ [tilde(V) (t + 1), Delta tilde(S)_1 (t) mid(|) cal(P)_t])/(var^QQ
    [Delta tilde(S)_1 (t) | cal(P)_t]) \
    theta_0^* (t) & = tilde(V)_X (t) - theta_1^* (t) tilde(S)_1 (t) \
    Delta tilde(C)^* (t) & = - EE^QQ [Delta tilde(V) (t) | cal(P)_t]
  $

  If (and only if) the holder does not exercise the option optimally, the writer can consume $Delta
  tilde(C)^* (t)$ by selling some $B$.


= Portfolio Optimization

This section deals with finding optimal strategies over time to maximize
utility of terminal wealth or consumption.

== Definitions

/ Relative portfolio weights: $alpha_i (t)$ is the fraction of $w$ invested in asset $i$ at time
  $t$.

/ Value Function $F (t, w)$: The maximum expected utility achievable from time $t$ onwards, given
  current wealth $w$.
  $
    F (t, w) = max_alpha EE [ sum^T_(s = t) u(V(s), alpha(s)) mid(|) V(t) = w ]
  $

/ State Price Density ($L$): Density of one probability compared to the other.
  $
    EE^QQ [X] = sum X(omega_k) QQ(omega_k)/PP(omega_k) PP(omega_K) = EE^PP [X dot.op L]
  $
  In the binomial model we have
  $
    L = dv(QQ, PP) = (q / p)^(N_u) ((1 - q) /(1 - p))^(N_d)
  $


== Optimal Portfolio Weight in Binomial Model

We want to solve
$
  max_alpha EE[sum^T_(t = 1) u(V(t), alpha(t))]
$

Determining the constant fraction of wealth invested in the risky asset ($S$) to maximize power/log
utility.
$
  u(w) = cases(
    display((w^(1 - gamma) - 1) / (1 - gamma)) wide & gamma != 1,
    ln w wide & gamma = 1
  )
$
where $gamma$ represents risk aversion.

/ Backwards recursion:
  Set $F(T, w) = u(w)$, then recourse backwards
  $
    F(t, w) = max_(alpha(t)) ( u(w, alpha(t)) + EE[F(t + 1, V(t + 1)) | V(t) = w])
  $
  where
  $
    V (t + 1) = V(t) (alpha_0 (t) (1 + r(t)) + sum^N_(i = 0) alpha_i (t) xi_i (t + 1))
  $

/ Log Utility ($gamma = 1$):
  $
    x_t^* = frac(R, u - d) frac(p - q, q \( 1 - q \))
    wide "with" R = 1 + r, thick forall t
  $
  Therefore $x^* > 0 <==> p > q$.

  $
    V_theta (1) = (1 - x_1^*) R + x^*_1 xi_1 \
    (V_theta (2)) / (V_theta (1)) = (1 - x^*) R + x_1^* xi_2
  $

/ Power Utility ($gamma eq.not 1$):
  $
    x^(*) = frac(R \( 1 - A \), A \( u - R \) + R - d)
    wide "with" A = (frac(q, 1 - q) frac(1 - p, p))^(1 \/ gamma)
  $
  Note: The weight $x^(*)$ is constant over time and independent of wealth.

== Martingale method

Finding the optimal wealth profile $V^(*)$ directly using the state price density $L$.

/ General Condition:
  $
    u' (V^*) = lambda L/B(T) ==> V^* = (u')^(-1) (lambda L/B(T))
  $

/ Log Utility:
  $
    V^(*) = w B(T)/L
  $

/ Power Utility:
  $
    V^* = w/H (L/B(T))^(-1/gamma) wide "with" H = EE[(L/B(T))^((gamma - 1)/gamma)]
  $


