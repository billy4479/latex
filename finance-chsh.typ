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

//
//
// == Exercise: Utility Maximization (One Period)
// <exercise-type-utility-maximization-one-period>
// #strong[Reasoning:] In a complete market, you can solve for the optimal
// wealth $W_T$ that equates marginal utility to the state price density.
//
// - #strong[First Order Condition:] $u' \( W_T \) = lambda L / B_T$ (where
//   $L$ is the Radon-Nikodym derivative $d bb(Q) \/ d bb(P)$).
//
// = Multiperiod & Derivative Pricing
//
// == Definitions
// - #strong[Risk-Neutral Measure ($bb(Q)$):] A probability measure under
//   which the discounted price process $S_t \/ \( 1 + r \)^t$ is a
//   martingale (constant expected value).
//
// - #strong[Martingale Property:]
//   $bb(E)^(bb(Q)) \[ S_(t + 1) divides cal(F)_t \] = S_t \( 1 + r \)$.
//
// - #strong[American Option:] A derivative that can be exercised at any
//   time $t lt.eq T$. Its value is the maximum of the immediate payoff and
//   the continuation value.
//
// - #strong[Barrier Option:] A path-dependent option. #emph[Knock-out]
//   becomes worthless if the barrier is crossed; #emph[Knock-in] only
//   becomes active if the barrier is crossed.
//
// - #strong[Running Maximum ($M_t$):] The maximum price observed up to
//   time $t$: $M_t = max_(0 lt.eq s lt.eq t) S \( s \)$.
//
// == Pricing with Backward Induction
// <exercise-type-pricing-with-trees-backward-induction>
// #strong[Reasoning:] Calculate the \"risk-neutral\" probability $q$, then
// work backward from maturity.
//
// + #strong[Step 1: Compute $q$ (Risk-Neutral Probability)]
//   $ q = frac(\( 1 + r \) - d, u - d) $ Ensure $d < 1 + r < u$ for No
//   Arbitrage.
//
// + #strong[Step 2: Backward Induction]
//
//   - #strong[At $T$:] Value = Payoff (e.g., $\( K - S_T \)^(+)$).
//
//   - #strong[At $t < T$:] Value = Discounted Expectation.
//     $ V_t = frac(1, 1 + r) \[ q V_u + \( 1 - q \) V_d \] $
//
// + #strong[Step 3: Check for American Exercise]
//
//   - At each node, compare $V_t$ (Continuation Value) vs. Intrinsic Value
//     (Payoff if exercised now).
//
//   - $"Price"_t = max \( upright("Payoff")_t \, upright("Continuation")_t \)$.
//
//
// = Portfolio Optimization
//
// This section deals with finding optimal strategies over time to maximize
// utility of terminal wealth or consumption.
//
// == Definitions
//
// - #strong[Value Function $F \( t \, w \)$:] The maximum expected utility
//   achievable from time $t$ onwards, given current wealth $w$.
//
// - #strong[Bellman Principle (Dynamic Programming):] Breaks the problem
//   into recursive steps:
//   $
//     F \( t \, w \) = max_alpha bb(E) \[ u \( dots.h \) + F \( t + 1 \, dots.h \) \]
//   $
//
// - #strong[Martingale Method:] Solves the static problem of optimal
//   terminal wealth first, then finds the replicating strategy.
//
// - #strong[State Price Density ($L$):] The ratio of risk-neutral to real
//   probabilities:
//   $ L = frac(d bb(Q), d bb(P)) = (q / p)^(N_u) (frac(1 - q, 1 - p))^(N_d) $
//
// == Optimal Portfolio Weight in Binomial Model
//
// #strong[Reasoning:] Determining the constant fraction of wealth invested
// in the risky asset ($S$) to maximize power/log utility.
//
// - #strong[Log Utility ($gamma = 1$):]
//   $ x^(*) = frac(R, u - d) frac(p - q, q \( 1 - q \)) $ Where
//   $R = 1 + r$. Condition for $x^(*) > 0$: $p > q$.
//
// - #strong[Power Utility ($gamma eq.not 1$):]
//   $ x^(*) = frac(R \( 1 - A \), A \( u - R \) + R - d) $ Where
//   $A = (frac(q, 1 - q) frac(1 - p, p))^(1 \/ gamma)$. Note: The weight
//   $x^(*)$ is constant over time and independent of wealth.
//
// == Optimal Terminal Wealth
//
// #strong[Reasoning:] Finding the optimal wealth profile $V^(*)$ directly
// using the state price density $L$.
//
// - #strong[General Condition:]
//   $
//     u' \( V^(*) \) = lambda frac(L, B \( T \)) arrow.r.double.long V^(*) = \( u' \)^(- 1) (lambda frac(L, B \( T \)))
//   $
//
// - #strong[Log Utility Result:] $ V^(*) = w frac(B \( T \), L) $
//
// - #strong[Power Utility Result:]
//   $
//     V^(*) = w \( 1 + r \)^T (p / q)^(N \( T \)) (frac(1 - p, 1 - q))^(T - N \( T \))
//   $
//   Where $N \( T \)$ is the number of \"up\" moves.
//
// == Optimal Consumption
//
// #strong[Reasoning:] Balancing intermediate consumption $c \( t \)$ and
// terminal wealth $W \( T \)$.
//
// - #strong[First Order Conditions:]
//
//   - For consumption at $t$:
//     $u'_"intermediate" \( c \( t \) \) = lambda beta^(- t) frac(L \( t \), B \( t \))$.
//
//   - For terminal wealth:
//     $u'_"terminal" \( W \( T \) \) = lambda beta^(- T) frac(L \( T \), B \( T \))$.
//
// - This implies the ratio of marginal utilities equals the ratio of state
//   prices (discounted).
