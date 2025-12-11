#let horizontalrule = line(start: (25%, 0%), end: (75%, 0%))

#show terms: it => {
  it
    .children
    .map(child => [
      #strong[#child.term]
      #block(inset: (left: 1.5em, top: -0.4em))[#child.description]
    ])
    .join()
}

#set table(
  inset: 6pt,
  stroke: none,
)

#show figure.where(
  kind: table,
): set figure.caption(position: top)

#show figure.where(
  kind: image,
): set figure.caption(position: bottom)

#let content-to-string(content) = {
  if content.has("text") {
    content.text
  } else if content.has("children") {
    content.children.map(content-to-string).join("")
  } else if content.has("body") {
    content-to-string(content.body)
  } else if content == [ ] {
    " "
  }
}
#let conf(
  title: none,
  subtitle: none,
  authors: (),
  keywords: (),
  date: none,
  abstract: none,
  cols: 1,
  margin: (x: 1.25in, y: 1.25in),
  paper: "us-letter",
  lang: "en",
  region: "US",
  font: "",
  fontsize: 11pt,
  sectionnumbering: none,
  pagenumbering: "1",
  doc,
) = {
  set document(
    title: title,
    author: authors.map(author => content-to-string(author.name)),
    keywords: keywords,
  )
  set page(
    paper: paper,
    margin: margin,
    numbering: pagenumbering,
    columns: cols,
  )
  set par(justify: true)
  set text(lang: lang, region: region, font: font, size: fontsize)
  set heading(numbering: sectionnumbering)

  if title != none {
    align(center)[#block()[
      #text(weight: "bold", size: 2em)[#title]
      #(
        if subtitle != none {
          parbreak()
          text(weight: "bold", size: 1.25em)[#subtitle]
        }
      )
    ]]
  }

  if authors != none and authors != [] {
    let count = authors.len()
    let ncols = calc.min(count, 3)
    grid(
      columns: (1fr,) * ncols,
      row-gutter: 1.5em,
      ..authors.map(author => align(center)[
        #author.name \
        #author.affiliation \
        #author.email
      ])
    )
  }

  if date != none {
    align(center)[#block(inset: 1em)[
      #date
    ]]
  }

  if abstract != none {
    block(inset: 2em)[
      #text(weight: "semibold")[Abstract] #h(1em) #abstract
    ]
  }

  doc
}
#show: doc => conf(
  title: [Mathematical Modelling for Finance],
  pagenumbering: "1",
  cols: 1,
  font: "Google Sans",
  paper: "a4",
  fontsize: 14pt,
  margin: (x: 2em, y: 4em),
  doc,
)

#set heading(numbering: "1.")
#set math.equation(numbering: "(1)")

#outline()
#pagebreak()

= Linear Algebra
<linear-algebra-refresher-for-finance>
- #strong[Matrix-Vector Multiplication:] Used to calculate portfolio
  payoffs:
  $ upright("Payoff") = upright("Matrix") times upright("Portfolio Weights") $
  $
    mat(delim: "[", a, b; c, d) mat(delim: "[", x; y) = mat(delim: "[", a x + b y; c x + d y)
  $

- #strong[Determinant (Checking Linear Independence):] Used to check
  Market Completeness. If $det \( A \) eq.not 0$ (for a square matrix),
  the market is #strong[Complete];.

  - #strong[$2 times 2$ Matrix:] $det \( A \) = a d - b c$.

  - #strong[$3 times 3$ Matrix (Sarrus Rule):]

    $
      det mat(delim: "[", a, b, c; d, e, f; g, h, i)
      = a ( e i - f h ) - b ( d i - f g ) + c ( d h - e g )
    $

- #strong[Rank:] The number of linearly independent rows/columns.

  - #strong[Algorithm:] Use Gaussian elimination to create zeros below
    the diagonal. The Rank is the number of non-zero rows remaining.

  - #strong[Context:] If
    $upright("Rank") \( upright("Payoff Matrix") \) = upright("Total Number of States")$,
    the market is #strong[Complete];.

- #strong[Matrix Inversion:] Used in Markowitz optimization to find
  $Sigma^(- 1)$.

  - #strong[$2 times 2$ Matrix:]
    $ A^(- 1) = frac(1, a d - b c) mat(delim: "[", d, - b; - c, a) $

= One-Period Market Fundamentals
<one-period-market-fundamentals>
== Key Definitions
<key-definitions>
- #strong[Asset Payoff ($S_1$):] A random variable vector representing
  the value of securities at time $t = 1$ across different states
  $omega$.

- #strong[Portfolio ($theta$):] A vector representing the number of
  units held of each security.

- #strong[Market Completeness:] A market is complete if every possible
  payoff $X in bb(R)^N$ can be replicated by a portfolio $theta$ (i.e.,
  $S_1 theta = X$).

- #strong[Law of One Price (LOP):] If two portfolios have the same
  payoff in every state, they must have the same initial price.

- #strong[Arbitrage Opportunity:] A trading strategy $theta$ that
  satisfies either:

  + $V_0 \( theta \) lt.eq 0$ and $V_1 \( theta \) gt.eq 0$ (in all
    states), with strict inequality in at least one state.

  + $V_0 \( theta \) < 0$ and $V_1 \( theta \) gt.eq 0$ (in all states).

- #strong[State Price Vector ($psi$):] A vector of strictly positive
  prices for the Arrow-Debreu securities (pays 1 in state $i$, 0
  otherwise). LOP holds if a solution exists; No Arbitrage holds if a
  #strong[strictly positive] solution exists.

== Exercise: Finding Arbitrage Opportunities
<exercise-type-finding-arbitrage-opportunities>
#strong[Reasoning:] If the No-Arbitrage condition is violated, you must
construct a specific portfolio $theta$ that generates risk-free profit.

#heading(level: 3, numbering: none)[Scenario A: Violation of LOP
  (Redundant Assets)]
<scenario-a-violation-of-lop-redundant-assets>
- #strong[Detection:] You find that Asset C is redundant (linearly
  dependent on A and B) but priced inconsistently.

- #strong[Steps:]

  + Find the replication weights $x \, y$ such that
    $upright("Payoff") \( C \) = x dot.op upright("Payoff") \( A \) + y dot.op upright("Payoff") \( B \)$.

  + Compare the costs: Is $upright("Price") \( C \) > x P_A + y P_B$?

  + #strong[Arbitrage Strategy:] Sell the expensive one (Short C) and
    Buy the cheaper replicating portfolio (Buy $x$ of A and $y$ of B).

  + #strong[Result:] You pocket the price difference at $t = 0$, and the
    net payoff at $t = 1$ is exactly zero.

#heading(level: 3, numbering: none)[Scenario B: Negative State Prices]
<scenario-b-negative-state-prices>
- #strong[Detection:] You solve the system $S_1^T psi = S_0$ and find a
  state price $psi_k < 0$.

- #strong[Meaning:] The market is \"paying you\" to accept a payout in
  state $k$.

- #strong[Arbitrage Strategy:] You want to \"Buy\" state $k$. If Arrow
  securities aren't traded directly, find the portfolio $theta$ that
  solves $S_1 theta = upright(bold(e))_k$ (where $upright(bold(e))_k$
  has 1 in state $k$ and 0 elsewhere).

- #strong[Result:] The cost of this portfolio is $V_0 = psi_k < 0$
  (instant profit), and at $t = 1$ you receive 1 if state $k$ occurs (or
  0 otherwise), so you never lose money.

= Markowitz Mean-Variance (Matrix Approach)
<markowitz-mean-variance-matrix-approach>
== Key Definitions
<key-definitions-1>
- #strong[Mean-Variance Frontier:] The set of portfolios that minimize
  variance for a given level of expected return.

- #strong[Global Minimum Variance (GMV) Portfolio:] The portfolio on the
  frontier with the absolute lowest variance
  ($w_(G M V) prop Sigma^(- 1) upright(bold(1))$).

- #strong[Efficient Frontier:] The upper branch of the hyperbola (or the
  CML with risk-free asset) where investors maximize return for a given
  risk level.

- #strong[Tangent (Market) Portfolio:] The unique portfolio of risky
  assets that, when combined with the risk-free asset, lies on the
  Capital Market Line (CML) tangent to the risky frontier.

== Exercise: The Efficient Frontier
<exercise-type-the-efficient-frontier>
#heading(level: 3, numbering: none)[Formula (Risky Only)]
<formula-risky-only>
- Compute the 4 Constants using $mu$ and $Sigma^(- 1)$:
  $
    A = upright(bold(1))^T Sigma^(- 1) mu \, quad B = mu^T Sigma^(- 1) mu \, quad C = upright(bold(1))^T Sigma^(- 1) upright(bold(1)) \, quad D = B C - A^2
  $

- #strong[Optimal weights:] $w^(*) \( k \) = g + h k$, where:
  $
    g = 1 / D \( B Sigma^(- 1) upright(bold(1)) - A Sigma^(- 1) mu \) \, quad h = 1 / D \( C Sigma^(- 1) mu - A Sigma^(- 1) upright(bold(1)) \)
  $

- #strong[Frontier Equation (Hyperbola):]
  $ sigma^2 = frac(C k^2 - 2 A k + B, D) $

#heading(level: 3, numbering: none)[Formula (With Risk-Free $R_f$)]
<formula-with-risk-free-r_f>
- Excess return vector: $mu_e = mu - R_f upright(bold(1))$.

- Scalar $H = mu_e^T Sigma^(- 1) mu_e$.

- #strong[Frontier Equation (Line/CML):]
  $ bb(E) \[ R \] = R_f + sqrt(H) sigma $

= Hansen-Richard (SDF & Projections)
<hansen-richard-sdf-projections>
== Key Definitions
<key-definitions-2>
- #strong[Stochastic Discount Factor (SDF) / Pricing Kernel:] A random
  variable $M$ such that for any asset with payoff $X$ and price $P$,
  $P = bb(E) \[ M dot.op X \]$. It relates to state prices by
  $M \( omega \) = psi \( omega \) \/ p \( omega \)$.

- #strong[Orthogonal Projection ($upright(p r o j) \[ n divides A \]$):]
  The specific vector within a subspace $A$ (e.g., the span of traded
  assets) that is closest to vector $n$ in the mean-square sense.

- #strong[$R^(*)$:] The unique return in the payoff space that
  replicates the risk-free pricing rule (related to the projection of
  the SDF).

- #strong[$R^(e^*)$:] The excess return component, related to the
  un-hedgeable risk or the projection of the constant 1.

== Exercise: Computing $R^(*)$ and $R^(e^*)$
<exercise-type-computing-r-and-re>
#strong[Reasoning:] Instead of inverting covariance matrices, we use
projections to find the efficient frontier components.

+ #strong[Step 1: Projection of 1 onto Asset Space
    ($upright(p r o j) \[ 1 divides A \]$)]

  - Compute the moment matrix: $Q = bb(E) \[ S S^T \]$ (Note: usually
    un-centered moments).

  - Solve for coefficients $theta_A = Q^(- 1) bb(E) \[ S \]$.

  - The projection payoff is:
    $upright(p r o j) \[ 1 divides A \] = S dot.op theta_A$.

+ #strong[Step 2: Finding $R^(*)$]

  - Find the traded SDF $M^(*)$ (which is the projection of any valid
    SDF onto the asset space).

  - $ R^(*) = (M^(*))/ (bb(E) \[ \( M^(*) \)^2 \]) $

+ #strong[Step 3: Finding $R^(e^*)$]

  - Calculate $R^(e^*)$ using the projection of 1:
    $
      R^(e^*) = upright(p r o j) \[ 1 divides A \] - upright(p r o j) \[ 1 divides R^(*) \]
    $

  - Note that
    $
      upright(p r o j) \[ 1 divides R^(*) \] = frac(bb(E) \[ R^(*) \], bb(E) \[ \( R^(*) \)^2 \]) R^(*)
    $

  - Any frontier return is $R^(M V) = R^(*) + omega R^(e^*)$.

= Multiperiod & Derivative Pricing
<multiperiod-derivative-pricing>
== Key Definitions
<key-definitions-3>
- #strong[Risk-Neutral Measure ($bb(Q)$):] A probability measure under
  which the discounted price process $S_t \/ \( 1 + r \)^t$ is a
  martingale (constant expected value).

- #strong[Martingale Property:]
  $bb(E)^(bb(Q)) \[ S_(t + 1) divides cal(F)_t \] = S_t \( 1 + r \)$.

- #strong[American Option:] A derivative that can be exercised at any
  time $t lt.eq T$. Its value is the maximum of the immediate payoff and
  the continuation value.

- #strong[Barrier Option:] A path-dependent option. #emph[Knock-out]
  becomes worthless if the barrier is crossed; #emph[Knock-in] only
  becomes active if the barrier is crossed.

- #strong[Running Maximum ($M_t$):] The maximum price observed up to
  time $t$: $M_t = max_(0 lt.eq s lt.eq t) S \( s \)$.

== Exercise: Pricing with Trees (Backward Induction)
<exercise-type-pricing-with-trees-backward-induction>
#strong[Reasoning:] Calculate the \"risk-neutral\" probability $q$, then
work backward from maturity.

+ #strong[Step 1: Compute $q$ (Risk-Neutral Probability)]
  $ q = frac(\( 1 + r \) - d, u - d) $ Ensure $d < 1 + r < u$ for No
  Arbitrage.

+ #strong[Step 2: Backward Induction]

  - #strong[At $T$:] Value = Payoff (e.g., $\( K - S_T \)^(+)$).

  - #strong[At $t < T$:] Value = Discounted Expectation.
    $ V_t = frac(1, 1 + r) \[ q V_u + \( 1 - q \) V_d \] $

+ #strong[Step 3: Check for American Exercise]

  - At each node, compare $V_t$ (Continuation Value) vs. Intrinsic Value
    (Payoff if exercised now).

  - $"Price"_t = max \( upright("Payoff")_t \, upright("Continuation")_t \)$.

= Beta Pricing & Utility
<beta-pricing-utility>
== Key Definitions
<key-definitions-4>
- #strong[Beta ($beta_(i \, m)$):] Sensitivity of an asset's return to a
  factor.
  $beta = frac(upright("Cov") \( R_i \, R_m \), upright("Var") \( R_m \))$.

- #strong[Beta Pricing Equation:] $bb(E) \[ R \] = gamma + lambda beta$,
  where $lambda$ is the risk premium.

- #strong[Power Utility (CRRA):]
  $u \( w \) = frac(w^(1 - gamma), 1 - gamma)$ (for $gamma eq.not 1$) or
  $log \( w \)$ (for $gamma = 1$). $gamma$ is the coefficient of
  relative risk aversion.

== Exercise: Utility Maximization (One Period)
<exercise-type-utility-maximization-one-period>
#strong[Reasoning:] In a complete market, you can solve for the optimal
wealth $W_T$ that equates marginal utility to the state price density.

- #strong[First Order Condition:] $u' \( W_T \) = lambda L / B_T$ (where
  $L$ is the Radon-Nikodym derivative $d bb(Q) \/ d bb(P)$).

= Portfolio Optimization (Dynamic Programming & Martingale Method)
<portfolio-optimization-dynamic-programming-martingale-method>
This section deals with finding optimal strategies over time to maximize
utility of terminal wealth or consumption.

== Key Definitions
<key-definitions-5>
- #strong[Value Function $F \( t \, w \)$:] The maximum expected utility
  achievable from time $t$ onwards, given current wealth $w$.

- #strong[Bellman Principle (Dynamic Programming):] Breaks the problem
  into recursive steps:
  $
    F \( t \, w \) = max_alpha bb(E) \[ u \( dots.h \) + F \( t + 1 \, dots.h \) \]
  $

- #strong[Martingale Method:] Solves the static problem of optimal
  terminal wealth first, then finds the replicating strategy.

- #strong[State Price Density ($L$):] The ratio of risk-neutral to real
  probabilities:
  $ L = frac(d bb(Q), d bb(P)) = (q / p)^(N_u) (frac(1 - q, 1 - p))^(N_d) $

== Exercise: Optimal Portfolio Weight ($x^(*)$) in Binomial Model
<exercise-type-1-optimal-portfolio-weight-x-in-binomial-model>
#strong[Reasoning:] Determining the constant fraction of wealth invested
in the risky asset ($S$) to maximize power/log utility.

- #strong[Log Utility ($gamma = 1$):]
  $ x^(*) = frac(R, u - d) frac(p - q, q \( 1 - q \)) $ Where
  $R = 1 + r$. Condition for $x^(*) > 0$: $p > q$.

- #strong[Power Utility ($gamma eq.not 1$):]
  $ x^(*) = frac(R \( 1 - A \), A \( u - R \) + R - d) $ Where
  $A = (frac(q, 1 - q) frac(1 - p, p))^(1 \/ gamma)$. Note: The weight
  $x^(*)$ is constant over time and independent of wealth.

== Exercise: Optimal Terminal Wealth ($V^(*)$) via Martingale Method
<exercise-type-2-optimal-terminal-wealth-v-via-martingale-method>
#strong[Reasoning:] Finding the optimal wealth profile $V^(*)$ directly
using the state price density $L$.

- #strong[General Condition:]
  $
    u' \( V^(*) \) = lambda frac(L, B \( T \)) arrow.r.double.long V^(*) = \( u' \)^(- 1) (lambda frac(L, B \( T \)))
  $

- #strong[Log Utility Result:] $ V^(*) = w frac(B \( T \), L) $

- #strong[Power Utility Result:]
  $
    V^(*) = w \( 1 + r \)^T (p / q)^(N \( T \)) (frac(1 - p, 1 - q))^(T - N \( T \))
  $
  Where $N \( T \)$ is the number of \"up\" moves.

== Exercise: Optimal Consumption
<exercise-type-3-optimal-consumption>
#strong[Reasoning:] Balancing intermediate consumption $c \( t \)$ and
terminal wealth $W \( T \)$.

- #strong[First Order Conditions:]

  - For consumption at $t$:
    $u'_"intermediate" \( c \( t \) \) = lambda beta^(- t) frac(L \( t \), B \( t \))$.

  - For terminal wealth:
    $u'_"terminal" \( W \( T \) \) = lambda beta^(- T) frac(L \( T \), B \( T \))$.

- This implies the ratio of marginal utilities equals the ratio of state
  prices (discounted).
