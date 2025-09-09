#import "lib/template.typ": template

#show: template.with(
  title: "Mathematical Modelling for Finance",
  author: "Giacomo Ellero",
  date: "A.Y. 2025/2026",
)

= One-period models

In this kind of models we have that $t in {0, 1}$.
We consider $N $ securities $S_j$ and $B$ being the risk free asset
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
  cal(M) = mat(-1, -S_1 (0), ..., -S_N (0);
    1+r, S_1 (1)(omega_1), ..., S_N (1)(omega_1);
    dots.v, dots.v, dots.down, dots.v;
    1+r, S_1 (1)(omega_k), ..., S_N(1)(omega_k)
  )
$
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
  V_theta (1)(omega_k) = S(1)(omega_k) dot theta
$

