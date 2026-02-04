#import "lib/template.typ": *
#import "lib/theorem.typ": *
#import "lib/utils.typ": *

#show: template.with(
  titleString: "Information Theory & Evolutionary Models",
  author: "Giacomo Ellero",
  date: "A.Y. 2025/2026",
)

#show: thm-init

= Introduction

== Entropy
$
  log (1/(prob (X)))
$

Then entropy is
$
  H(X) = EE[log 1/(prob (X))]
$
Entropy is independent of the base of the logarithm (use change of base formula), it is just a
function of the distribution of $X$.

== KL Divergence
$
  D_(K L) (P, Q) = EE_P (log P(x)/Q(x))
$
Measures how inefficient it is to assume that the distribution is $Q$ while the true distribution is
$P$.

== t-Distributed Stochastic Neighbor Embedding (t-SNE)

It tries to preserve local distance (try to keep near what is already near). Not as reliable at high
distance.

For each point $x_i$ and for each neighbour $x_j$ compute $p_(j|i)$ which is the probability that,
when considering a Gaussian distribution centered at $x_i$, $x_j$ is picked.
Then we do the same for $p_(i|j)$ and define
$
  p_(i j) = (p_(j|i) + p_(i|j))/(2 N)
$

The $sigma$ for the Gaussian distribution considered above is chosen such that the entropy of the is
equal to a predefined entropy value. We can control this value adjusting the perplexity of the
embedding: this is a measure derived from the entropy which effectively regulates how many
neighbours are considered.

Then we compute $q_(i j)$ which is the distribution of points on the low-dimensional space, this is
a Student-$t$ distribution with 1 degree of freedom. This $q$ is used to measure similarities
between points in the low-dimensional space.

The final step is to assign the coordinates in the low-dimensional space by minimizing the KL
divergence between $P$ and $Q$.
