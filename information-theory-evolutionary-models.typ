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

= Compression

#definition(title: [Entropy rate])[
  Given a stochastic process $cal(X) = {X_i}$, then its entropy rate is
  $
    H(cal(X)) = lim_(n -> oo) 1/n H(H_1, ..., H_n)
  $
]

Entropy gives us a lower bound: an encoded message can't be shorter than $n H(X)$.

There are various classes of codes:
/ Non-Singular: Each symbol in the source is mapped to a different symbol in the output
/ Uniquely Decodable: Even when encoded words are concatenated into a string, there is an unique way
  to decode the message.
/ Instantaneous: Even when encoded words are concatenated into a string, we can start decoding the
  message without reading the whole string. We have this when no encoded word is a prefix of another
  encoded word.

#theorem(title: [Kraft inequality])[
  For any instantaneous code with an alphabet of size $D$, the encoded word length
  $ell_1, ell_2, ..., ell_m$ must satisfy
  $
    sum_(i = 1)^m D^(-ell_i) <= 1
  $

  Conversely, if the inequality holds, there must exist an instantaneous code for those word
  lengths.
]


#theorem[
  The expected length $L$ of any instantaneous code of alphabet of size $D$ for a random variable
  $X$ is
  $
    L >= H_D (X)
  $
  where $H_D$ is the entropy with logarithm in base $D$.

  It holds with equality when $D^(ell_i) = p_i$ where $p_i$ are the probabilities of a $D$-adic
  distribution (i.e. where each probability is equal to $D^(-n)$ for some $n in NN$).
]

To find the best coding we want to minimize
$
  EE[ell] = sum^n_(i = 1) p(ell_i) ell_i \
  "s.t." sum^n_(i = 1) D^(-ell_i) <= 1
$
where $p_(ell_i)$ is the probability that we use a code of length $ell_i$.

We can solve with Lagrangian multipliers to get
$
  EE[ell]_"opt" = -sum^n_(i = 1) p(ell_i) log_D p(ell_i) = H_D (X)
$

#example(title: [Shannon codes])[
  In Shannon codes the length of each symbol is exactly $ell_i = ceil(-log_D p(ell_i))$.
]

#example(title: [Huffman codes])[
  Given the probabilities of the input our algorithm takes the $D$ input symbols with the lowest
  probability and adds them to the leaves of a tree, then it replaces the $D$ input symbols with a
  new symbol which has the sum of probabilities the taken symbols. If this new symbol is chosen
  again the whole tree is attached as a leaf.

  Eventually we will have just one root node and a tree which we can use to construct code words. In
  this constructions low-probability inputs will be mapped to the longest codes.
]

= Communication

A communication channel is a probability transition matrix which outputs the probability of seeing
an output $y in Y$ given that the channel received an input $x in X$.

The channel capacity is the maximum information taken over the possible distributions of $X$.
$
  C = max_(p(x)) (H(Y) - H(Y | X))
$

Define the conditional probability of error
$
  lambda_i = prob(g(Y^n) != i | X^n = x^n (i))
$
where $g$ is the decoding function and $x^n$ is the encoding function.
