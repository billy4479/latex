#import "@preview/diatypst:0.9.1": *
#import "lib/utils.typ": *

#show: slides.with(
  title: "Introduction to Convolutional Codes", // Required
  subtitle: "",
  date: "17/04/2026",
  authors: "Giacomo Ellero",
  // layout: "small",
  toc: false,
  count: "number",
)

#set heading(numbering: "1.")
#let bu(content) = $bold(upright(content))$

== Get the slides


- #link(
    "https://excalidraw.com/#json=p1mq3nBmn0rVnxTI1v4vx,2za5GXKqbnCGWyyJv0U8_A",
    [Figure 1, 2 and 4],
  )

Download the slides from here:
#align(center)[
  #image(
    "assets/infoth-research/qr.png",
    width: 45%,
  )
]


= Recap

== Recap on Error Control Codes

- These codes are a way to attempt to *detect* (and in some cases correct) *errors which can occur
  during transmission* of messages over noisy channels.
- These codes, contrary to other encodings we saw (Shannon, Huffman...), *increase the size* of the
  output compared to the input.

== Recap on Hamming codes

- This is one of the first ECCs to be discovered (1940). We've already seen it in class.
- Consider all the non-null binary strings on length $m$: there are $n := 2^m - 1$ of them.
- We then consider a $m times n$ binary matrix $M_H$ such that all its columns are distinct and
  non-zero.
- By the rank-nullity theorem, the null-space of $M_H$ has dimension $k := n - m$: our codewords $c$
  will come from this space, such that $c M_H = 0$.
- Each codeword $c$ is $n$ bits long: the first $k$ bits represent the actual message, while the
  other $m$ bits are the so called parity bits.

#pagebreak()

For each encoded message we have
$
  cases(
    delim: #none,
    m wide & "parity bits",
    n := 2^m - 1 wide & "total number of bits",
    k := n - m wide & "data bits"
  )
$

- Given that both the sender and the receiver have both the same matrix $M_H$, the sender needs to
  solve a linear system to find the parity bits and the receiver needs to perform the multiplication
  $c M_H$ to detect any errors.
- If decoding gives a non-zero result, then we can use it to figure out where the error occurred and
  fix it.

#pagebreak()

- Standard Hamming codes fix only one error per message. They can still detect if there are two
  errors but they cannot fix them.
- If we want to encode longer messages we need to break them into "blocks" of $k$ bits.
- Hamming code is a *block code*, there are many other codes which work in a similar manner.

= Convolutional Codes

== Introduction

- Introduced in 1955 by Elias and intended as an alternative to block codes.
- Convolutional codes have *memory*: they take into account the previous $m$ messages to encode the
  next one.
- We can classify CC using three integers $(n, k, m)$ where $n > k$.
- CCs can be implemented on a *circuit* with $k$ inputs, $n$ outputs and $m$ memory cells.
- Note that when $k = 1$ the information doesn't need to be divided into blocks and can be streamed
  continuously.

$
  cases(
    delim: #none,
    n wide & "output bits",
    k wide & "input bits",
    m wide & "dependence on past input"
  )
$

== A first circuit

#figure(
  image("./assets/infoth-research/circuit-1.png", width: 65%),
  caption: [Example $(2, 1, 3)$ circuit. Colors represent which input bit is transmitted:
    #text(fill: rgb("#1971c2"), $u_t$),
    #text(fill: rgb("#2f9e44"), $u_(t-1)$),
    #text(fill: rgb("#f08c00"), $u_(t-2)$),
    #text(fill: rgb("#9c36b5"), $u_(t-3)$).
    $square$ are memory cells, $plus.o$ are binary sums.
  ],
)<fig:circuit-1>

In this encoder $bu(u) = (u_0, u_1, ...)$ is the information sequence and $bu(v)^((1))$ and
$bu(v)^((2))$ are the two output sequences.

Memory cells output their previous value and store the input for the next round.
Sums just perform the normal binary sum.
*These are the only allowed components in a CC circuit.*

== Convolutions and impulse responses

Since the circuit is linear, its output can be written as a *discrete convolution* of the input with
the *impulse responses* $bu(g)^((j))$.
$
  bu(v)^((j)) = bu(u) * bu(g)^((j))
$

The *convolution* is defined as follows:
$
  v_ell^((j)) = sum^m_(i = 0) u_(ell - i) g_i^((j)) wide
  cases(
    delim: #none,
    "for all" ell >= 0 "and",
    u_(ell - i) := 0 "if" ell - i < 0
  )
$

While the *impulse responses* can be obtained by feeding the first $m + 1$ values of the sequence
$bu(u) = mat(1, 0, 0, 0, dots.c)$ to the circuit and recording the values of the output.

For the circuit in the previous slide we have
$
  bu(g)^((1)) & = mat(1, 0, 1, 1) \
  bu(g)^((2)) & = mat(1, 1, 1, 1) \
$

== Matrix representation

The outputs of the circuit are then *multiplexed*, in the circuit in Figure 1 we would have
$
  bu(v) = mat(v_1^((1)), v_1^((2)), v_2^((1)), v_2^((2)), dots.c)
$

But, since the convolution is a linear operation, the whole encoding process can be expressed as a
matrix operation.

$
  bu(v) = bu(u G) wide "where" \
  G = mat(
    g_0^((1)), g_0^((2)), g_1^((1)), g_1^((2)), dots.c, g_m^((1)), g_m^((2)), , , , ;
    , , g_0^((1)), g_0^((2)), g_1^((1)), g_1^((2)), dots.c, g_m^((1)), g_m^((2)), , ;
    , , , , g_0^((1)), g_0^((2)), g_1^((1)), g_1^((2)), dots.c, g_m^((1)), g_m^((2));
    , , , , , , dots.down, , , , dots.down;
  )
$

$bu(G)$ is a _semi-infinite_ matrix, since the size of the input sequence is arbitrary.
All its rows are the same but they are shifted by $n$ (in this case $n = 2$).

== A second circuit

#figure(
  image("./assets/infoth-research/circuit-2.png", width: 60%),
  caption: [Example $(3, 2, 1)$ circuit. Color represent which input bit is transmitted:
    #text(fill: rgb("#1971c2"), $u_t^((1))$),
    #text(fill: rgb("#2f9e44"), $u_t^((2))$),
    #text(fill: rgb("#f08c00"), $u_(t-1)^((1))$),
    #text(fill: rgb("#9c36b5"), $u_(t-1)^((2))$).
  ],
)

Here the information sequence $bu(u) = mat(u_0^((1)), u_0^((2)), u_1^((1)), u_1^((2)), ...)$
enters the encoder two bits at the time ($k = 2$).

== Matrix representation

This time we need more impulse generators, in fact we need $k times n$ of them, each one is a $m+1$
sized vector. Let $bu(g)_i^((j))$ be the generator sequence corresponding to input $i$ and output
$j$.

In general the encoding process is still a linear map $bu(u) = bu(u G)$ where the *generator
matrix* $bu(G)$ is
$
  bu(G) = mat(
    G_0, G_1, dots.c, G_m, , , ;
    , G_0, G_1, dots.c, G_m, , ;
    , , G_0, G_1, dots.c, G_m, ;
    , , , dots.down, , , , dots.down;
  )
  \ "where" wide
  G_ell = mat(
    g_(1, ell)^((1)), g_(1, ell)^((2)), dots.c, g_(1, ell)^((n));
    g_(2, ell)^((1)), g_(2, ell)^((2)), dots.c, g_(2, ell)^((n));
    dots.v, dots.v, dots.down, dots.v;
    g_(k, ell)^((1)), g_(k, ell)^((2)), dots.c, g_(k, ell)^((n));
  )
$

== Polynomial representation

It is convenient to represent each information sequence as a polynomial instead:
$
  bu(u)(D) = u_0 + u_1 D + u_2 D^2 + ...
$
In this notation, the encoding process becomes
$
  bu(v)(D) = [bu(u)^((1)) bu(G)](D^n) + D[bu(u)^((2)) bu(G)](D^n) + dots.c
  + D^(n - 1)[bu(u)^((n)) bu(G)](D^n)
$
where $bu(G)(D)$ is a matrix of polynomials and is referred to as the *transfer function matrix*.

The indeterminate $D$ can be seen as a *delay operator*: powers of $D$ denote the number of times
the bit is delayed with respect to the initial bit in the sequence.

// == State Machine representation
//
// The encoder circuit can also be represented as a state machine. This state machine has $2^K$
// possible states, where $K$ is the number of bits stored in the encoder memory cells.
//
// #figure(
//   image("./assets/infoth-research/state-diagram-1.png", width: 65%),
//   caption: [
//     State diagram for the encoder in Figure 1. On each edge we write
//     the input received at step $ell$ and the output of the circuit:
//     $u_ell \/ v^((1))_ell v^((2))_ell$.
//   ],
// )

== Systematic codes

Systematic codes are a subset of possible codings which in which *the first $k$ bits of the output
are the same of the input*.

This is both easier to implement on the encoding side, since it usually requires less hardware, and
on the decoder side, since *the information content can be recovered* from the codeword *without an
inverter circuit*.
The existence of an inverter circuit is not trivial: there need to exist an $n times k$ matrix
$bu(G)^(-1)(D)$ such that
$
  bu(G)(D) bu(G)^(-1)(D) = bu(I)_k D^ell wide "for some" ell >= 0
$

If we have a systemic code, the transfer function matrix becomes
$
  bu(G)(D) = mat(bu(I)_k, cal(G)(D))
  wide "where"
  cal(G) = mat(
    bu(g)^(k+1)_1 (D), dots.c, bu(g)^(n)_1 (D);
    bu(g)^(k+1)_2 (D), dots.c, bu(g)^(n)_2 (D);
    dots.v, dots.down, dots.v;
    bu(g)^(k+1)_1 (D), dots.c, bu(g)^(n)_1 (D);
  )
$

= Distance Properties

== Minimum free distance

The performance of a convolutional code depends both on the decoding algorithm used and on its
distance properties. The most important distance measure of a CC is the *minimum _free distance_*
denoted by $d_"free"$.

$
  d_"free" & := min {d(bu(v'), bu(v'')): bu(u') != bu(u'')} \
           & = min {w(bu(v') + bu(v'')) : bu(u') != bu(u'') } \
           & = min {w(bu(v)) : bu(u) != 0 } \
           & = min {w(bu(u G)) : bu(u) != 0 }
$
where $bu(v')$ and $bu(v'')$ are the codewords corresponding to the information sequences $bu(u')$
and $bu(u'')$. This means that $d_"free"$ is the minimum distance between any two codewords in the
code.

As for the distance function $d$ the usual way is to use the *weight* of a codeword $w$: this is the
number of non-zero bits in the codeword.

== Column distance function

This distance measure is very similar to the free distance, except it takes into account *only the
first $i$ bits of each sequence*.

Let $[bu(u)]_i$ denote the $i$-th truncation of the information sequence:
$
  [bu(u)]_i = ( & mat(delim: #none, u_0^((1)), u_0^((2)), dots.c, u_0^((k))), \
                & mat(delim: #none, u_1^((1)), u_1^((2)), dots.c, u_1^((k))), \
                & mat(delim: #none, dots.c), \
                & mat(delim: #none, u_i^((1)), u_i^((2)), dots.c, u_i^((k)))
                  )
$

Then the column distance function is defined as
$
  d_i & := min(d([bu(v')]_i, [bu(v'')]_i) : [bu(u')]_0 != [bu(u'')]_0) \
      & = min(w[bu(v)]_i : [bu(u)]_0 != 0)
$

#pagebreak()

Note that by definition $d_i$ is a non-decreasing function of $i$.

#figure(
  image("./assets/infoth-research/cdf.png", width: 50%),
  caption: [ Column distance function of a $(2, 1, 16)$ code.],
)

It can be shown that for "regular enough" codes $lim_(i -> oo) d_i = d_"free"$.

= Decoding

== Trellis diagram

In order to understand the algorithm we need to represent the encoder in a *trellis diagram*.
Trellis diagrams show the *evolution of state through time*, we choose branches depending on the
value of $u_i$.

#figure(
  image("./assets/infoth-research/trellis-diagram.png", width: 70%),
  caption: [Trellis diagram of Figure 1 with an input of size $L=5$.],
)


== Viterbi algorithm

This algorithm was invented in 1967 by Viterbi and it has been shown to be the decoding algorithm
which maximizes the likelihood of decoding the correct message over a noisy channel.

Consider an information sequence $bu(u)$ encoded to $bu(v)$ and sent through a _discrete memoryless
channel_: the receiver gets a sequence $bu(r)$ and wants to decode it.

Let us denote $M(bu(r) | bu(v))$ the *path metric*
$
  M(bu(r) | bu(v)) & := log prob(bu(r) | bu(v))
                     = sum_(i = 0)^(L + m - 1) log prob(bu(r)_i | bu(v)_i) \
                   & = sum_(i = 0)^(n(L + m) - 1) log prob(r_i | v_i)
$

We also define the *partial path metric* $M([bu(r) | bu(v)]_j)$ as the path metric computed up to
the first $j$ branches.

#pagebreak()

+ We assume that the encoder is initialized with all zeros.
+ The idea is that the decoder keeps track of its guess of the state of the encoder. To each one of
  the state it has assigned a *metric*, a score.
+ At each step $t$ we receive $bu(r)_t$ which is a sequence of $n$ bits.
+ We look at the trellis diagram and in particular at all the arrows which point into into the
  current time $t$:
  - We look at all the possible outputs $bu(v)_t$ which the encoder could generate.
  - For each one of them we *compute the partial path metric*: first we compute the branch metric,
    which is the log likelihood of receiving $bu(r)_t$ when the encoder sent $bu(v)_t$, then we add
    it to the metric of the encoder being in that precise state.
  - There will be two ways to get to the same state: we always consider the one with the best metric
    when we need to compute the next partial path metric.
+ Go to step 3 and repeat until the whole $t > L + m$, then follow the path with the best metric to
  get maximum likelihood message.


= Bibliography

== Bibliography

- Lin, Shu, and Daniel J. Costello, Jr. _Error Control Coding_. Englewood Cliffs, N.J.:
  Prentice-Hall, 1983.
- UConn HKN. _Digital Communications: Viterbi Algorithm_. YouTube, 2017,
  #link("https://www.youtube.com/watch?v=dKIf6mQUfnY").
