#import "lib/template.typ": *
#import "lib/theorem.typ": *
#import "lib/utils.typ": *

#show: template.with(
  titleString: "Quantum and Statistical Physics",
  author: "Giacomo Ellero",
  date: "A.Y. 2025/2026",
)

#show: thm-init

= Mathematical Tools

== TODO: Curse and blessing of dimensionality

== TODO: WAVES

== Fourier

=== Fourier series

Let $f: RR -> RR$ be a periodic function, that is $f(t) = f(t + T)$ for some period $T$. Define the
frequency as $omega = 2pi/T$

#theorem(title: [Fourier Series on $RR$])[
  Let $f(t)$ be a periodic function such that $integral_0^T f(t)^2 dd(t)$ is finite.
  Define
  $
    f_N (t) = sum^N_(n = 0) [a_n cos(n omega t) + b_n sin(n omega t)]
  $
  where
  $
    a_p & = 2/T integral_0^T f(t) cos(p omega t) dd(t) \
    b_p & = 2/T integral_0^T f(t) sin(p omega t) dd(t)
  $
]

#proof[
  We will take for granted that such series of functions $f_N$ exists. We will prove the formula to
  compute the coefficients.

  Substitute $f_infinity (t)$ in the formula.
  $
    a_p & = 2/T integral_0^T sum^infinity_(n = 0) [a_n cos(n omega t) + b_n sin(n omega t)]
          cos(p omega t) dd(t) \
        & = 2/T sum^infinity_(n = 0) [integral_0^T a_n cos(n omega t) cos(p omega t) dd(t)
            + integral_0^T b_n sin(n omega t) cos(p omega t) dd(t)]
  $

  First we invoke the following trigonometry identities:
  $
    cos(p omega t) cos(n omega t) &= 1/2 [cos((p - n) omega t) + cos((p + n) omega t)]\
    cos(p omega t) sin(n omega t) &= 1/2 [sin((p + n) omega t) + sin((p - n) omega t)]
  $
  Then note that integrating a periodic function on its period gives $0$ all the times, the only
  exception is when $p = n$ (since $cos(0) = 1$ and $sin(0) = 0$).

  We can then continue our derivation of $a_p$ by removing all the terms of the sum where $p != n$:
  $
    a_p & = 2/T [integral_0^T a_p 1/2 (1 + cos (2n omega t)) dd(t)
      + integral_0^T b_n 1/2 (0 + sin(2n omega t) dd(t))] \
    & = 1/T integral_0^T a_p (1 + 0) + b_p (0 + 0) dd(t) = 1/T integral_0^T a_p dd(t) = a_p
  $
  where we used the fact that integrating a periodic function on its period gives $0$.

  We then repeat the same procedure for $b_p$.
]

#corollary(title: [Fourier series on $CC$])[
  A periodic function $f: RR -> CC$ is a function which is periodic on both the real and imaginary
  component.

  To compute the Fourier series we could just use the formula on both parts, however we can simplify
  by using Euler's formula.

  $
                & f(t) = sum^infinity_(n = 0) f_n e^(i n omega t) dd(t) \
    "with" wide & f_p = 1/N integral_0^T f(t) e^(-i p omega t) dd(t)
  $
]

=== Fourier Transform

Now consider a generic $f: V -> CC$ where $V = RR$ (but could be any vector space).
Assume $f in C^infinity$ and that
$
  integral_(-infinity)^infinity abs(f(x)) x^k dd(x) wide "exists" forall k
$
meaning that $f(x)$ decays at infinity faster than any power law.

#definition(title: "Fourier Transform")[
  The Fourier transform of a function $f: V -> CC$ satisfying the requirements above is a function
  $tilde(f): V -> CC$ defined as
  $
    tilde(f) (k) = 1/sqrt(2pi) integral_(-infinity)^infinity f(x) exp(-i k x) dd(x)
  $
]

#example(title: [Fourier transform of Gaussian])[
  Let $f(x) = exp(- x^2/(2 sigma^2))$. Compute its Fourier transform.
]

#solution[
  Using the definition we get
  $
    tilde(f) (x) & = 1/sqrt(2 pi) integral exp(- x^2 /(sigma^2)) exp (-i k x) dd(x) \
    & = 1/sqrt(2 pi) integral exp(- x^2 /(sigma^2) -i k x) dd(x) \
    & = 1/sqrt(2 pi) integral exp(- 1/(2 sigma^2) (x^2 + 2 i k x sigma - k^2 sigma^4 + k^2 sigma^4)) dd(x) \
    & = 1/sqrt(2 pi) integral exp(- 1/(2 sigma^2) (x + i k sigma^2)^2 - (k^2 sigma^2)/2) dd(x) \
    & = 1/sqrt(2 pi) exp(- (k^2 sigma^2)/2) integral exp(- 1/(2 sigma^2) (x + i k sigma^2)^2) dd(x) \
    & = 1/sqrt(2 pi) exp(- (k^2 sigma^2)/2) integral exp(- y^2/(2 sigma^2)) dd(x)
    & "where" y = x + i k sigma^2 \
    & = 1/sqrt(2 pi) exp(- (k^2 sigma^2)/2) sqrt(2 pi sigma^2) & "by contour integration" \
    & = sigma exp(- (k^2 sigma^2)/2)
  $
]

=== Inverse Fourier transform

#theorem(title: [Inverse Fourier transform])[
  Let $tilde(f)$ be the Fourier transform of $f$, then
  $
    f(x) = 1/(sqrt(2 pi)) integral_(-infinity)^infinity tilde(f)(k) exp(i k x) dd(k)
  $
]

#proof[
  Consider the auxiliary function
  $
    h_sigma (x) = integral dd(k)/sqrt(2 pi) tilde(f)(k) exp(- (k^2 sigma^2)/2) exp(i k x)
  $
  Note that the theorem is equivalent to showing that $h_sigma -> f$ as $sigma -> 0$.

  Substitute the definition of the Fourier transform in $h_sigma$:
  $
    h_sigma (x) & = integral dd(k)/sqrt(2 pi) exp(- (k^2 sigma^2)/2) exp(i k x)
                  integral dd(y)/sqrt(2 pi) f(y) exp(-i k y) \
                & = integral dd(y)/sqrt(2 pi) f(y) integral dd(k)/sqrt(2 pi)
                  exp(- (k^2 sigma^2)/2) exp(i k (x-y)) \
                & = integral dd(y)/sqrt(2 pi) f(y) dot.op
                  sigma exp(- ((x - y)^2)/(2 sigma^2))       & "FT of Gaussian" \
                & = integral dd(u)/sqrt(2 pi) f(x + sigma u) dot.op
                  sigma exp(- ((sigma u)^2)/(2 sigma^2))     &  y = x + sigma u \
                & = integral dd(u)/sqrt(2 pi) f(x + sigma u) dot.op
                  sigma exp(- u^2/2) ->^(sigma -> 0) f(x)
  $
]

#proposition(title: [Derivation of FT])[
  Let $g(x) = f'(x)$ then $tilde(g) (x) = i k tilde(f)(x)$.

  Similarly, let $g(x) = -i x f(x)$, then $tilde(g)(x) = tilde(f)' (x)$.
]

=== Fast Fourier Transform (FFT)

Suppose we now want to compute numerically the FT of a function $f$. Assume that $f$ is negligible
outside the interval $[a, a + L]$, then let $x_n = a + (n L)/N$ for $n in {0, 1, ..., N-1}$, and
define $f(x_n) = f_n$

$
  tilde(f) (k) & = 1/sqrt(2pi) integral_a^(a + L) f(x) exp(-i k x) dd(x) \
               & approx L/n 1/sqrt(2 pi) sum^(N - 1)_(n = 0)
                 f_n exp(-i k (a + (n L)/N))
$
But $tilde(f)(k + (2 pi N)/L) = tilde(f)(k)$, therefore we can compute $tilde(f)(k)$ for
$k in [0, (2 pi N)/L]$. Let $k = (2 pi p)/L$ and $tilde(f)_p = tilde(f)_p ((2 pi p)/L)$.

Then (substitute $k = (2 pi p)/L$)
$
  tilde(f)_p = exp(-i k a)/sqrt(2 pi) L/n
  underbracket(sum^(N - 1)_(n = 0) f_n exp(- i (2 pi p n)/N), S_p)
$
but this is $bigO(N^2)$ to compute.

The trick is to group the terms of the sum $S_p$ in a smart way.
Assuming $N$ is even, let
$
  E_p & = sum^(N/2 - 1)_(n = 0) f_(2n) exp (-i (2 pi p)/N 2n) \
  O_p & = sum^(N/2 - 1)_(n = 0) f_(2n + 1) exp (-i (2 pi p)/N (2n + 1))
$
and let $p = N/2 dot.op p'$ for $p' in {0, 1, ..., N/2-1}$.
Then
$
  S_(N/2 + p') = E_p - exp(-i (2 pi)/N p') O_p
$
therefore by computing the even and odd part of the sum for $N/2$ point we can reuse the sum terms
for the second half. This can be done recursively, subdividing $E_p$ and $O_p$ again and again,
giving us a final complexity of $bigO(n log n)$.

=== Convolutions

Recall that given two functions $g, h$ their convolution $f$ is defined as
$
  f(x) = (g star h)(x) = integral g(y) h(x - y) dd(y)
$

#theorem(title: [Parseval-Plancherel])[
  $
    f(x) = (g star h)(x) <==> tilde(f)(k) = sqrt(2 pi) tilde(g) (k) tilde(h) (k)
  $
]

#proof[
  $
    tilde(f)(k)
    & = integral dd(x)/sqrt(2 pi) exp(-i x k) integral g(y) h(x - y) dd(y) \
    & = integral dd(y) integral dd(x)/sqrt(2 pi) exp(-i k (x - y)) exp(- i k y) g(y) h(x - y) \
    & = integral dd(y) integral dd(u)/sqrt(2 pi) exp(-i k u) exp(- i k y) g(y) h(u) & u = x - y\
    & = sqrt(2 pi) tilde(g)(k) tilde(h)(k)
  $
]

== Random Walks

