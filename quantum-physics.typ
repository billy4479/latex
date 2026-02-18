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

Let $n_1$ the number of steps to the right and $n_2 = N - n_1$ the number of steps to the left. The
position of the particle is $x = ell (n_1 - n_2) = ell m$, where $ell$ is the step size and
$m colon.eq n_1 - n_2$.

After $N$ steps the probability of having taken exactly $n_1$ steps to the right is
$
  P(n_1) = binom(N, n_1) p^(n_1) q^(n_2)
$
and the mean number of steps to the right is
$
  angle(n_1) & = sum_(n_1 = 1)^N n_1 binom(N, n_1) p^(n_1) q^(N - n_1) = p N \
  angle(x) & = ell (angle(n_1) - angle(n_2)) = N(p - q) ell \
  angle(x^2) - angle(x)^2 & = 4 N p q ell^2
$

Note that the standard deviation grows with a factor of $N^(1/2)$.
This factor of $1/2$ is independent of the distribution of the walk and is also independent of the
dimension of the walk.

This behavior breaks down in a few cases: when the variance is not finite and when we introduce a
critical phenomenon (like in self-avoiding walks).

== Maxwell distribution

In an ideal dilute gas there is no interaction between the molecules.

Maxwell made the following assumptions: $rho(arrow(v))$ is a function of the modulus of the velocity
squared and that it depends on the product of some functions of the three components.

Given these assumptions Maxwell's hypothesis was that
$
  rho (arrow(v)) = c e^(- a/2 v_x^2) + e^(- a/2 v_y^2) + e^(- a/2 v_z^2)
$

We start by computing the normalization constant $c$. Since $rho$ is a probability we need
$
  integral.triple dd(x, y, z) rho(arrow(v)) = 1
$
But this is the product of three Gaussian integrals, which gives us
$
  c ((2 pi)/a)^(3/2) = 1 ==> c = (a / (2 pi))^(3/2)
$

Computing the moments (by noticing that $rho$ is Gaussian) we get that
$
    angle(v_x) & = 0 \
  angle(v_x^2) & = 1/a
$

Experimentally we know that $sqrt(angle(v_x^2)) approx 100 tilde 1000 "m"/"s"$

Now we consider also the probability over position, which it's safe to assume it's uniform.
$
  rho(arrow(r)) = 1/V
$

Then the joint probability distribution is
$
  rho(arrow(v), arrow(r)) = 1/V (a / (2 pi))^(3/2) e^(- a/2 v_x^2) + e^(- a/2 v_y^2) + e^(- a/2 v_z^2)
$

When the gas is inside a chamber with a piston on the positive $x$ direction and a molecule hits the
piston we get that the momentum on the $x$ axis gets reversed, therefore $Delta p_x = -2 m v_x$.
Since momentum is conserved, the piston absorbs the momentum from the particle.

By the law of impulse we know that $F = dv(p, t)$. We now look at the particles with velocity
$[v_x, v_x + dd(v)_x]$. For a particle with that velocity to hit the wall we need it to be
$ell = v_x dd(t)$ from the wall, otherwise it will not hit in time: this means that the particles
which hit the piston in $dd(t)$ are all located in a volume of $v_x dd(t) A$.

This gives us that, given the number of particle in such volume at that velocity $N$,
$
  dd(p)_x = N/V v_x dd(t) A dot.op 2 m v_x
$

We can then integrate this from $0$ to $infinity$ to take in account all the (positive) velocities
$
  F & = integral^infinity_0 rho(v_x) dd(v_x) [N/V A dot.op 2 m v^2_x] \
    & = N/V A dot.op 2 m 1/2 angle(v_x^2)
$
Giving us that
$
  P = F/A = N/V dot.op m angle(v_x^2)
$

We can substitute the kinetic energy such that
$
  P V = 2/3 U
$
the $3$ comes from the fact that we consider all $3$ components in the energy.

=== Adiabatic expansion

We keep the temperature constant, we have:
$
  P dd(V) + V dd(P) = 2/3 dd(U)
$
which we combine with
$
  dd(U) = - P dd(V)
$
to get
$
  P dd(V) + V dd(P) = - 2/3 P dd(V) & ==> 5/3 dd(V)/V + dd(P)/P = 0 \
                                    & ==> P V^(5/3) = "constant"
$

=== What is $a$?

Confronting the law of ideal gasses with the Maxwell distribution we have that
$
  a = m/(k_B T) = (m cal(N)_A)/(R T)
$

Giving that
$
  rho(arrow(v)) = (m/(2 pi k_B T))^(3/2) exp(- (m v^2)/(2 k T))
$

== Entropy

$
  H = - k sum_n p_n log p_n = k angle(log 1/p_n)
$
where $k$ is arbitrary, it is used to scale the logarithm (in CS we want to get to $log_2$, in
thermodynamics is $k_B$).

We note that
+ $H >= 0$.
+ $H = 0 <==> exists n^*$ s.t. $p_(n^*) = 1$ and all other $p_n = 0$.
+ $p_n = 1/N <==> H = log N$, uniform distributions have the largest entropy.
+ Let $x, y$ independent, then $H_(x, y) = H_x + H_y$, if $x, y$ not independent
  $H_(x, y) <= H_x + H_y$.
+ Computable by composition

In the continuous case with $x in RR^d$ and pdf $rho(x)$ we consider $d$-dimensional boxes of size
$(Delta x)^d$ and let $x_n$ be the center of the $n$-th box and $p_n$ its probability.

Then
$
  p_n approx rho(x_n) (Delta x)^d
$
which gives us
$
  H_(Delta x) & = - sum_n rho(x_n) (Delta x)^d [ log rho (x_n) + d log Delta x] \
              & = - integral dd(x) rho(x) log rho(x) - dd(log Delta x)
$
note that the constant on the right depending on $Delta x$ diverges as $Delta x$ goes to $0$,
however, since it does not depend on $rho$, we usually just ignore it and compute the continuous
entropy as
$
  H_"cont" = - integral dd(x) rho(x) log rho (x)
$

=== Maximum entropy principle

Assume that the system is in some state $n in {n}$.
Assume also we have some observables of our system $A_r (n)$ for $r = 1, ..., R$. Call $tilde(A_r)$
the mean of $A_r$.

Then the least biased probability distribution over events is, given the constraints, the one which
maximizes entropy.

The maximization problem then is to maximize entropy given that
$
  sum_n p_n A_r (n) = tilde(A)_n wide forall r in {1, ..., R} \
  sum_n p_n = 1
$

We can just use Lagrangian multipliers to get
$
  phi.alt = - sum_n p_n log p_n - alpha (sum_n p_n - 1)
  - sum^R_(r = 1) lambda_r (sum_n p_n A_r (n) - tilde(A)_r)
$
giving that
$
  p_n = 1/Z e^(- sum_r lambda_r A_r (n)) wide "where" Z = sum_n p_n
$
This distribution will always be of the exponential family.

Note that $Z$ depends on lambda as well, we call it the partition function:
$
  Z = sum_n exp(- sum^R_(r = 1) lambda_r A_r (n))
$
also note that
$
  - pdv(, lambda_r) log Z = angle(A_r) \
  pdv(, lambda_r, lambda_s) log Z = underbrace(
    (A_r A_s) - angle(A_r) angle(A_s),
    "covariance"
  )
$
we can recover these formulas from computing the derivative of
and since the covariance matrix is positive semi-definite, we get that $log Z$ is convex.
