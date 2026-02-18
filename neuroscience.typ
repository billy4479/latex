#import "lib/template.typ": *
#import "lib/theorem.typ": *
#import "lib/utils.typ": *

#show: template.with(
  titleString: "Mathematical Modelling for Neuroscience",
  author: "Giacomo Ellero",
  date: "A.Y. 2025/2026",
)

#show: thm-init

= Neural coding

We choose a certain neuron and, when a stimulus is shown to the subject, we record the activity of
that neuron.
We will try to answer the following questions:
- How much information is contained in a single neuron (or a population of neuron) response? How
  many neurons do I need to obtain a certain information?
- Is there an optimal way of transmitting information?
- Are neurons close to this optimal way?

== Anatomy of a neuron

/ Soma: Body of the cell, contains the nucleus and various organelles.
/ Dendrites: Branches which come off the soma which receive the signals from other neurons.
/ Axon: A long branch which transmits signals off the neuron.

The number of synapses per neuron varies widely depending on the type of neuron: it can go from as
little as 4 to 150000.

Neurons are *electrically charged*: at rest the membrane potential is $-70"mV"$. On the cell membrane
there are ions channel which help keep the potential in balance, the main actors are $"Na"^+$ and
$"K"^+$ channels.

The *action potential* is a rapid electrical signal or impulse and it's caused by a change in ions
concentration in the membrane. This signal is then transmitted through the axon to other neurons or
muscles. The potential difference between the resting state and the peak of the action potential is
significant: the signal can travel very long without being attenuated.

*Synapses* are the junctions between neurons: when a synapse on an axon receives an action potential
a voltage-gated calcium channel opens and in turns triggers the release of neurotransmitters which
influence the post-synaptic neuron.

== Modelling neuron's activity

Neurons exhibit activity even when there is no external stimulus. We can use a raster plot to
illustrate neurons' activity.


#figure(
  image("./assets/neuroscience/raster-plot.png"),
  caption: [Raster plot: each row represents a trial; time is on the $x$ axis, stimulus occurs at
    $t= 0$; each line represents an action potential.],
)

As we can see stimuli induce brain activity, but responses are noisy.
A deterministic model is likely impossible, we use a probabilistic one based on Poisson processes
with a time dependent firing rate.

Let $n_T$ be the number of trials and $Delta t$ the bin size, then count the number of spikes in
each bin $n_s$ over all trials. We define the instantaneous firing rate (PSTH) as
$
  "PSTH" = n_s / (n_T Delta t)
$

Neurons have different purposes, each one might have a continuous or discrete firing rate depending
on the stimulus. An example of continuous firing rate is orientation sensitivity: depending on the
rotation of the stimulus the neuron fires according to a bell curve; see other examples in slides
001, page 18. Other times external stimuli cannot be mapped to a low-dimensional continuous function
and it is often sparse: only a small fraction of neurons fire given a stimulus and viceversa each
neuron responds only to a small fraction of stimuli.

=== Spike-Triggered Average

To look which neurons activate when we use *spike-triggered average* (STA).
Let $n$ be the number of spikes, $s(t)$ be a time-varying stimulus and $delta(t)$ be a neuron's
signal.
$
  rho(t) & = "spike train" = sum^n_(i = 1) delta(t - t_i) \
  C(tau) & = "STA" = 1/n sum^n_(i = 1) s(t_i - tau)
$

The spike train is the number of signals until $t$.

#proposition[
  $
    C(tau) = 1/angle(r)_"trial" Q_"rs" (- tau)
  $
]<prop:sta>


#proof[
  Let $angle(dot)_"trials"$ denote the average over the trials:
  $
    angle(rho(t))_"trials" = 1/N sum^N_(alpha = 1) rho^alpha (t)
  $

  Let us consider the average STA over the trials.
  $
    angle(C(tau)) & = angle(1/n sum^n_(i = 1) s(t_i - tau)) \
                  & approx^(T >> 1) 1/angle(n) angle(sum^n_(i = 1) s(t_i - tau))
  $
  This is because, over a large number of trials, the number of spikes will be constant.

  We continue by looking at the sum:
  $
    sum^n_(i = 1)
  $
  TODO: complete proof
]

=== Inter-Spike Interval

We define the *inter-spike interval* (ISI) as the time between spikes.
The coefficient of variation $"CV"_"ISI" = sigma/mu$ has been measured experimentally and it is
close to $1$

#proposition[
  Since $"CV"_"ISI" = 1$ experimentally, the ISI is well described by a Poisson process.
]

#proof[
  We will describe the neuron firing with an homogeneous Poisson process and show that then the CV
  is also 1.
  $
       P("spike in bin") & = r Delta t \
    P("no spike in bin") & = 1 - r Delta t
  $

  Then the probability of $n$ spikes in $T$ is distributed as Poisson
  $
    P_T (n) = ((r T)^n e^(- r T) ) / n!
  $

  Now we shift the time so that at $t_0 = 0$ we have a spike. We discretize time using bins of size
  $Delta t$.

  Then at some time $t_1$ another spike will occur and, because of our discretization, we will have
  that $t_1 in [t_0 + tau, t_0 + tau + Delta t]$.

  The $"ISI" = t_1 - t_0$. By our Poisson distribution we get
  $
    P(tau <= t_1 - t_0 < tau + Delta t) & = P_tau (n = 0) P_(Delta t) (n = 1) \
                                        & e^(-r tau) r Delta t
  $

  To compute the coefficient of variation of the ISI we need $mu$ and $sigma$:
  $
    mu = angle(tau) & = integral_0^infinity tau n r e^(- tau r) dd(tau) = 1/r \
    sigma^2 = angle(tau^2) - angle(tau)^2 & =
    integral^infinity_0 tau^2 r e^(- tau r) dd(tau) - 1/r^2 = 2/r^2 - 1/r^2 = 1/r^2
  $
  This means that $sigma = 1/r$ and $"CV"_"ISI" = 1$.
]

#proposition[
  The Fano Factor (FF) defined as $sigma^2 / mu$ of the number of events of a PP is $1$.
]

#proof[
  To compute the moments we need to compute the derivatives of the moment-generating function at
  $alpha = 0$.
  $
    g(alpha) &= sum^infinity_(n = 0) e^(alpha n) ((r T)^n e^(-r T))/n! \
    &= e^(- r T) sum^infinity_(n = 0) ((r T e^alpha)^n )/n! \
    & = e^(-r T) e^(e^alpha r T) \
    & = e^((1 - e^alpha) r T) \
    lr(dv(g(alpha), alpha, k) |)_(alpha = 0) & = sum^infinity_(n = 0) n^k ((r T)^n e^(-r T))/n!
  $


  We now use the result to compute the moments.
  $
    angle(n) & = sum^infinity_(n = 0) n P_T (n) = dv(g(alpha), alpha) |_(alpha = 0) \
    & = e^(- r T (1 - e^alpha)) r T e^alpha |_(alpha = 0) = r T\
    angle(n^2) & = (r T)^2 + r T \
    sigma^2 & = r T
  $

  Then $"FF" = 1$.
]

However experimentally we get that the FF is usually greater than $1$, this means that the spiking
is not really an homogeneous PP. A better model is a non-homogeneous PP, where the firing rate is
a stochastic process.

=== Reverse-Correlation Method

This is a method for estimating the firing rate, i.e. $r(t)$ in the previous section.

Let our signal be just a function of time $S(t)$, then we have the data $r(t)$ which is what the
neuron outputs. Our goal is to find an estimator for $r(t)$: this can be dependent just on the
stimulus (e.g. $r_"est" = f(S)$) or it could be history dependent
$
  r_"est" (t) = r_0 + integral_0^oo dd(tau) S(t - tau) D(tau)
$
for some kernel $D(tau)$. This is a Volterra expansion, we could also add higher order terms but we
won't need them.

For example let
$
  S(t) & = cases(A wide & t >= 0, 0 wide & t<0) \
  D(tau) & = 1/sigma exp(-tau/sigma) \
  r_"est" & = r_0 + integral^oo_0 dd(tau) A/sigma exp(-tau/sigma) bb(1)_(t - tau > 0) \
  & =integral_0^t dd(tau) A/sigma exp(-tau/sigma) = A(1 - exp(-t/sigma))
$

We are interested in the case where we know $r(t)$ but we want to find $D(tau)$.
To do this we want to minimize the distance between the true $r$ and the estimated one.

Let $T$ be the trial duration and compute the square loss:
$
  E = 1/T integral_0^T dd(t) abs(r_"est" (t) - r(t))^2
$
we then look for $r_0, D(tau)$ minimizing $E$.

#proposition[
  Assume that $integral_0^T dd(t) S(t) = 0$, that $S tilde N(0, sigma^2_S)$ and that $S$ are
  uncorrelated i.e. $angle(S(t') S(t)) = sigma^2_S S(t - t')$.

  The optimal $D(tau)$ is
  $
    D(tau) = (angle(r) C(tau))/sigma^2_S
  $
]

#proof[
  We start by discretizing time.
  $
    E & = (Delta t)/T sum^(N = T/(Delta t))_(i = 0) abs(r_"est" (i Delta t) - r(i Delta t))^2 \
    & = (Delta t)/T sum^N_(i = 0)
    abs(r_0 + Delta t sum^oo_(k = 0) D(k Delta t) S((i - k) Delta t) - r(i Delta t))^2 \
    & = (Delta t)/T sum^N_(i = 0)
    abs(r_0 + Delta t sum^oo_(k = 0) D^k S^(i - k) - r^i)^2
  $
  where in the last step we just abbreviated the notation.
  Then this is just a function of a vector of values of $D$: we can just set the derivative to $0$.
  $
    pdv(E, D^j) & = (2 Delta t)/T sum^N_(i = 0) [(r_0 + Delta t sum^oo_(k = 0) D^k S^(i - k) - r^i)
                    pdv(, D^j) (Delta t sum^oo_(k = 0) D^k S^(i - k))] \
                & = (2 Delta t)/T sum^N_(i = 0) [(r_0 + Delta t sum^oo_(k = 0) D^k S^(i - k) - r^i)
                    Delta t S^(i - j)] \
                & ==> (cancel(2) Delta t)/T sum^N_(i = 0) (r^i - r_0)S^(i - j) =
                  (cancel(2) Delta t)/T sum^N_(i = 1) Delta t
                  sum^oo_(k = 0) D^k S^(i - k) S^(i - j) \
                & ==> 1/T integral_0^T dd(t) (r^i - r_0) S(t - tau) =
                  1/T integral_0^T dd(t)
                  integral^oo_(0) dd(tau') D(tau') S(t - tau) S(t - tau') \
  $
  But then we can use our assumption: the LHS becomes
  $
    1/T integral_0^T dd(t) (r^i - r_0) S(t - tau)
    & = 1/T integral_0^T dd(t) dot.op r^i S(t - tau) -
    1/T integral_0^T dd(t) dot.op r_0 S(t - tau) \
    & = 0 + Q_(r s) ( - tau)
  $
  and we can use the substitution $t' = t - tau$ on the RHS to get
  $
    1/T integral_0^T dd(t) integral^oo_(0) dd(tau') D(tau') S(t - tau) S(t - tau')
    & = 1/T integral^(T - tau)_(-tau) dd(t') S(t' + tau- t') S(t') \
    & = integral dd(tau') Q_(s s) (tau - t') D(tau')
  $
  TODO: there is something wrong in the derivation above

  giving us the equation
  $
    Q_(r s) (- tau) = integral_0^oo dd(tau') D(tau') Q_(s s) (tau - tau')
  $

  Now we use the fact that $S$ is independent to get
  $
    integral^oo_0 dd(tau) D(tau') sigma^2_S delta(tau - tau') = D(tau) sigma^2_S
  $

  Showing that
  $
    D(tau) = (Q_(r s) (- tau))/sigma^2_S
  $
  and using @prop:sta we get the result.
]

The calculation also works for a generic $S(t)$, however the result is
$
  D(tau) = 1/(2 pi) integral^oo_(-oo) dd(omega) (tilde(Q)_(r s) (-omega))/(tilde(Q)_(s s) (omega))
  e^(-i omega t) wide cases(delim: #none, "where" tilde "represents", "the Fourier transform")
$

Note that we can choose the stimulus to be as the assumption since we are the one designing the
experiment.

=== Most effective stimulus

#proposition[
  The function $S(t)$ that maximizes $r_"est"(t)$ given that
  $
    integral^T_0 dd(t') abs(S(t'))^2 = "const"
  $
  is
  $
    S(T - tau) prop D(tau)
  $
]

#proof[
  TODO: lagrange multipliers
]

However, usually this is not enough to estimate the firing rate accurately. This might be due to
non-linearity of data or too little terms in the Volterra expansion.

We can fix this by introducing a non linearity $F(dot)$:
$
  r_"est" = r_0 + F(L(t)) wide "where" L(t) = integral_0^oo D(tau) S(t - tau) dd(tau)
$

This non-linear function $F$ can be fitted with the training data.

=== Visual system

This model can be expanded to spacial stimuli too:
$
  S(t, x, y) \
  C(tau, x, y) = sum_i S(t_i 0 tau, x, y) \
  L(t) = integral_0^oo dd(tau) integral integral dd(x, y) D(tau, x, y) S(x, y, t - tau) \
  D(tau, x, y) = angle(r) C(tau, x, y) /(sigma_S^2)
$

= Neural decoding

Given a vector of neural responses (i.e. firing rates) we want to go back to the stimulus $theta$.
A decoder is an estimator $hat(theta) (arrow(r))$.
