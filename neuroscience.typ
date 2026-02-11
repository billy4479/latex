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
]


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

We define the *inter-spike interval* (ISI) as the time between spikes.
The coefficient of variation $"CV"_"ISI" = sigma/mu$ has been measured experimentally and it is
close to $1$

#proposition[
  Since $"CV_ISI" = 1$ experimentally, the ISI is well described by a Poisson process.
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


