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
Let $n$ be the number of trials, $s(t)$ be a time-varying stimulus and $delta(t)$ be a neuron's
signal.
$
  rho(t) & = "spike train" = sum^n_(i = 1) delta(t - t_i) \
  C(tau) & = "STA" = 1/n sum^n_(i = 1) s(t_i - tau)
$

The spike train is the number of signals until $t$.

TODO: add correlation between $rho$ and $C$.


