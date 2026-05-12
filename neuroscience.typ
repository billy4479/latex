#import "lib/template.typ": *
#import "lib/theorem.typ": *
#import "lib/utils.typ": *

#show: template.with(
  titleString: "Mathematical Modelling for Neuroscience",
  author: "Giacomo Ellero",
  date: "A.Y. 2025/2026",
)

#show: thm-init

#let Nap = $"Na"^+$
#let Kp = $"K"^+$
#let mV = $"mV"$

= Neural Encoding

== Characterizing Activity

A neuron contains a soma (metabolic processes), dendrites (receive signals), and an axon (transmits
signals).
The mammalian cortex contains approximately 100,000 neurons per $m m^3$.

Neurons maintain a resting membrane potential of approximately -70 $mV$ driven by $Nap$ and $Kp$
channels.

When a spike reaches the axon terminal, voltage-gated calcium channels open, triggering the release
of neurotransmitters into the synaptic cleft.

A *Post-Stimulus Time Histogram (PSTH)* calculates average firing rate by counting spikes across
multiple trials over a time bin $Delta t$:
$
  "PSTH" = n_S / ( n_T Delta t )
$
where $n_S$ is the number of spikes within a specific time bin and $n_T$ is the number of trials.

The *Spike-Triggered Average (STA)* is the average stimulus preceding a spike:
$
  C ( tau ) = 1 / n sum_(i = 1)^n s ( t_i - tau )
$
where
- $tau$ is the time delay: neurons take some time to process information so a spike at time $t$ can
  be caused by a stimulus some time before. $tau$ is how much time in the past we should look.
- $n$ is the number of spikes recorded during the experiment.
- $t_i$ is the time in which the $i$-th spike occurred.
- $s$ is the continuous stimulus which was presented, $s(t_i - tau)$ is the value of the stimulus
  $tau$ time before the spike.

The time between each spike (*InterSpike Interval (ISI)*) is well described by a Poisson process
with time dependent $lambda$: experimentally it was shown that $"CV"_"ISI" := sigma/mu$ for the
ISI is $"CV"_"ISI" = 1$ which is the same as a PP.


== Predicting firing rates

We now want to predict firing rates.

We start with a simple model for instantaneous firing rate:
$
  r(t) = r_0 + L(integral_0^oo D (tau) s (t - tau) dd(tau))
$
where $L$ is a non-linearity and $D$ is the kernel: it tells us how much a stimulus presented at
$tau$ time ago influences the firing rate.

= Neural Decoding

== Reading Populations
For $N$ neurons responding linearly to a stimulus, the population estimator is
$
  hat(theta) ( arrow(r) ) = 1 / N sum_i r_i
$
For neurons with preferred directions we use a population vector
$
  arrow(C)_t = 1 / N sum_i r_(i \, t) arrow(C)_i
$

=== Cramer-Rao
An estimator is unbiased if
$
  angle(hat(theta) \( arrow(r) \)) - theta = 0
$
Fisher Information is defined as
$
  J \( theta \) = angle(\( V \( theta \, arrow(r) \) \)^2)
$
where the score $V$ is the gradient of the log-likelihood.

The Cramer-Rao inequality tells us that the MSE of any unbiased estimator is bounded by the inverse
of Fisher Information:
$
  angle((hat(theta) ( arrow(r) ) - theta )^2) gt.eq frac(1, J (theta))
$

We say that an estimator is efficient if the bound is sharp in the large $N$ limit.

For a population of independent Poisson neurons the Fisher information is
$
  J \( theta \) = T sum_(i = 1)^N frac(r_(i') \( theta \)^2, r_i \( theta \))
$

== Information Theory

Recall the definition of entropy
$
       H \( X \) & = - sum p_i log_2 p_i \
  H \( X \| Y \) & = H \( X \, Y \) - H \( Y \) \
        I (X, Y) & = sum p(x, y) log_2 ((p(x, y))/(p(x) p(y)))
$

= Neuronal Biophysics

== Equivalent circuit

A neuron is modeled as a leaky capacitor
$
  I_e = C_m frac(d V_m, d t) + V_m / R_L
$

We define the membrane time constant as $tau_m = R_L C_m$, typically 10-20 ms.

The voltage relaxes exponentially:
$
  V \( t \) = V^oo + \( V^"eq" - V^oo \) e^(- t \/ tau_m)
$
where $V^oo$ is the potential the neuron will reach at $t -> oo$ (usually defined by $V_"rest" +
I_"ext" R_m$) and $V^"eq"$ is a constant, usually the resting potential.


To find $V_"eq"$ we need to balance the concentration gradient and the electrical drift (Fick's and
Ohm's law) for each ion.

$
  V_(e q) = - V_T / z log ([C]_"in")/([C]_"out")
$
where $V_T$ is the thermal voltage (constant depending on temperature), $z$ is the valence of the
ion (e.g. +1 for $Nap$, -1 for $"Cl"^-$).

Then we can compute the overall resting potential using *Goldman equation* using all the ions,
giving a resting potential of $-70 mV$.

In the *Hodgkin-Huxley model* conductances are voltage-dependent.
$Nap$ activates rapidly then inactivates, while $Kp$ activates slowly and persists.
$
  I_m = g_L \( V - E_L \) + g_K \( V - E_K \) + g_(N a) \( V - E_(N a) \)
$
where $g_L, g_"K", g_"Na"$ are the gates for the "leak", potassium and sodium channel: their
conductance is allowed to change with voltage.

== Synapses
Chemical synapses are slow and unidirectional (using neurotransmitters); electrical synapses are
rapid and bidirectional (using gap junctions).

Ionotropic receptors trigger immediate changes in membrane potential;
Metabotropic receptors trigger slower, longer-lasting intracellular cascades.

Synaptic current is modeled as
$
  I_s = g_s (V - E_s) "with" g_s = macron(g)_s P_s P_"rel"
$
where $P_s$ is the probability that the receptor in the postsynaptic neuron is open, while $P_"rel"$
is the probability that the presynaptic neuron releases a neurotransmitter when a spike arrives.

Postsynaptic open probability evolves as
$
  dv(P_s, t) = alpha_s (1 - P_s) - beta_s P_s
$

Common synapses are
- $"AMPA"$: excitatory, fast, no voltage dependency
- $"NMDA"$: excitatory, slow, voltage-dependent due to $"Mg"^(2 +)$ block
- $"GABA"_A$: inhibitory, fast

== Leaky Integrate-and-Fire (LIF) Models

This model is a simplification of the HH model, which can get quite computationally expensive.

Instead of modelling the $Nap$ and $Kp$ currents we just look at the leak channel. Also, when $V$
reaches $V_"th"$, a spike is emitted and $V$ gets reset to $V_"reset"$.
$
  tau_m dv(V, t) = -(V - E_L) + I_"syn" (t) R_m
$<eq:lif-ode>
where $tau_m$ is the membrane time constant, which tells us how quickly a neuron reacts to a certain
input; $I_"syn"$ is the sum of the currents of the pre-synaptic excitatory or inhibitory neurons:
$
  I_"syn" = sum^(N_E)_i g_(E, i) (V - E_E) + sum^(N_I)_i g_(I, i) (V - E_I)
$<eq:lif-syn>
where $g_(E, i) (V - E_E)$ is the current generated by the $i$-th excitatory pre-synaptic neuron.

The mean firing rate for constant input is
$
  r_"isi" = [tau_m log ((R_m I_e + E_L - V_"reset")/(R_m I_e + E_L - V_"th"))]^(- 1)
$

We can further simplify @eq:lif-syn with some further assumptions to get
$
  I_"syn" = - tau_m J_E sum^(N_E)_i y_(E, i) + tau_m J_I sum^(N_I)_i y_(I, i)
$
where $J_E, J_I$ are the synaptic efficacies and $y_(dot, i)$ are the spike trains for neuron $i$
(sum of dirac deltas of when the neuron spikes).

=== Gaussian approximation

With many pre-synaptic inputs we can approximate @eq:lif-ode as
$
  tau_m dv(V, t) = - V + mu + tau_m sigma z(t)
$
where $angle(z(t)) = 0$ and $angle(z(t) z(t')) = delta(t - t')$ (dirac delta).
Furthermore we have
$
       mu & = N r_"pre" tau_m (J_E - J_I) + E_L \
  sigma^2 & = N r_"pre" tau_m (J_E^2 + J_I^2)
$

= Networks of Neurons
Connectivity can be feed-forward (good for processing and transforming information), recurrent
(enables memory and interesting network dynamics), or feedback.

*Dale's Law* states that a neuron transmits the same neurotransmitter set at all its postsynaptic
connections.

For analyzing large networks of neurons even LIF models are too computationally expensive. We resort
to firing rate model, which take as input the firing rate of the pre-synaptic neurons, add weights
and non-linearities and give as output the firing rate of the current neuron.
$
  cases(
    display(tau_s dv(I_S (t), t) = - I_S (t) + sum_i w_i u_i (t)),
    display(tau_r dv(v(t), t) = - v(t) + F(I_s (t)))
  )
$
where $tau_s, tau_m$ are the synaptic and membrane time constants and $F$ is a non-linear activation
function.

We can also use simplified versions:
- If we assume instantaneous responses $tau_s >> tau_m$
$
  cases(
    display(tau_s dv(I_S (t), t) = - I_S (t) + sum_i w_i u_i (t)),
    display(v(t) = F(I_s (t)))
  )
$
- If we assume instantaneous synapses $tau_s << tau_m$
$
  cases(
    display(I_S (t) = sum_i w_i u_i (t)),
    display(tau_r dv(v(t), t) = - v(t) + F(I_s (t)))
  )
$

== Feedforward & Linear Recurrent Networks
We assume the case of fast synapses $tau_s << tau_m$, therefore the model can be approximated by
$
  tau_r dv(v(t), t) = -v (t) + F(W u + M v)
$
where $W$ is them matrix of feed-forward weights and $M$ is the matrix of recurrent connections.

In feed forward networks $M = 0$.

In a 1D recurrent network we have
$
  tau dv(v, t) = -v + h + M v
$
where $h$ is the external input.

The behavior of the network depends on $M$:
- If $M < 1$ the network is stable and converges to
  $
    v_oo = h/(1 - M)
  $
- If $M > 1$ the activity diverges.
- If $M = 1$ we can perfectly integrate the network:
  $
    v(t) = 1/tau integral h(t') dd(t')
  $

In $N$ dimensions we just check the eigenvalues of the matrix $M$ and do the same analysis we did
for the 1D case on each direction.

We could also define a continuous network of neurons, for example by imagining neurons which are
sensible to a preferred orientation of the stimulus $theta in [-pi, pi]$. Then the connection
between two neurons with preferred orientations $theta, theta'$ can be defined as
$
  M(theta, theta') prop cos(theta - theta')
$
giving that neurons which prefer similar angles excite each other strongly.

== Nonlinear Recurrent Networks

=== General case

The equation we need to solve is
$
  tau_r dv(v(t), t) = -v(t) + F(h + M v)
$

First we need to find fixed points:
$
  v_0 = F(h + M v_0)
$
we could have 0, 1, or many fixed points.

Then we linearize around the fixed point
$
  v(t) = v_0 + delta v(t) quad "with" tau_r dv(delta v, t) = lambda delta v
$
where
$
  lambda = - 1 + M lr(dv(F(I), I)|)_(v = v_0)
$

Depending on $lambda$ we can deduce the stability of the system:
- $lambda < 0$ the fixed point is stable
- $lambda > 0$ the fixed point is unstable
- $lambda = 0$ the perturbation persists and the system is at the boundary of stability

For $N$ dimensions the perturbation $delta bold(v)$ obeys to
$
  tau_r dv(delta bold(v), t) = J delta v quad "where" J "is the Jacobian"
$

Again we look at the eigenvalues of $J$:
- The real part behaves like $lambda$ in the 1D case.
- The imaginary part adds oscillation.

=== E-I Model

We group the population of neurons in two: excitatory and inhibitory; then we assume that the two
groups behave as a single neuron, having the same firing rate and input stimulus.

$
  tau dv(v_E, t) & = -v_E + [h_E + M_(E E) v_E - M_(E I) v_I]_+ \
  tau dv(v_I, t) & = -v_I + [h_I + M_(I E) v_E - M_(I I) v_I]_+
$
where $[ dot ]_+$ is ReLU.

We have
$
  J = mat(
    -1 + M_(E E), - M_(E I);
    M_(I E), -1 - M_(I I)
  )
$

We can look at the following cases where the network is stable:
- $M_(E E) < 1$: in this case the excitatory subnetwork is stable on its own, this means that the
  inhibitory network is not needed to stabilize the activity.
- $M_(E E) > 1$ but the inhibition is strong enough to stabilize the network.

If $M_(E E) > 1$ it is possible that increasing $h_I$ will cause $v_I$ to decrease in steady state
since the stronger inhibitory activity will actually decrease $v_E$ enough to make $v_I$ decrease
too.
