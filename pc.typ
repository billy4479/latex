#import "lib/template.typ": *
#import "lib/theorem.typ": *
#import "lib/utils.typ": *

#show: template.with(
  titleString: "Parallel Computing",
  author: "Giacomo Ellero",
  date: "A.Y. 2026/2027",
)

#show: thm-init

= PRAM

This is a model to approximate the behavior of RAM.
Memory access is one of the most important thing to design around in a parallel system.

With this model we ask _"How much of the computation can run in parallel if memory is not the
bottleneck"_: we remove from the equations caches, networking, schedulers, etc.
This provides an upper bound on the computing time of the system.

In this approximations we assume:
- All processors $P_1, ..., P_n$ are identical.
- Each processor has its own registers and private variables.
- All instructions take the same time.
- Load and store to RAM take a constant time, we say "one unit of time".
- No limits on the `int` or `float` size.
- All processors execute the same program.
- All processors are tightly in sync.

This means that all processors
$
  #raw("Read") --> #raw("Compute") --> #raw("Write")
$
No synchronization, no signal passing. This means that we can fully utilize the whole computing
power.

We can generalize to say that interactions within processors happen only at specific times, however
we will deal with them later.

== Access model

We can have a model which only allow exclusive reads and writes (ER, EW), or allow concurrent ones
(CR, CW) too, in any combination.

In particular, we need to be particularly careful about CW, since we need some special rules such as
a priority between processors.

== Defining "faster"

#definition(title: "Speedup")[
  The speedup is how many times the parallel solution is faster than the sequential baseline over a
  certain size of the input $n$.
  $
    S_p (n) = (T^* (n)) / (T_p (n))
  $
  where $T^* (n)$ is the elapsed time for the sequential version and $T_p (n)$ is the elapsed time
  for the parallel program over $p$ processors.
]
#definition(title: "Efficiency")[
  $
    E_p (n) = (T_1 (n)) / (p T_p (n))
  $
  where $T_1 (n)$ is the serialized execution of the parallelized algorithm.
]
#definition(title: "PRAM Cost")[
  This is the allocated processors times the number of rounds.
  A cost-optimal solution has $Theta(T_1)$.
  $
    "Cost" = p T_p (n)
  $
]

== Choosing the baseline

Note the difference between $T^*$ and $T_1$: $T^*$ is the program optimized for a single core, while
$T_1$ is the parallel program running on a single core.

The baseline is the *best* sequential algorithm available, our baseline is $T^*$, not $T_1$.
