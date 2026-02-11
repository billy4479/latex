#import "lib/template.typ": *
#import "lib/theorem.typ": *
#import "lib/utils.typ": *

#show: template.with(
  titleString: "Theoretical\nComputer Science",
  author: "Giacomo Ellero",
  date: "A.Y. 2025/2026",
)

#show: thm-init

= Computability

We will explore what is actually possible to compute and what not.

/ Fact 1.: Any reasonable model of computation can be simulated on a TM (empirical).
/ Fact 2.: There exists problems that no TM can solve (will be proven).


#definition(title: [Alphabet])[
  Let $Sigma$ be an "alphabet", i.e. a finite set such as ${0, 1}$ or ${"A", "B", ..., "Z"}$. Let
  $Sigma^* = union.big_(n in NN) Sigma^n$, where $Sigma^n$ is the $n$-times Cartesian product of
  $Sigma$.
]
Note that $abs(Sigma^n) = abs(Sigma)^n$ and that $Sigma^*$ is countable.

#definition(title: [Computational Problem])[
  A computational problem is of two types.

  / Search problem: We look for a function $f: Sigma^* -> Sigma^*$ such that, given any input $w$,
    the output is a desired $f(w) = u$.
  / Decision problem: We look for a function such that, given a "language" $L subset.eq Sigma^*$, we
    have that
    $
      f(w) = cases("YES" wide & "if" w in L, "NO" wide & "if" w in.not L)
    $

  The input $w in Sigma^*$ is an *instance* of the problem.
]

#remark[
  Decision is actually a special case of search. Indeed we are searching for a function whose output
  will be interpreted as a $"YES"$ or a $"NO"$.
]

Computation can then be described as performing a series of local operations to the input to obtain
a global effect. Moreover the size of the machine is bounded in advance (i.e. the "code" is written
in advanced and is not infinite) but the input size is _not_ bounded in advance (at most countable).

== Turing Machine (TM)

The components of a TM are the following:
/ Infinite tape: This a one dimensional array which acts as the memory of the TM. Note that the tape
  has a start.
/ Tape head: The tape head points a position on the tape and can either move left/right on the tape
  or it can read/write in the pointed location.
/ A finite description: This means that the TM has a finite number of states it can be in.

Initially the tape is initialized with infinitely many "\_" symbols, which we assume are
$in.not Sigma$, and, at the head's position, is placed a finite input $in Sigma^*$. The input ends
at the first "\_" symbol. The output is also the content of the tape from the initial position up to
the current position of the head.

#definition(title: [Turing Machine])[
  A TM is a tuple of the following 7 items:
  - A finite set of states $Q$
  - The input alphabet $Sigma$
  - The alphabet of the tape $Gamma supset Sigma$
  - A transition function $delta: Gamma times Q -> Gamma times Q times {"L", "R"}$
  - A starting state $q_0 in Q$
  - A state which is recognized as the accept state $q_"accept" in Q$
  - A state which is recognized as the reject state $q_"reject" in Q$
    (such that $q_"accept" != q_"reject"$)
]

Then, a *configuration* of a TM is the tape, the state and the head location.
A configuration can then be expressed as $u, v in Gamma^*$, which are the elements of the tape to the
left and to the right of the head, and the state $q in Q$; we can write a configuration as $u q v$.

#corollary[
  Since $Q$ and $Gamma$ are finite, the domain of $delta$ is also finite. This implies that any
  TM has a finite description.
]

#remark[
  If we are at the start of the tape and $delta$ tells us to move left we stand still.
]

#definition(title: [Configuration system])[
  We say that a configuration $C_1$ can reach configuration $C_2$ if applying $delta$ at $C_1$
  yields $C_2$. We write $C_1 -> C_2$.

  Given two states $C_1, C_n$, we call it a configuration system if $C_1 ->^* C_n$, i.e.
  $exists C_1, ..., C_n$ such that $C_i -> C_(i + 1)$ for all $i in {1, ..., n-1}$.
]


We differentiate between *deciding* $L$ and *recognizing* $L$: if $M$ decides $L$, then either it
accepts or rejects based on whether $w in L$; if $M$ recognizes $L$, then if $w in L$ $M$ accepts,
but if $w in.not L$ we either reject or we don't halt.
