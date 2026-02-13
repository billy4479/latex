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
  Let $Sigma$ be an "alphabet", i.e. a finite set such as ${0, 1}$ or ${"A", "B", ..., "Z"}$.
]

Let $Sigma^* = union.big_(n in NN) Sigma^n$, where $Sigma^n$ is the $n$-times Cartesian product of
$Sigma$.
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

Note that, by definition, there exists at least one symbol "\_" such that $"_" in Gamma$ but
$"_" in.not Sigma$.

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

#definition(title: [Language])[
  A language $L subset.eq Sigma^*$ is a set of strings in the given alphabet $Sigma$.

  / Decidable: The set $R$ of decidable languages is such that $exists M$, a TM, such that
    $
      M(w) = cases("accept" & "if" w in L, "reject" & "if" w in.not L) wide forall w in Sigma^*
    $

  / Recognizable: The set $"RE"$ of recognizable languages is such that $exists M$, a TM, such that
    $
      M(w) = cases(
        "accept" & "if" w in L,
        display(cases(delim: #none, "reject or", "does not hald")) & "if" w not in L
      ) wide forall w in Sigma^*
    $
]

#lemma[
  $ R subset "RE" $
]

#lemma[
  $ L in R quad ==> quad overline(L) = Sigma^* without L in R $
]

#proof[
  Since $L in R$ there exists a TM $M$ which decides $L$. Then define a TM $M'$ that decides
  $overline(L)$ by running $M$ and accepting if and only if $M$ rejects.
]

#lemma[
  $ L in "RE" and overline(L) in "RE" quad ==> quad L in R $
]

#proof[
  Since $L, overline(L) in "RE"$ there exists TMs $M_1, M_2$ which recognize them.
  Let $N$ be a TM which runs $M_1, M_2$ in parallel. Then, if $w in L$, $M_1$ will halt with
  acceptance, and define that $N$ will accept in this case. If $w in.not L$, then $M_2$ will halt
  with acceptance, and define that $N$ will reject in this case.

  In parallel means that the two machines will run "together", step by step.
]

#corollary[
  Suppose that $"RE" without R != varnothing$. Then $exists L in "RE"$ such that
  $overline(L) in.not "RE"$.
]

#proof[
  Take $L in "RE" without R$, then if $overline(L) in R$ we have that $L$ is also in $R$, if
  $overline(L) in "RE"$ then $L$ would also be in $R$. The only possibility is that
  $overline(L) in.not "RE"$.
]

Note that there are multiple variants of TMs which are all equivalent to a single-tape TM. Some
examples are adding a "stay" instruction, multi-tape TMs and non-deterministic TMs.

For example, in a multi-tape TM with $k$ tapes we have
$delta: Q times Gamma^k -> Q times Gamma^k times {L, R}^k$.

#proposition[
  Any $k$-tape TM $M$ has an equivalent single-tape TM $S$.
]

#proof[
  Note that every single-tape TM is a special case of multi-tape TM, hence this direction is trivial.

  Given a multi-tape TM $M$, we initialize the tape of a single-tape TM $S$ with a \# symbol, the
  content of the first tape, a \# symbol, the content of the second one, and so on.
  On each tape cell pointed by one of the $k$ pointers add an underline to differentiate from other
  symbols.

  The other limitation is that each portion of the tape could run out of space. In such case we
  implement a (very expensive) "shift everything by 1" operation which frees a space.
]

#theorem(title: [Acceptance problem])[
  Consider the set of all TMs and inputs such that $M$ accepts $w$:
  $
    A_"TM" = { angle(M, w) | M "is a TM and" M(w) = "accept"}
  $

  Then $ A_"TM" in "RE" $
]

#proof[
  On input $angle(M, w)$ we use an universal Turing machine $U$ which simulates $M(w)$.
  Then $U$ will accept or reject based on the output of $M(w)$, but if $M$ does not halt $U$ will
  also not halt.
]

#theorem[
  $ A_"TM" in.not R $
]

#corollary[
  $ overline(A_"TM") in.not "RE" $
]
