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
]<def:tm>

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

== Decidability VS Recognizability

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
]<cor:eixsts-no-re>

#proof[
  Take $L in "RE" without R$, then if $overline(L) in R$ we have that $L$ is also in $R$, if
  $overline(L) in "RE"$ then $L$ would also be in $R$. The only possibility is that
  $overline(L) in.not "RE"$.
]

=== Acceptance problem

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
  $
    exists L in.not "RE"
  $
]
#proof[
  The idea is that the set of TMs is countable while the set of all languages is uncountable.

  Indeed, the set of TMs is countable, since each all components needed to describe it are
  countable, see @def:tm.

  Then note that the set of infinite binary strings $B$ is uncountable by Cantor's diagonalization.
  Let $A$ be the set of all languages over $Sigma$. We now construct a bijection $f: A -> B$ showing
  that $A$ is also uncountable.

  Enumerate the elements of $Sigma^*$ (we know we can do this since $Sigma^*$ is countable) so that
  $Sigma^* = {s_1, s_2, ...}$. Now assign to each element of $Sigma^*$ a sequence of binary strings
  in $B$: each position of the binary string is $1$ if $s_i in A$ and $0$ otherwise.

  Then, a language $L$ can also be translated to $L_B$ to this representation as a subset of the
  translated $Sigma^*_T$.
  Then $f$ takes a language $L in A$ and maps it to a sequence in $B$ such that at position $i$
  there is a $1$ if the $i$-th element of $Sigma^*_T$ is contained in $L$.

  Then $f$ is a bijection between $A$ and $B$.
]


#theorem[
  $ A_"TM" in.not R $
]

#proof[
  By contradiction assume that there exists a TM called $H$ which decides $A_"TM"$, hence it always
  halts. Then $H$ accepts if $M$ accepts and rejects otherwise.

  Let $D$ be a TM whose input a TM $M)$, then runs $H(angle(M, angle(M)))$ but returns the
  opposite of what $H$ returns.

  This means that
  $
    D(angle(M)) = cases(
      "accept" wide & "if" M "does not accept" angle(M),
      "reject" wide & "if" M "accepts" angle(M),
    )
  $
  but feeding $D$ to itself we reach a contradiction:
  $
    D(angle(D)) = cases(
      "accept" wide & "if" D "does not accept" angle(D),
      "reject" wide & "if" D "accepts" angle(D),
    )
  $
]

#corollary[
  $ overline(A_"TM") in.not "RE" $
]
#proof[
  Immediate from @cor:eixsts-no-re.
]

=== Other undecidable problems

#proposition[
  Let
  $
    "Halt"_"TM" = {angle(M, w) | M "is a TM and" M "halts on" w}
  $

  Then $"Halt"_"TM"$ is undecidable.
]
#proof[
  Assume there exists a TM $R$ which decides $"Halt"_"TM"$. Then construct a TM $S$ which runs
  $R(angle(M, w))$: if $R$ rejects, $S$ rejects too; if $R$ accepts, then we simulate $M(w)$ (which we
  know it will not halt), and accept iff $M(w) = "accept"$.

  Then $S$ is a decider for $A_"TM"$ which cannot exist: contradiction.
]

#proposition[
  Let
  $
    E_"TM" = { angle(M) | M "is a TM and" L(M) != varnothing }
  $
  which tells us if a TM will reject on any input.

  $E_"TM"$ is undecidable.
]

#proof[
  Assume there exists a TM $R$ which decides $E_"TM"$.

  Construct $M_w$ which rejects each input $x != w$, while if $x = w$, it returns the output of
  $M(w)$.

  We then construct a TM $S$ as follows: on input $angle(M, w)$ return the output of
  $R(angle(M_w))$. $S$ is then a decider for $A_"TM"$, which cannot exist.
]

#proposition[
  Let
  $
    "EQ"_"TM" = { angle(M_1, M_2) | M_1, M_2 "are TMs and" L(M_1) = L(M_2)}
  $
  which tells us if two TMs are equivalent.

  $"EQ"_"TM"$ is undecidable.
]

#proof[
  Let $M_varnothing$ be a machine which always rejects. Then if we had a decider $R$ for $"EQ"_"TM"$
  we could run $R(angle(M, M_varnothing))$ and accept iff $R$ rejects: this is a decider for
  $E_"TM"$.
]

=== Reductions

A reduction converts a computational problem $A$ into a problem $B$ in a way that a solution to $B$
can be used to solve $A$. Formally it is a function $f: Sigma^* -> Sigma^*$.

This means that if there is a reduction from $A$ to $B$ and $A$ in undecidable then also $B$ is
undecidable.

#definition(title: [Computable reduction])[
  A function $f: Sigma^* -> Sigma^*$ is computable if there exists a TM $M$ which halst on every
  input $w in Sigma^*$ and return $f(w) in Sigma^*$.
]

#definition(title: [Mapping reducible])[
  A problem $A$ is mapping reducible to $B$, denoted by $A <=_m B$ if exists a computable function
  $f: Sigma^* -> Sigma^*$ where
  $
    w in A <==> f(w) in B wide forall w in Sigma^*
  $
]

#remark[
  If $A <=_m B$ then $overline(A) <=_m overline(B)$.
]

#theorem[
  If $A <=_m B$ and $B$ is decidable, then $A$ is decidable.
]

#proof[
  Let $M$ be a decider for $B$ and $f$ be a reduction from $A$ to $B$. Then a TM which computes
  $M(f(w))$ is a decider for $A$.
]

#corollary[
  If $A <=_m B$ and $A$ is undecidable, then $B$ is undecidable.
]
#proof[ Contrapositive of previous theorem. ]

#theorem[
  If $A <=_m B$ and $B$ is recognizable, then $A$ is recognizable.
]
#proof[

]

#proposition[
  $
    "EQ"_"TM" <=_m overline(A_"TM") wide "and" wide
    overline("EQ"_"TM") <=_m overline(A_"TM")
  $
]

#proof[
  For the first statement we will first prove that $A_"TM"$ reduces to $overline("EQ"_"TM")$, which
  will give us the result.
  Let $M_varnothing$ a TM that returns $M(w)$ if its input is $w$, while rejects everything else.
  Note that $angle(M, w) in A_"TM"$ implies that $L(M_w) != L(M_varnothing)$, while its negation
  also holds.
  We can then define the reduction $f$ as $f(angle(M, w)) = angle(M_w, M_varnothing)$, which is
  computable.

  For the second statement we will use the same method, proving that $A_"TM"$ reduces to
  $"EQ"_"TM"$.
  Define $M_w$ as before, then define $N_w$ as the TM which accepts iff its input is $w$.
  Then using $f(angle(M, w)) = angle(M_w, N_w)$ is a computable reduction which is complete and
  sound.
]

#theorem(title: [Rice])[
  $
        L_1 & = { angle(M) | M "is a TM and" L(M) "is recognizable" } in R \
        L_2 & = { angle(M) | M "is a TM and" L(M) "is finite" } in.not R \
    L_"odd" & = { angle(M) mid(|) cases(
                  delim: #none,
                  M "is a TM and" L(M) subset.eq {0, 1}^*,
                  "and" forall w in L(M)\, med abs(w) = 2n + 1\, med n in NN
                ) } in.not R \
  $
]

#theorem[
  Let $C subset "RE"$ be a non-empty subset of RE. Then
  $
    L_C = {angle(M) | M "is a TM and" L(M) in C} in.not R
  $
]

#proof[
  Wlog assume that $varnothing in.not C$ (otherwise we consider the complement of $L_C$).
  Let $L_0 in C$ and let $M_0$ a TM s.t. $L(M_0) = L_0$ (it exists since $L_0 in "RE"$).

  We define a reduction $f$ from $"Halt"_"TM"$ to $L_C$.
  $
    f(angle(M, w)) = angle(M_angle(M, w))
  $
  where $M_angle(M, w) (u)$ is a TM which runs $M(w)$ and returns $M_0 (u)$.
  Then $M_angle(M, w) (u)$ does the same thing as $M_0 (u)$ iff $M(w)$ does not halt.

  We have
  $
    L(M_angle(M, w)) = &cases(
      L(M_0) in C wide & "if" M "halts on" w,
      varnothing wide & "otherwise"
    ) \
    angle(M_angle(M, w)) &cases(in L_C wide & "if" M "halts on" w, in.not L_C wide &"otherwise")
  $
  and we can be sure that $angle(M_angle(M, w)) in.not L_C$ when $M$ does not halt on $w$ since
  $varnothing in.not C$ by assumption.

  We get
  $
         & f(angle(M, w)) = angle(M_angle(M, w)) in L_C \
    <==> & L(M_angle(M, w)) = L(M_0) \
    <==> & M "halts on" w \
    <==> & angle(M, w) in "Halt"_"TM"
  $
]
