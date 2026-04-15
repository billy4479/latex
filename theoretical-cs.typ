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

#corollary[
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


#example(title: [Modified Post Correspondence Problem (MPCP)])[
  Consider a set of stings $L$ and the set of pairs $D = {(t, b) | t, b in L}$ called dominoes where
  $t$ refers to the "top" string and "b" to the bottom one.
  A MPCP instance $P$ is a list of elements of $D$ with repetition such that there is a "special"
  marked element.

  Then $P$ is match if concatenating all the top strings together gives the same string as the
  concatenation of all the bottom strings.

  The problem of finding a MPCP instance with a match is undecidable.
]

#proof[
  We will prove that $A_"TM" <=_m "MPCP"$.

  We construct a $f$ such that, for all pairs $angle(M, w)$, $f(angle(M, w)) = P$ such that:
  - $P$ is a match if and only if there exists a legal sequence of configurations of $M$ running on
    $w$ such that $M$ accepts $w$.
  - Then $M$ accepts $w$ iff $P$ has a match.
  - This means that $angle(M, w) in A_"TM" <==> P in "MPCP"$.

  Consider a legal sequence of configurations of $M$ running on $w$ denoted by $c_1, c_2, ...$.
  Let $q_1, q_2, ...$ be the sequence of states of $M$ corresponding to $c_1, c_2, ...$.
  To serialize each state $c_i$ we write $angle(c_i) = u plus.o q_i plus.o v$ where $u$ is what is
  behind the tape head and $v$ is the part of the tape which is under the head and beyond.

  Construct each domino $d_i = (t_i, b_i)$ such that $t_i = angle(c_i) plus.o \#$ and
  $b_i = angle(c_(i + 1)) plus.o \#$. At $i = 0$ we set $t_0 = \#$.

  From this construction we have that the concatenation of the top strings is always longer than the
  concatenation of the bottom string. Then, if $c_(i + 1)$ is the accept state on the next domino we
  just complete the last part missing for matching.

  This is a sketch but the main ideas are locality of the application of the $delta$ function.
]

= Complexity

We look at problems which are solvable in principle but in practice require more time or memory that
what is reasonable.

== Time complexity

This is the number of steps performed by a single-tape TM needed to solve the problem.

The complexity can then be influenced by the algorithm used, the input representation and the
computational model.

We will also divide problems in classes:
- $P$ can be solved in polynomial time
- $"NP"$ can be verified in polynomial time
- $"PSPACE"$ can be solved in polynomial time
- $"CONP"$ their complement can be solved in polynomial time
- $L$ can be solved in logarithmic time
- $"NL"$ can be solved in logarithmic time when using stochastic algorithms

#definition(title: [Running time])[
  Let $M$ be a TM that halts on all inputs.
  The running time of $M$ is a function $f: NN -> NN$ where $f(n)$ is the maximum number of steps
  that $M$ performs on any input of length $n$.
]

#definition(title: [Time complexity class])[
  Let $t : NN -> NN$. The time complexity class $"TIME"(t(n))$ is the collection of all languages
  which are decidable by an order $bigO(t(n))$.
]

Note that the choice of computational model might affect running time.
We want to classify in a way which is not sensitive to "small" differences.

#theorem[
  Let $t(n)$ be a function. Every $t(n)$-time multi-tape TM has an equivalent $O(t^2(n))$-time
  single-tape TM.
]

#proof[
  The idea is that it takes $t(n)$ steps for each tape and $t(n)$ steps to emulate each step on a
  single tape.
]

We will see that all reasonable deterministic computational models are polynomially equivalent,
therefore we assume that polynomial differences in running time are "small". The only exception is
quantum computers which are able to solve some problems in polynomial time, while classical
algorithms cannot.

We can define then some classes:
- Polynomial time: $t(n) = n^d$.
- Quasi-polynomial time: $t(n) = 2^bigO(log^d n)$.
- Sub-exponential time: $t(n) = 2^(n^epsilon)$ with $epsilon < 1$.
- Exponential: $t(n) = 2^bigO(n)$ or $t(n) = 2^(n^bigO(1))$.

#definition(title: [Class P])[
  P is the class of all languages which are decidable in polynomial time on a deterministic
  single-tape TM.
]

This is an important class because
+ It is invariant under all models of computation.
+ Roughly corresponds to the class of problems which are realistically solvable on a computer.

=== Non-deterministic TM

A non-deterministic TM is a TM in which the $delta$ function which now returns an element of
$cal(P)(Q times Gamma times {L, R})$. Then the move gets chosen at random.

We model this machines as a *computational tree*: each note is a machine configuration, each edge
is a deterministic transition and each branch (or path) is a deterministic computation. The root is
the initial configuration, then every leaf is one of the elements of the output of $delta$.

We say that a non-deterministic TM (NTM) accepts an input if $exists$ a branch which leads to
"accept".

#theorem[
  Every NTM has an equivalent deterministic TM which runs in exponential time.
]

#proof[
  Let $N$ be a NTM.
  Use BFS to traverse the computational tree of $N$ (DFS does not work as some branch might not
  halt).

  We simulate the NTM on a 3-tapes DTM, which we know can be simulated on a single-tape TM:
  one tape stores the input, one runs the simulation from the root to the current branch, one keeps
  track of the current branch.

  Since the domain of the $delta$ of the NTM is still finite (the power set of a finite set is still
  finite), the alphabet of the address-tape is also finite. On that tape we store the list of
  choices of the output of $delta$ we used to get to the current leaf of the computational tree.
]

#definition(title: [Running time of NTM])[
  Let $N$ be a NTM. Then the running time of $N$ is the function $f: NN -> NN$ where $f(n)$ is the
  maximum number of steps that $N$ performs on any input of size $n$ on any branch.
]

#proposition[
  Every $t(n)$-time single tape NTM has an equivalent $2^bigO(t(n))$-time single-tape DTM.
]

=== Verifiability

#definition(title: [Verifier])[
  A verifier for a language $A$ is an algorithm $V$ where
  $
    A = { w | exists "a string" c "s.t." V "accepts" angle(w, c)}
  $
]

The running time of $V$ is measured in terms of $w$. We say that $A$ is polynomially verifiable if
there exists a polynomial time $V$. We call $c$ the *certificate* or proof of membership.

#definition(title: [NP])[
  NP is the class of languages which have a polynomial time verifier.
]

Note that if a language is in $P$ then its polynomial verifier is just the (polynomial) algorithm
which solves the original problem.

#theorem[
  A language is in NP if and only if it can be decided by some NTM in polynomial time.
]

#proof[
  / P-verifiable implies NTM-decidable:
    Let $A in "NP"$ and $V$ a verifier for $A$ which runs in polynomial time. The following NTM $N$
    is a decider for $A$ in polynomial time:
    - Accept input $w$ of length $n$.
    - Choose non-deterministically a string $c$ of length at most $n^k$ ($k$ is some constant)
    - Run $V(w, x)$.
    - Accept iff $V(W, c)$ returns accept.

  / NTM-decidable implies P-verifiable:
    Build a verifier for $A$ as follows:
    - Accept input $angle(w, c)$
    - Simulate $N$ deterministically on $w$, where $c$ are the choices made along the
      non-deterministic branches.
    - Accept iff this branch of $N$ accepts.

]

#corollary[
  Any language in NP can be decided in exponential time.
]

== NP Completeness

#definition(title: [NP complete])[
  A language $B$ is NP-complete if $B in "NP"$ and $A in "NP" ==> a <=_p B$.
]

Empirically we noticed that most problems are either in P or NP-complete.

#definition(title: [Polynomial time reducibility])[
  A problem $A$ is polynomial time mapping reducible to $B$ ($A <=_p B$) if $exists$ a polynomial
  time computable function $f: Sigma^* -> Sigma^*$ s.t.
  $
    w in A <==> f(w) in B
  $
]

#theorem[
  3SAT $<=_p$ CLIQUE.
]

#proof[
  Construct a mapping as follows:
  - Let $phi = c_1 and ... and c_k$ be a 3CNF
  - For each clause $c_i$ add 3 vertices in $G$, one for each literal
  - Add an edge between two vertices if:
    - They are in different triples AND
    - Their literals are consistent (i.e. put an edge unless the vertices represent $x$ and $not x$
      for some $x$)

  Then the elements of a clique in $G$ give the truth assignment for 3SAT problem.
]

#definition(title: [NP-Hard])[
  A language $B$ is NP-Hard if $A in "NP" ==> A <=_p B$.
]

#proposition[
  If $B$ is NP-Complete and $B in P$, then $P = "NP"$.
]

#proposition[
  If $B$ is NP-Complete and $B <=_p C$ for some $C in "NP"$ then $C$ is also NP-Complete.
]

#theorem[
  The Bounded Halting (BH) problem is NP-complete.
]

Bounded Halting is defined as
$
  "BH" = {
    angle(M, x) lr(
      | cases(
        delim: #none,
        M "is a TM and" exists c "such that",
        M(x, c) = "accept in less than poly"(abs(x)) "steps"
      )
    )
  }
$

#proof[
  First note that $"BH" in "NP"$, since given the certificate $c$ by definition we halt in
  polynomial time.

  Let $A in "NP"$, we will show that $A <=_p "BH"$. Let $V_A$ be a polynomial time verifier for $A$.

  Construct the reduction $f(x) = angle(V_A, x)$, then
  $
    angle(V_A, x) in "BH" <==> exists c "s.t." V(x, c) = "accept" <==> x in A "in poly"(abs(x))
    "steps"
  $

  Meaning that BH is NP-Complete.
]

#theorem(title: [Cook-Levin])[
  SAT is NP-Complete.
]
#proof[
  We need to show that $"SAT" in P$ and that $A in "NP" ==> A <=_p "SAT"$.
  The first part is trivially true.

  Let $A in "NP"$. Given $w$ we construct a formula $phi$ such that $w in A <==> phi in "SAT"$.
  Since $A in "NP"$ there exists a NTM $N$ which decides $A$ in poly-time, say $n^k$ for some $k$.
  This means that
  $
    w in A <==>cases(
      delim: #none,
      exists c_0\, c_1\, ...\, c_m "legal configurations of" N,
      "s.t." c_m "is accept"
    )
  $

  Then we can build a $n^k times n^k$ tableau where
  - Each row represents $c_0, c_1, ..., c_m$: the first row is the initial configuration, the last
    row is either accept or reject, and consecutive rows must obey the $delta$ function of $N$.
    This is at most $n^k$ by the definition of $N$.
  - Each column contains the state of the machine at each configuration. This is at most $n^k$ since
    the TM can move at most $n^k$ cells in $n^k$ steps, so we don't care about what happens beyond
    that point.

  A tableau is accepting if any row is an accept configuration.

  We construct a formula $phi$ as follows
  $
    phi = phi_"cell" and phi_"start" and phi_"move" and phi_"accept"
  $
  where
  - $phi_"cell"$ enforces that each cell contain exactly one symbol.
  - $phi_"start"$ enforces that the first row is $q_0 w$.
  - $phi_"move"$ enforces that each row legally follows the preceding row.
  - $phi_"accept"$ enforces that the state $u q_"accept" v$ occurs somewhere.

  We now proceed with the explicit construction of each component of $phi$.

  The alphabet of the tableau is $C = Q union Gamma union {\#}$ (where \# is placed to delimit the
  input). We define $"cell"[i, j]$ to be the cell in row $i$ and column $j$. A SAT variable
  $x_(i, j, s)$ with $s in C$ is true if $"cell"[i, j] = s$. The number of SAT variables is
  $abs(C) n^(2k)$.

  Then
  $
    phi_"start" & = x_(1, 1, \#) and x_(1, 2, q_0) and x_(1, 3, w_1) and ... and x_(1, n^k, \#) \
    phi_"accept" & = or.big_(1 <= i, j <= n^k) x_(i, j, q_"accept") \
    phi_"cell" & = and.big_(1 <= i, j, <= n^k) [(or.big_(s in C) x_(i, j, s)) and
      (and.big_(s, t in C \ s != t) (not (x_(i, j, s) and x_(i, j, t))))] \
    phi_"move" & = and.big_(1 < i, j < n^k)
    (or.big_(a_1, a_2, a_3, a_4, a_5, a_6\ "s.t. the window is legal") \
      & x_(i, j - 1, a_1) and x_(i, j, a_2) and x_(i, j + 1, a_3) and x_(i + 1, j - 1, a_4)
      and x_(i + 1, j, a_5) and x_(i + 1, j + 1, a_6)
    )
  $
  Where $phi_"move"$ checks that every $2 times 3$ window the move was legal. This works because
  changes happens locally, at most in a $2 times 3$ window. There are a few possibilities for this:
  if the head is not in the window the window should be copied; if the head is in the middle of the
  cell we check that the move that it performs is allowed by the $delta$ function; if the head is at
  the end of the window (either in the row above or in the one below) we should always allow for
  this construction, since we don't have enough information to know if the head (which is now out of
  our view) is in the right state, the next window will take care of this, we just accept. Note that
  the set of legal windows is finite, therefore the big or in $phi_"move"$ is finite and over a
  polynomially large set.

  The time complexity of this transaction is polynomial:
  - $phi_"cell"$ is $bigO(n^(2k))$.
  - $phi_"start"$ is $bigO(n^k)$.
  - $phi_"move"$ is $bigO(n^(2k))$.
  - $phi_"accept"$ is $bigO(n^(2k))$.
  Giving a total complexity of $bigO(n^(2 k))$.

  There are ways to run this reduction faster, but it's out of scope of today's class.
]

#proposition[
  $
    "SAT" <=_p "3SAT"
  $
]

#theorem[
  Vertex Cover is NP-Complete.
]

Recall the definition of Vertex Cover (VC):
$
  "VC" = {
    angle(G, k) | G "is an undirected graph that has a" k"-vertex cover"
  }
$
where a $k$-vertex cover is a set of $k$ vertices such that all edges in the graph are touched by
those vertices.

#proof[
  First, VC is trivially in NP, since given a set of vertices we can quickly check if all the edges
  are covered.

  We will prove that clique reduces to VC in order to show NP-completeness.
  To do so, we write a reduction $f(angle(G, k)) = angle(G', k')$ such that
  $angle(G, k) in "CLIQUE" <==> angle(G', k') in "VC"$.

  We define the complement $G_C$ of a graph $G$ as the graph which contains exactly all edges _not_
  in the original graph.
]

#proposition[
  Given a 3SAT expression $phi$ with $m$ clauses, a random assignment will have
  $
    EE["number of satisfied clauses"] = 7/8 m
  $

  Moreover, it's NP-hard to decide if more than $7/8 + epsilon$ fraction of the clauses is
  satisfiable, $forall epsilon > 0$.
]

#proof[
  This is a sketch.

  Every clause has $8$ possible assignment, of these $8$, $7$ are truthful (since the only false
  assignment is all variables in the clause are false). We get the result by linearity of the
  expectation.
]

= Zero Knowledge Proofs

Let $x_A$ be the password of Alice and $f(x)$ be a function hard to invert. ZKPs are a way to prove
that you know $x_A$ such that $f(x_A) = y_A$ without revealing anything else.

#definition[
  An NP proof system for membership in $L$ is an algorithm $V$ such that i
  / Completeness: $ x in L => exists "proof s.t." V(x, "proof") = "accept" $
  / Soundness: $ x in.not L => forall "proof s.t." V(x, "proof") = "reject" $
  / Efficiency: $ V(x, "proof") "run s in poly"(abs(x)) "time" $
  are satisfied.
]

#remark[
  NP proofs provide more "knowledge" than just $x in L$.
]

We introduce the idea of interactive proofs: there is a proofer $P$ and a verifier $V$ which sent to
each other a series of random messages $m_i$, then $V$ looks at the message history and decides to
accept or reject.

#definition(title: [Interactive proof])[
  An interactive proof for $L$ is an interactive protocol between $(P, V)$ such that
  - $x in L => V "accepts in" (P, V)(x) "with" prob >= 2/3$
  - $x in.not L => forall P^*, V "accepts in" (P, V)(x) "with" prob <= 1/3$
  - $V$ runs in polynomial time
]

It might look like $1/3$ probability of mistakes is quite high, however we can fix this by repeating
the proof multiple times and invoke the CLT.

In general $P$ has an advantage compared to $V$: either $P$ is computationally unbounded or it knows
some secret which $V$ does not know (e.g. a certificate for an instance of an NP problem).

#remark[
  The space of languages which can be proved interactively contains both NP and co-NP.
]

#example(title: [Quadratic-Residuosity])[
  $
    L = {(N, x) | x in Q R_N }
  $
  where
  $
    Q R_N = {c in ZZ_N | exists z "s.t." z^2 = x mod N}
  $
  and $ZZ_N$ is the set of numbers modulo $N$.

  If $N = P Q$ for two large prime numbers $P, Q$, then deciding $(N, x) in Q R_N$ is hard.

  How do we prove that $x in Q R_N$.
]

#solution[
  The naive approach would be to just give the root $z$ such that $z^2 = x mod N$. We can do better
  though.

  First note that
  $
    x in Q R_N <==> exists y in Q R_N and x y in Q R_N
  $

  Construct a protocol with 3 messages:
  1. The proofer picks $r in ZZ_N^*$ and sends $t = r^2 mod N$.
  2. The verifier will then reply with a bit $b$ at random (either 1 or 0), this is kind of a
    "challenge".
  3. If the proofer got a 0 it sends $s = r mod N$, if it got a 1 it sends $s = z r mod N$.
  4. The verifier check:
    - If $b = 0$ we check that $r^2 = t mod N$.
    - If $b = 1$ we check that $(z r)^2 = t x$.


  If $x in Q R_N$ then the proofer always accepts.
  If $x in.not Q R$ then it will reject with probability at least $1/2$.
]

#definition(title: [Zero Knowledge])[
  $(P, V)$ is Zero Knowledge if for all probabilistic polynomial verifiers $V^*$ there exists
  a simulator $S$ such that $S(x)$ has the same distribution of $(P, V^*) (x)$ (meaning that we
  could simulate the interaction, therefore $V^*$ learned nothing).
]

#proposition[
  The Quadratic-Residuosity proofer is ZK.
]

#proof[
  Note that this protocol is complete with probability 1 (if the proofer is honest it can always
  convince the verifier) and sound with probability $1/2$ (if the proofer is lying it can still
  convince the verifier $1/2$ of the times when $b = 0$).

  To show that this proof is ZK we construct a simulator:
  - Pick $s$ and $b$ at random
  - Depending on $b$
    - If $b = 0$ choose $t = s^2 mod N$
    - If $b = 1$ choose $t = s^2/x mod N$
  This interaction is one where the verifier accepts, however, compared to an honest proofer, the
  simulator does not know what is $sqrt(t)$..
]

We went from bottom to top: indeed a simulator is more powerful than the proofer, a proofer cannot
choose before hand which $b$ will receive from $V$.

#theorem(title: [GMW '86])[
  Every $A in "NP"$ can be proved in Zero Knowledge.
]

#proof[
  This is a sketch.

  We will prove that there exists a ZK proof for 3-coloring which is NP-complete. This will show the
  result: given $x in L$ construct $G = f(x)$ and a certificate $d = g(c)$ such that we are working
  just on 3-coloring.

  To be exact we will show that 3-coloring is computational zero knowledge, which means that the
  simulator is computationally undistinguishable from an actual proof.

  The idea is
  - The proofer commits to a coloring, which sends to the verifier in such a format that the
    verifier cannot open it without the proofer telling it how.
  - The verifier asks for an edge
  - The proofer sends the coloring of just that edge and the "key" to open the commitment on just
    that edge.

  This is complete with prob 1 and sound with prob $1 - 1/abs(E)$. Note that by repeating this proof
  multiple times the verifier could extract the coloring for all the edges: to prevent this it's
  enough to permute the colors between each interaction, there are only $3!$ permutations but they
  still look random in the eye of the verifier.
]

= Space complexity

#definition(title: [Space complexity])[
  Let $M$ be a TM that halts on all inputs. The space complexity of $M$ is a function $f: NN -> NN$
  where $f(n)$ is the maximum number of cells that $M$ scans on any input of length $n$.
]

#proposition[
  The time complexity of a $f(n)$-space TM for $f(n) > n$ is at most $2^bigO(f(n))$.
]

#proof[
  By definition we know that the number of tape symbols in each configuration is $<= f(n)$.
  Then we can count the number of configurations with $f(n)$ symbols to be $f(n) 2^bigO(f(n))$
  because $abs(Gamma)$ is finite.
  Moreover, since each configuration occurs at most once (otherwise the TM would loop) we are done.
]

Define the following spaces:
$
   "SPACE"(f(n)) & = {L | L "is decidable by a" bigO(f(n))"-space TM"} \
  "NSPACE"(f(n)) & = {L | L "is decidable by a" bigO(f(n))"-space NTM"} \
        "PSPACE" & = union.big_k "SPACE"(n^k) \
       "NPSPACE" & = union.big_k "NSPACE"(n^k)
$

#proposition[
  SAT is decidable in linear space.
]

#proof[
  Enumerate all possible $x in {0, 1}^n$ and check if $phi(x) = "true"$.

  This means that the runtime is $2^n$, but the space is $bigO(n)$. The reason is that space can be
  recycled.
]

#corollary[
  All problems in NP can be decided in linear time.
]
#proof[
  Immediate from NP-completeness of SAT.
]

#theorem(title: [Savitch])[
  $
    "PSPACE" = "NPSPACE"
  $
  In particular
  $
    "NSPACE"(f(n)) subset.eq "SPACE"(f(n)^2)
  $
]
#proof[
  We will prove this by showing that DTMs can simulate NTMs using polynomially more space.

  Consider the configuration tree of a NTM, call each configuration $c_i$. Now we turn this tree
  into a directed graph: take the tree and make it directed from the root to the leaves, then merge
  all the nodes with repeated configurations.

  But then deciding acceptance of a NTM is the same as deciding reachability in the configuration
  graph. We modify the configuration graph adding another special "final-accept" state, then draw
  an edge from all accepting configurations of the NTM to this special "final-accept" node. In this
  way we just need to decide reachability from $c_0$ to "final-accept".

  The idea of the algorithm to find this path is that finding a path from $s$ to $t$ in $d$ steps is
  equivalent to showing that there exists an intermediate vertex $z$ such that $z$ is reachable from
  $s$ in $ceil(d/2)$ steps and $t$ is reachable from $z$ in $ceil(d/2)$ steps.

  At each step of the recursion we recycle the space we used to compute the other branch, therefore
  at each level we store $bigO(f(n))$, the depth of the recursion is
  $log_2 (2^(bigO(f(n)))) = bigO(f(n))$. This gives a total space of $bigO(f(n)^2)$.
]

#theorem[
  $
    "PSPACE" = "IP"
  $
  where IP is the space of interactive provable languages.
]

= Quantum Computing

A system is fully described by assigning an amplitude $alpha in CC$ to each possible configuration.

The *Born rule* gives us a way to commutate amplitudes to probabilities: the probability of an
outcome $i$ is given by $abs(alpha_i)^2 = Re(alpha_i)^2 + Im(alpha_i)^2$.

We can also represents probabilities distributions as matrices:
a *stochastic matrix* is a mapping to and from a probability distribution, we need that each entry
is non-negative and that all columns sum up to 1.

#definition(title: "Tensor product")[
  Let $v, w$ be two vectors, the tensor product is defined as
  $
    (v times.o w)_(i j) = v_i w_j
  $
  note that this can be written both as a matrix and as a longer vector.
]

Not all vectors can be decomposed into a tensor product of other vectors.

== Operations on qubits

If a bit can be $0$ or $1$ with probability $p$ and $q = 1 - p$ we can write the probability of the
bit to be in a certain position using vectors:
$
  vec(p, q) = p vec(1, 0) + q vec(0, 1)
$

A *qubit* is defined in a similar way:
$
  CC^2 in.rev vec(alpha, beta) = alpha vec(1, 0) + beta vec(0, 1)
$
with $abs(alpha)^2 + abs(beta)^2 = 1$ which comes by imposing Born rule.

Note that a probability vector should be one $ell_1"-unit"$ long (indeed $p + q = 1$ is a Manhattan
distance), while quantum states should be one $ell_2"-unit"$ long.

#let latcross = "✝"

#definition(title: "Dirac notation")[
  We denote column vector in $CC^d$ as $ket(psi)$, this is called a "ket".

  Given $ket(psi)$ we define $bra(psi)$ as
  $
    bra(psi) = (ket(psi))^latcross = mat(psi_1^*, ..., psi_d^*)
  $
  where $latcross$ denotes the transpose of the conjugate.

  Then a $braket(psi, phi)= bra(psi) dot.op ket(phi)$ is the dot product (a bra-ket), which means
  that $norm(ket(psi))_2 = sqrt(braket(psi, psi))$.
]

We then define the *computational basis* vectors as
$
  ket(0) & colon.eq vec(1, 0) \
  ket(1) & colon.eq vec(0, 1)
$
such that this is an orthonormal basis.

Given this basis we can write a qubit as $alpha ket(0) + beta ket(1)$.

Another basis we will use is the *Hadamard basis*:
$
  ket(+) & = 1/sqrt(2) ket(0) + 1/sqrt(2) ket(1) \
  ket(-) & = 1/sqrt(2) ket(0) - 1/sqrt(2) ket(1)
$

Another basis is the $theta$-rotated basis:
$
       ket(theta) & = vec(cos(theta), sin(theta)) \
  ket(theta^perp) & = vec(-sin(theta), cos(theta)) \
$

#example[
  If $ket(psi) = alpha ket(0) + beta ket(1)$ then we can extract $alpha$ and $beta$ as
  $
    alpha & = braket(0, psi) \
     beta & = braket(1, psi) \
  $
]

Any vector $ket(psi)$ different from an element of the basis is called a *superposition*. Note that
the definition of superposition depends on the basis.

The first axiom we saw already is the normalization of the qubit. The second axiom is about
*measurement* of a qubit: measuring a qubit in the computational basis gives us the probability of
the outcome being 0 or 1.
$
  prob("outcome is 0") & = abs(braket(0, psi))^2 \
  prob("outcome is 1") & = abs(braket(1, psi))^2
$

The third axiom is one which says that every transformation which maps a quantum state to another
quantum state is a valid transformation: any rotations are allowed and reflections are also allowed,
this means that all the transformations we can apply are represented by a unitary matrix.

Given a unitary matrix $U$ we can apply it to $ket(psi)$ as $U ket(psi)$.
This third axiom is just a way to state the *Schrödinger equation*.

#proposition(title: [Properties of unitary matrices])[
  Recall that a $d times d$ is unitary if $U^latcross U = I$.

  Then the following properties are also equivalent:

  - $U U^latcross = I$
  - $braket(U v, U w) = braket(v, w)$
  - $U$ preserves $ell_2$ norms
  - $U$ sends any orthonormal basis to an orthonormal basis
  - $U$ sends at least one orthonormal basis to an orthonormal basis
]

The easiest example of unitary matrix is rotation matrices:
$
  R_theta = mat(cos theta, -sin theta; sin theta, cos theta)
$

Some other famous operations are
$
  X & = mat(0, 1; 1, 0) wide  &                    "flips the bit" \
  Z & = mat(1, 0; 0, -1) wide & "keep 0 but changes the sign of 1" \
  Y & = mat(0, -i; i, 0) wide &            "we don't talk about Y" \
  I & = mat(1, 0; 0, 1) wide  &                         "identity" \
  H & =
      mat(1/sqrt(2), 1/sqrt(2); 1/sqrt(2), -1/sqrt(2))
      wide                    &     cases(
                                      delim: #none,
                                      "change of basis between",
                                      "computational and Hadamard"
                                    )
$

Actually $H$ is just the discrete Fourier transform in 2D.

The other operation we can perform is of course measuring the qubit. When we do the qubit collapses
to a probability and the realization of the probability becomes the new value of the qubit.

=== More qubits

If we have two qubits they will form a vector space over $CC^4$ with basis
$ket(00), ket(01), ket(10), ket(11)$, with some amplitudes $alpha$ which give probabilities in the
usual way.

In general the state of $n$ qubits is a unit vector in $(C^2)^(times.o n)$.

Given a state $ket(psi) = sum_(x in {0, 1^n}) alpha_x ket(x)$ we can measure all of them. We will
see the outcome $x$ with probability $abs(alpha_x)^2 = abs(braket(x, psi))^2$. We also say that the
state collapses to $ket(x)$.

Again, the legal transformation can be represented by unitary matrices $U in CC^(2^n times 2^n)$
such that $U_(x y) = braket(x, U, y)$. Note that if we specify a transformation on some basis, then
we are done since maps are specified completely by their effect on the basis.

Some examples are:
- $"SWAP"ket(a b) = ket(b a)$
- $"CNOT"ket(a b) = ket(a (a plus.o b))$
- $"CZ"ket(a b) = (-1)^(a b) ket(a b)$

As we saw in physics, the global phase $ket(phi) = lambda ket(psi)$, with $lambda in CC$ and
$abs(lambda) = 1$, does not matter: $ket(phi)$ is indistinguishable $ket(psi)$.

=== Tensor product

We define $ket(0 1) = ket(0) times.o ket(1)$. This works also in superpositions
$ket(alpha), ket(beta) in CC^2$ their joint state is $ket(alpha) times.o ket(beta)$.

Recall that
$
  ket(alpha) times.o ket(beta) & = (alpha_0 ket(0) + alpha_1 ket(1)) times.o (beta_0 ket(0) + beta_1 ket(1)) \
  & = alpha_0 beta_0 ket(00) + alpha_0 beta_1 ket(01) + alpha_1 beta_0 ket(10) + alpha_1 beta_1 ket(11)
$

Moreover, if $A$ and $B$ are linear maps, then their tensor product is the unique linear map such
that
$
  A times.o B (ket(alpha) times.o ket(beta)) = A ket(alpha) times.o B ket(beta)
$

Multiplication of tensor products commute:
$
  (I times.o V) (U times.o I) = U times.o V = (U times.o I) (I times.o V)
$

=== Entanglement

Not all states can be decomposed in a tensor product of smaller states. If the state is decomposable
we call it a *product-state*, otherwise we say that the state is *entangled*.

An example of entangled state is the EPR state:
$
  1/sqrt(2) (ket(00) + ket(11)) = 1/sqrt(2) vec(1, 0, 0, 0) + 1/sqrt(2) vec(0, 0, 0, 1)
$
which can be obtained with $"CNOT"(H times.o I) ket(00)$.

=== Partial measurement

When we have multiple qubits we can choose to measure just one.

If the two qubits are disentangled we just measure it as usual way, as if it was the only qubit in
the system.
However even if just one qubit collapses we still need to renormalize the amplitudes of the other
qubit so that we are still in a quantum state.

$
  ket(psi) & = alpha_(00) ket(00) + alpha_(01) ket(01) + alpha_(10) ket(10) + alpha_(11) ket(11) \
  &==> "measure first qubit" \
  &==> prob("seeing outcome" 0) = p_0 = abs(alpha_(00))^2 + abs(alpha_(01))^2 \
  & ==> ket(psi) = 1/sqrt(p_0) (alpha_00 ket(00) + alpha_(01) ket(01))
$

== Quantum circuit

We care about some state $ket(psi)$ which we will measure at the end of the circuit.
If we need other registers which are not part of the final result we add "ancilla" qubits.

Since we have ancillas we can defer all measurements to the end of the circuit: instead of measuring
we CNOT the value of the qubit we want to measure in a fresh ancilla which we won't touch ever again
until the end of the circuit.

The gates H, T and CNOT are enough to describe all other gates. The proof is kind of hard: matrices
have arbitrary precision, so we need to show that these gates give an arbitrarily good approximation
of any gate, fast.

To create a classical circuit on a quantum computer we need to create AND and NOT gates. We already
have an equivalent of NOT, the X gate, but we don have an equivalent for AND. For that we need to
create the Toffoli gate.
