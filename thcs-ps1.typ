#import "lib/template.typ": *
#import "lib/utils.typ": *

#show: template.with(
  titleString: "Theoretical CS\nProblem Set 1",
  author: "Giacomo Ellero - 3243701",
  date: "25/02/2026",
  header: false,
  nameInFooter: false,
  toc: false,
  font: "New Computer Modern",
  bigHeading: false,
)

#set heading(numbering: none)
#set math.equation(numbering: "(1)")

= Exercise 1

+ This move is *feasible* assuming that $delta(q_1, 1) = (q_0, \_, R)$.
+ This move is *not feasible*: the head did not move and this TM does not include a steady state,
  therefore this is impossible to end up in that state with just one step.
+ This move is *not feasible*: the symbol $c in.not Gamma$.
+ This move is *feasible* assuming that $delta(q_0, 1) = (q_"acc", b, L)$.
+ This move is *not feasible* in just one step: either the head moved two positions or some more
  complex manipulations were made, which still require more than one step.
+ This move is *not feasible* since the state $q_2 in.not Q$.
+ This move is *not feasible* since once a TM is in state $q_"acc"$ it is halted will never perform
  other operations.
+ This move is *not feasible* in just one step since this TM is forced to move its head at every
  step.
+ This move is *not feasible* in just one step as a cell which is not under the tape head was
  modified.
+ This move is *not feasible* since $2 in.not Sigma$.

= Exercise 2

== Part 1

This language is recognizable but not decidable.

First note that $L in "RE"$ since we can use a universal TM $U$ to run the input TM $angle(M)$ on
$epsilon$.
Then we return "accept" if $M$ halts, if $M$ will not halt $U$ will not halt as well.

However, $L in.not R$, since we can reduce it to $"Halt"_"TM"$. When presented with an instance of
$"Halt"_"TM"$ $I = angle(M, w)$ construct the following TM $N_I$:
- Take as input $x$:
- Ignore $x$.
- Simulate $M(w)$:
  - If $M(w)$ halts return accept.
  - If $M(w)$ does not halt, we will also not halt.

This means that, on input $x = epsilon$, $N_I$ will halt iff $M(w)$ also halts. This means
$N_I in L <==> angle(M, w) in "Halt"_"TM"$. Then, if we had a decider $D$ for $L_epsilon$ we could
just construct $N_I$ and run $D(angle(N_I))$, which would be a decider on $I$.

== Part 2

$L in.not R$. If $L(M)$ contains $s = \""theoryofcomputing"\"$, it means that $M$ accepts $s$.
We can reduce this to $"Halt"_"TM"$ by using a similar method of the previous part: given an instance of
$"Halt"_"TM"$ $I = angle(A, w)$ construct a TM $N_I$:
- Take as input $x$.
- Ignore $x$.
- Simulate $M(w)$:
  - If $M(w)$ halts return accept.
  - If $M(w)$ does not halt we also don't return.

In particular, when running $N$, $N$ will accept iff $M(w)$ does not halt. If we had a decider
$D$ which could tell us if $N$ is accepted $s$ or not we would also have a decider for
$"Halt"_"TM"$.

Note however that $L in "RE"$ since we can just simulate $M(s)$ and see what happens.

We can now invoke the corollary seen in class: since $L in "RE" without R$, then
$overline(L) in.not "RE"$.

= Exercise 3

== Part 1

If $overline(L) in "RE"$ (and $overline(L) in.not R$, if $overline(L) in R$ also $L in R$)
$L in.not "RE"$.

(If both $L_1, L_2 in R$, then we can build a TM which decides $L_1 union L_2$ by first running a
decider for $L_1$, then a decider for $L_2$ and return accept if any of the two returns accept.)

If at least one of the two languages $L_1, L_2 in.not "RE"$, say $L_1 in.not "RE"$, we assume by
contradiction that there exists $M$ which recognizes $L_1 union L_2$. Then, since
$L_1 subset.eq L_1 union L_2$, $M$ will recognize $L_1$, which is a contradiction since $L_1$ is not
recognizable.

== Part 2

Consider an instance $I$ of $L_3$ and the reduction $f$ from $L_3$ to $L_2$. Then $f(I)$ is an
instance of $L_2$. Now consider the reduction $g$ from $L_2$ to $L_1$, then $g(f(I))$ is an instance
of $L_1$, which means that solving $L_3$ is not harder than solving $L_1$.

== Part 3

Since $L <=_m overline(L)$ there exists a computable function $f(x)$ such that $x in L$ iff
$f(x) in overline(L)$ or, equivalently, $f(x) in.not L$.
By contrapositive we have that $x in.not L <==> f(x) in L$.
Then we can construct a decider for $L$ as follows:
- On input $x$:
- Compute $y = f(x)$.
- Let $M$ be a recognizer for $L$.
- In parallel, we run $M(x)$ and $M(y)$.
  - If $x in L$ then $M(x)$ will halt and accept
  - If $x in.not L$, then $y in L$, which means that $M(y)$ halts and accepts

== Part 4

We build a TM which "hardcodes" in its states each one of the elements of $L$, such that, on
each input $x$, the TM will test it against all other elements of $L$: if it finds a match it
accepts, if not it rejects. Since $L$ is finite, the definition of this TM is also finite.

== Part 5

If $L <=_m A_"TM"$ then there exists $f(x)$ such that $x in L <==> f(x) in A_"TM"$.
Then we can build a TM which recognizes $L$ as follows:
- On input $x$:
- Compute $angle(M, w) = f(x)$, which is an instance of $A_"TM"$.
- Simulate $M(w)$ and return whatever it returns.
This is a recognizer since if $x in L$ then $f(x) in A_"TM"$ which means that $M(x)$ will accept.
If $x in.not L$ then $f(x) in.not A_"TM"$ and either $M(w)$ will reject or it will not halt.

If $L in "RE"$, then we can define $f(x) = angle(M, x)$ where $M$ is a recognizer for $L$. Then if
$x in L$ will result in $M(x)$ accepting therefore $angle(M, x) in A_"TM"$, if $x in.not L$ will
result in $M(x)$ rejecting or hanging forever, which means that $angle(M, x) in.not A_"TM"$.

= Exercise 4

== Part 1

In this case $C$ is the set of all languages of length $5$.
Note that $C$ is not empty (indeed there exists some language of length 5), $C subset "RE"$ since it
is a finite language (therefore $C in R$ and $R subset "RE"$).

We can then apply Rice's theorem and get that $L_1$ is undecidable.

== Part 2

Here we cannot apply Rice's theorem since $C = "RE"$.

== Part 3

We cannot apply Rice's theorem as $L_3$ is not a language in the form of Rice's theorem.
