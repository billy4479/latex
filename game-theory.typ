#import "lib/template.typ": template
#import "lib/utils.typ": *
#import "lib/theorem.typ": *
#show: template.with(
  titleString: "Mathematical Modelling for Finance",
  author: "Giacomo Ellero",
  date: "A.Y. 2025/2026",
)

#show: thm-init

= Introduction

*Game theory* is the study of strategic interactions.
A strategic interaction is one where the action of one player affects the other(s) player(s) and
vice versa.

Meanwhile *mechanism design* is kind of reverse game theory: we need to design the rules for other
people to play.

= Representation of Static Games

A static game is a game where everybody knows all the rules and all the outcomes.
To define one of these games we need the following elements:
- The actual players
- Actions that a player can take
- Which outcomes actions lead to
- A preference over outcomes

== Formal definitions

Then we define a *static game* as
$
  G = angle.l I, Y, (A_i)_(i in I), g, (v_i)_(i in I) angle.r
$
where
- $I$ is the set of players
- $Y$ is the set of outcomes
- $A_i$ the (non-empty) set of actions for each player $i$
- $g$ is a function $g: times A_i -> Y med forall i in I$ which associates each action to a
  consequence (where $times A_i = A_1 times ... times A_N$)
- $v_i: Y -> RR$ is the vNM utility function of each player $i$

Then, we will denote by $Delta (X)$ the set of probability measures $mu$ over a _finite_ set $X$
and $"supp" mu = {x in X | mu(x) > 0}$ to be the support of the probability measure $mu$.

Usually we can summarize a static game just with
$
  G = angle.l I, Y, (A_i, u_i)_(i in I) angle.r
$
where $u_i: times A_i -> RR$ is player's $i$ payoff function, defined as $u_i = v_i compose g$.

In lotteries, we have the space of probabilities over the outcomes $Y$ is denoted by $Delta (Y)$ and
a player prefers one lottery over another if the expected win is greater.

Note though that we only have $Delta (A)$ i.e. the distribution over action profiles. But moving
from actions to outcomes is easy, since we can exploit our function $g$:
- Define $g^(-1)$, the inverse of $g$. Then $g^(-1)(y)$ is the set of actions profiles inducing
  outcome $y$
- Define the *push forward function* $hat(g): Delta (A) -> Delta (Y)$. Then,
  $
    hat(g)(mu)(y) = mu(g^(-1) (y))
  $
  where $hat(g)(mu)(y)$ is the likelihood that outcome $y$ realizes if the distribution over action
  probabilities is $mu$, and $mu(g^(-1) (y))$ is the probability that $g^(-1)(y)$ realizes.

Therefore, given $mu_1, mu_2 in Delta(A)$ being lotteries over actions, we get
$
  mu_1 attach(succ.tilde, br: i) mu_2
  & <==> sum_(y in Y) hat(g)(mu_1)(y) v_i (y) >= sum_(y in Y) hat(g)(mu_2)(y) v_i (y) \
  & <==> sum_(y in Y) sum_(a in g^(-1) (y)) mu_1(a) v_i (g(a)) >= sum_(y in Y) sum_(a in g^(-1) (y)) mu_2(a) v_i (g(a)) \
  & <==> sum_(a in A) mu_1(a) u_i (a) >= sum_(a in A) mu_2(a) u_i (a) \
  & <==> EE_(mu_1) [u_i (a)] >= E_(mu_2) [u_i (a)]
$

#definition(title: "Finite static game")[
  A static game $G$ is finite if, for all players $i in I$, the action set $A_i$ is finite.
]

#definition(title: "Compact-continuous game")[
  A static game $G$ is compact-continuous if, for all players $i in I$, the set of actions $A_i$ is
  a compact subset of $R^(k_i)$ with $k_i in NN$, and the payoff function $u_i: A -> RR$ is
  continuous.
]

== Justifiable actions

#example[
  A soccer player has to shoot. He can choose to shoot on the right (R), center (C) or left (L).
  At the same time the goalkeeper can choose to jump either right (R) or left (L).

  If the player shoots in the center there is a $0.6$ probability of scoring independently from
  where the goalkeeper chooses to jump; if the player shoots in the same direction of the goalkeeper
  jump there is a $0.4$ probability of scoring, while if he shoots in the opposite direction there
  is a $0.9$ probability of scoring.
]

#model[
  We will play as the player and show that we should never shoot at the center.

  For starters, we don't know the probability distribution of what the goalkeeper will do, therefore
  we will graph our probability of scoring (depending on what we do) based on the probability of the
  goalkeeper jumping to the right.

  #figure(
    image("assets/game-theory/goal-keeper-graph.svg", width: 70%),
    caption: [
      Graph of the utility of the shooter w.r.t. the probability that the goalkeeper jumps to the
      right. Blue is "shoot to the right", red is "shoot to the left", green is "shoot to the
      center".
    ],
  )

  As we can see, no matter the probability of the goalkeeper jumping to the right, we are always
  better off by choosing to shoot on one side or another rather than in the center.
]

#definition(title: "Conjecture")[
  The conjecture of some player $i$ is $mu^i in Delta(A_(-i))$ which is what player $i$ thinks is
  the distribution over actions of other players.
]

In the previous example, no matter the conjecture, it is always better to choose a side rather than
shooting in the middle.

#definition(title: "Mixed action")[
  A mixed action $alpha_i$ by player $i$ is a probability distribution over the set of action $A_i$
  where $alpha_i (a_i)$ denotes the probability that action $a_i in A_i$ is taken.
]

If the distribution is degenerate (i.e. $alpha_i (a_i) = 1$ and $0$ for all actions different from
$a_i$) we say that the action is *pure*.

A conjecture for a certain action is true if $mu^j (a_i) = alpha_i (a_i)$.

We say that a mixed action $alpha_i^*$ is the best reply to conjecture $mu^i$ if
$
  alpha_i^* in limits("arg max")_(alpha_i in Delta(A_i)) med u_i (alpha_i, mu_i)
$
note that there might be more than one.
Therefore, we can define the *best-reply correspondence* $r_i: Delta(A_(-i)) arrows A_i$ as
$
  r_i (mu^i) = A_i inter limits("arg max")_(alpha_i in Delta(A_i)) med u_i (alpha_i, mu_i)
$

We say that an action is *justifiable* if there exists a conjecture for which that strategy is the
best reply.

#lemma[
  Fix a player $i in I$ and a conjecture $mu_i in Delta (A_(-i))$ and a mixed action $alpha_i^*$.
  Then $alpha^*_i$ is a best reply to $mu^i$ if and only if for every pure action in the support of
  $alpha^*_i$ is the best reply to $mu^i$.

  $
    alpha^*_i in limits("arg max")_(alpha_i in Delta(A_i)) med u_i (alpha_i, mu_i) <==> "supp"
    alpha^*_i subset.eq r_i (mu^i)
  $
]

#proof[
  First we prove that if $alpha_i^*$ is a BR against $mu_i$ then $"supp"(alpha_i^*)$ is a BR too.

  We prove it by contrapositive, i.e. we want to show that
  if $exists a_i in "supp"(alpha_i^*)$ that is not a BR given $mu^i$, then $alpha^*_i$ is dline is next Tuesdaynot a BR
  given $mu^i$.

  If $alpha_i^*$ is not a BR given $mu_i$ then
  $
    exists a_i ' in A_i : u_i (alpha_i^*, mu^*) < u_i (a_i^*, mu^i)
  $

  Consider the mixed action
  $
    alpha_i' (a_i) = cases(
      0 & wide "if" a_i = a_i^*,
      alpha_i (a'_i) + alpha_i^* (a_i^*) & wide "if" a_i = a'_i,
      alpha_i^* (a_i) & wide "if" a_i != a^*_i \, a_i',
    )
  $
  but then the difference in utility is
  $
    u_i (alpha_i^*, mu^i) - u_i (alpha_i', mu^i) =
    alpha_i^* (a_i^*) (u_i (a_i^*, mu_i) - u_i (a_i', mu^i)) < 0
  $
  by definition of $a_i'$, implying that $alpha_i^*$ is not the best reply.

  Now we prove the second implication: if $"supp" alpha_i^* subset.eq r_i (mu^i)$ then $a_i^*$ is a
  BR against $mu_i$.

  Let $overline(u)_i = max_(alpha_i in Delta (A_i)) u_i (alpha_i, mu^i)$

  TODO: see Lemma 3.1, page 18 of lecture notes
]

#lemma[
  If there exists an optimal action there exists also an optimal pure action.
]

#proof[
  TODO: see Lemma 3.2, page 19
]

#definition(title: "Domination")[
  A (mixed) action $alpha_i$ dominates a pure or mixed action $beta_i$ if, independently from the
  choices of other players, it yields a strictly higher payoff.
  $
    u_i (alpha_i, a_(-i)) > u_i (beta_i, a_(-i)) wide forall a_(-i) in A_(-i)
  $
]

We denote the set of actions which are *not dominated* by any other action as
$
  "ND"_i = A_i without { a_i in A_i |
    exists alpha_i in Delta(A_i),
    a_(-i) in A_(-i),
    u_i (alpha_i, a_(-i)) > u_i (beta_i, a_(-i)) }
$

#lemma(title: [ND Action $<==>$ Justifiable Action])[
  Fix player $i$ and an action $a^*_i in A_i$. There exists a conjecture $mu_i in Delta(A_(-i))$
  such that $a_i^*$ is the best reply to $mu^i$ if and only if $a_i^*$ is not dominated by any mixed
  action.

  Thus the set of undominated pure actions and the set of justifiable actions coincide:
  $
    "ND"_i = r_i (Delta (A_(-i))
  $
]

#proof[
  TODO: Lemma 3.3, page 20
]

From this lemma we learn that every rational player always chooses undominated actions and that each
undominated action is justifiable as a best reply to some belief.

#example(title: "Linear Public Good Game")[
  Consider a community composed of $n$ individuals.
  With an input of $x$, a public good can be produced according to $y(x) = k x$ and $k in (1/n, 1)$
  ($x$ and $y$ have the same monetary unit).
  Each individual $i$ has wealth $W_i > 0$ and can choose how much money to contribute to the
  production of the public good: $a_i in A_I = [0, W_i]$.

  Therefore, the payoff function for each individual is
  $
    u_i (a_1, ..., a_n) = W_i - a_i + k sum^n_(j=1) a_j
  $
]

#definition(title: "Cautious player")[
  A player $i$ is cautious if their conjecture does not rule out any $a_(-i) in A_(-i)$.

  The space of all cautious conjectures for player $i$ is
  $
    Delta^C (A_(-i)) = {mu^i in Delta (A_(-i)) | "supp" mu^i = A_(-i)}
  $
]

A player which is both rational and cautious chooses action within $r_i (Delta^C (A_(-i)))$.

#definition(title: "Weak domination")[
  A mixed action $alpha_i$ weakly dominates another mixed action $beta_i$ if it yields at least the
  same expected payoff for every action profile $a_(-i)$ of the other players and strictly more for
  at least one $hat(a)_(-i)$:
  $
    forall a_(-i) in A_(-i), wide u_i (alpha_i, a_i) >= u_i (beta_i, a_(-i)) \
    exists hat(a)_(-i) in A_(-i), wide u_i (alpha_i, a_i) > u_i (beta_i, a_(-i)) \
  $
]

The set of non weakly dominated actions is denoted by $"NWD"_i$.

#lemma()[
  In _finite_ games
  $
    r_i (Delta^C (A_(-i)) = "NWD"_i
  $
]

= Elimination of Dominated Actions

We assume *complete information*, that is, the rules of the game and everyone's preferences are
common knowledge.


#definition(title: "Common knowledge")[
  A fact is common knowledge if everyone knows the fact, everyone knows that everyone knows the
  fact, and so on.
]

We know that there if a player is rational he will never choose actions which are dominated by some
other, but what happens if player $i$ believes that all other players are also rational?
The set of action profiles which are reasonable to be played by others (weakly) shrinks, therefore,
every conjecture of player $i$ $mu^i$ which assigns a non-zero probability to some action
$a_j in A_j$ which dominated by some other action $alpha_j in A_j$ is immediately discarded, since
it is not consistent with player's $i$ belief.

We will define the set of *rationalizable actions* as the set of actions which are compatible to the
common knowledge of rationality.

== Notation

Let $R_i$ denote the _event_ that player $i$ is rational, then $R = inter.big_(i in I) R_i$ denotes
the event that all players are rational.
Let $"ND" = times_(i in I) "ND"_i$ be the set of all non-dominated action profiles, then $"ND"$ is
the set of action profiles compatible with the event $R$.

Let $E$ denote a generic event. If everybody believes $E$, then we write $B(E)$. If everyone
believes that everyone believes $E$ we write $B(B(E)) = B^2(E)$ and so on.

We want to study the action profiles which are compatible with the sequence of events
$
  R inter B(R), wide R inter B(R) inter B^2(R), wide ..., wide R inter (inter.big^K_(k = 1) B^k (R))
$

Consider the set $A = times_(i in I) A_i$ and let $cal(C) subset.eq cal(P)(A)$ be a collection of
action profiles.
Each element of $cal(C)$ is a set
$
  C = { times_(i in I) C_i | C_i subset.eq A = times_(i in I) A_i}
$

#example[
  In a $3 times 3$ with two players game we have that there are $2^3 - 1 = 7$ action profiles (the
  $-1$ comes from the removal of the empty set), then $abs(cal(C)) = 7^2 = 49$.
]

#definition(title: "Rationalization oeperator")[
  Let $Delta(C_i)$ denote the set of conjectures $mu^i$ such that $mu^i (C_(-i)) = 1$.
  Let the set of justifiable conjectures for actions profiles in $C_(-i)$
  $
    r_i (Delta (C_(-i)) = union.big_(mu^i | mu^i (C_(-1)) = 1) r_i (mu^i)
  $
  The map $rho : cal(C) -> cal(C)$ defined as
  $
    rho(C) = times_(i in I) r_i (Delta (C_(-i)))
  $
]

Note that $rho (A)$ is just the set of justifiable actions (i.e. consistent with event $R$) and by
iterating $rho(rho(A))$ is the set of actions consistent with $B(R)$ and so on.

== Iterated applications of $rho$.

#remark[
  - The statement $rho(C) subset.eq C$ is *not* true in general.
  - The rationalization operator is monotone: let $E, F in cal(C)$ such that $E subset.eq F$, then
    $rho(E) subset.eq rho(F)$.
]

#lemma[
  For every $k in NN$, $rho^(k + 1) (A) subset.eq rho^k (A)$.
]
#proof[
  Proceed by induction. We know that $rho(A) subset.eq A = rho^0(A)$.
  Then we have that
  $
    rho^(t + 1) (A) = rho(rho^t (A)) subset.eq rho(rho^(t-1)(A)) = rho^r (A)
  $
  by the induction hypothesis $rho^t (A) subset.eq rho^(t -1) (A)$ and by monotonicity of $rho$.
]

#definition(title: "Rationalizable action profiles")[
  Let
  $
    rho^oo (A) = inter.big_(k >= 1) rho^k (A)
  $
  denote the set of rationalizable action profiles, that is, the set of action profiles compatible
  with the _common knowledge_ of rationality.
]

We have that the sequence $(rho^k(A))_(k in NN)$ is a decreasing sequence in a finite game,
therefore it must converge.

#theorem[
  If $G$ is a finite game, then there exists a positive integer $K$ such that
  $rho^(K+1) (A) = rho^K (A) = rho^oo (A) != nothing$.
]


= Nash Equilibrium

#definition(title: [Nash Equilibrium])[
  An action profile $a^*$ is a NE if for every $i in I$ the action $a^*_i$ is the best reply against
  the conjecture $mu^i (a_(-i)^*) = 1$.
]

Nash equilibrium requires that all players hold correct conjectures about all other players actions.
NE is compatible with common knowledge of rationality.

To find the Nash Equilibrium in finite games we fix one player and iterate over all other players'
actions and mark the best reply to each one. Repeat the process for each player: NE are the action
profiles where there is a mark for each player.

#example(title: [Cournot Competition])[
  $N$ firms compete in a market and have to choose the quantity of a certain product to produce
  $q_i in [0, overline(q)]$.
  The utility of each firm is given by
  $
    u_i (q_i, q_(-i)) = q_i P(q_1, ..., q_N) - C_i (q_i)
  $

  It is common knowledge that the firms maximize expected profit, the price function $P$ and all the
  cost functions $(C_i)_(i in I)$.
]

#solution[
  Consider the simple case where $N = 2$, we want to find the Nash Equilibrium.

  Each firm $i$ wants to maximize its own quantity $q_i$, then, the best reply function is just the
  first order condition:
  $
    q_i^(B R) (q_(-i)) = (1 - q_(-i) - c) / 2
  $
  To find the Nash equilibrium we need to find the intersection of the two best reply functions.
]

== Existence of Nash equilibrium

Let $r_i: A_(-i) arrows A_i$ be the best reply correspondence and let $r: A arrows A$ be the
joint best-reply correspondence:
$
  r(a) = times_(i in I) r_i(a_(-i)) wide forall a in A
$
this correspondence delivers the best reply for each player given the action profile $a$.

Nash Equilibria are fixed-points in the best-reply correspondence.

#theorem(title: [Existence of NE in compact-continuous games])[
  Let $G$ be a compact-continuous game. If, for all $i in I$, $A_i$ is convex and the function
  $u_i (dot, a_(-i)) : A_i -> RR$ is quasi-concave for every $a_(-i) in A_(-i)$ then $G$ has a Nash
  Equilibrium.
]

#proof[
  Not required.
]

=== Finite games

In finite games we can get some cases where no _pure_ NE exists, however it can be shown that it is
always possible to find a _mixed_ NE.

#definition(title: [Mixed extension of finite games])[
  Given a finite game $G = angle.l I, (A_i, u_i)_(i in I) angle.r$ we define the mixed extension
  $macron(G) = angle.l I, (Delta(A_i), macron(u)_i)_(i in I) angle.r$ with
  $
    macron(u)_i (alpha) = sum_(a in A) u_i (a) product_(j in I) alpha_j (a_j)
  $
]

#theorem[
  Every finite game $G$ has at least one mixed Nash equilibrium.
]

#proof[
  This is just a matter to prove that finite games satisfy all the requirements for existence of NE
  in compact-continuous games.
]

=== Finding a Nash Equilibrium

Recall that, given a mixed strategy $alpha_i$ where pure strategies $a'_i$ and $a''_i$ have
non-zero probability, $alpha_i$ is the best reply to some conjecture $mu^i$ only if
$u(a'_i, mu^i) = u(a''_i, mu^i)$.

We can proceed as follows:
1. Fix player $i$ and the pure actions $a_i$ this player is mixing over;
2. Find the conjectures about the other players' actions that make player $i$ indifferent between
  actions $a_i$;
3. Repeat for all players;
4. Impose that the conjectures are correct and player follow the computed conjectures.

= Correlated Equilibrium

We will discuss how players can coordinate based on some external random signal to maximize utility.
The external signal makes sure that the decision is still "fair" to all players.

#definition(title: [Correlated Equilibrium])[
  A correlated equilibrium is a list $angle.l Omega, prob, (T_i, tau_i, sigma_i)_(i in I) angle.r$
  where
  - $(Omega, p)$ is a finite probability space;
  - The sets $T_i$ are finite;
  - The functions $tau_i : Omega -> T_i$ and $sigma_i : T_i -> A_i$ are such that
    $
          & forall i in I, forall t_i in T_i,
            "if " p({omega' in Omega : tau_i (omega') = t_i}) > 0 \
      ==> & sum_(omega in Omega) p(omega | t_i) u_i (sigma_i (t_i), sigma_(-i) (tau_(-i)
              (omega)) \
          & >= sum_(omega in Omega) p(omega | t_i) u_i (a_i), sigma_(-i) (tau_(-i) (omega)) wide
            forall a_i in A_i
    $
]

This definition tells us that if some external event $omega in Omega$, then the function $tau_i$
gives to the player a signal $t_i$, then given the signal the function $sigma_i$ gives back the
action that players have agreed they would play on a certain signal.
Finally, $p(omega | t_i)$ is the belief of player $i$ that the world in state $omega$ after having
observed $t_i$.

== Finding a correlated equilibrium

Since we are looking for equilibria, players have no incentive to deviate from the strategy,
therefore we should assume that all players respond correctly to the signals.
To enforce this intuition we write $sum_(i in I) abs(A_i)$ inequalities, one for each action every
player can take, for each chance it has to deviate from the agreed strategy, for every player.
$
  & sum_(a_(-i) in A_(-i)) p(a_i, a_(-i)) u_i (a_i, a_(-i)) wide &\
  >= & sum_(a_(-i) in A_(-i)) p(a_i, a_(-i)) u_i (tilde(a)_i, a_(-i)) wide & \
  & & forall tilde(a)_i in A_i without {a_i} \
  & & forall a_i in A_i \
  & & forall i in I \
$<eq:ce-constraints>
where the left part of the inequality is the payoff if player $i$ follows the strategy and the right
part is the payoff if it deviates; $tilde(a)_i$ represents the deviation while $gamma(a_i, a_(-i))$
represents the probability that the signal to play $(a_i, a_(-i))$ is displayed.
Moreover, we have to impose
$
               p(a) & > 0 wide forall a in A \
  sum_(a in A) p(a) & = 1
$<eq:ce-constraints-prob>
so that they form a probability distribution.

Then, we want to maximize some sort of global utility function, which, for example, could be the
$
  max_(p(a) med forall a in A) sum_(a in A) (p(a) (sum_(i in I) u_i (a)))
$
This utility function is just the weighted average of all the utilities of all players, with
an equal weight, of course we could have different ones too, for example if we wanted to advantage a
player over another.

From here it is just a matter of solving an optimization problem, in $2 times 2$ games this is
easily solvable by hand since we would have only 4 constraints from @eq:ce-constraints and, since
$abs(A) = 4$, we would also have only 5 constraints from @eq:ce-constraints-prob

#remark(title: [Computational cost])[
  While Nash Equilibrium is a PPAD-hard problem, the computation of correlated equilibrium is
  trivial: it is just an optimization problem with linear equations on a convex set. There are
  algorithms which guarantee convergence in linear time.
]

= Incomplete information

We will analyze the so called Aumann model for incomplete information.
Let $Omega$ be the set of states of the world, we will assume $Omega$ is finite.
Then consider $cal(F)_i$ for all $i in I$, each one being a partition of $Omega$. Each element of
$cal(F)_i$ is the set of the states of the world that player $i$ cannot discriminate between.

Let $A subset Omega$ be an event. Then, player $i$ knows $A$ if $cal(F)_i (omega) subset.eq A$. We
denote all such states, i.e. all the states $omega$ in which $i$ knows $A$, as
$
  K_i (A) = {omega in Omega | cal(F)_i (omega) subset.eq A}
$

#definition(title: [Common knowledge])[
  Let $A$ be an event and $omega in A$ be the state of the world. Then $A$ is common knowledge in
  $omega$ if for every finite sequence of players $i_1, ..., i_m$ where holds
  $
    omega in K_(i_1) ( K_(i_2) (... (K_(i_m) (A))))
  $
]

#theorem[
  If an event $A$ is common knowledge in $omega$ and if there exists $omega' in cal(F)_i (omega)$
  for some $i in I$, then the event $A$ is common knowledge also in $omega'$.
]
