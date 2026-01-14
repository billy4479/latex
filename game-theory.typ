#import "lib/template.typ": *
#import "lib/utils.typ": *
#import "lib/theorem.typ": *
#show: template.with(
  titleString: "Game Theory &\n Mechanism Design",
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
  G = angle(I, Y, (A_i)_(i in I), g, (v_i)_(i in I))
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
  G = angle(I, Y, (A_i, u_i)_(i in I))
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
  Given a finite game $G = angle(I, (A_i, u_i)_(i in I))$ we define the mixed extension
  $macron(G) = angle(I, (Delta(A_i), macron(u)_i)_(i in I))$ with
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
  A correlated equilibrium is a list $angle(Omega, prob, (T_i, tau_i, sigma_i)_(i in I))$
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

== Aumann model

#definition(title: [Aumann model])[
  An Aumann model consists of three components $angle(I, Omega, (cal(F)_i)_(i in I), p/2)$:
  - $I$ is a finite set of players.
  - $Omega$ is a finite set of states of the world.
  - $cal(F)_i subset cal(P)(Omega)$ is a partition of $Omega$ for each player $i$
]

Each element of $cal(F)_i$ is the set of the states of the world that player $i$ cannot discriminate
between.
With the notation $cal(F)_i (omega)$ we denote the element of $cal(F)_i$ which contains $omega$.

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

In this model, either a player knows $A$ or it knows that it doesn't know $A$.

#theorem[
  If an event $A$ is common knowledge in $omega$ and if there exists $omega' in cal(F)_i (omega)$
  for some $i in I$, then the event $A$ is common knowledge also in $omega'$.
]

#proof[
  TODO: Lemma 8.1
]


=== Graph representation

Construct a undirected graph $G = (V, E)$ as follows:
- $V = Omega$ i.e. there's a vertex for each state of the world
- Then, $(omega, omega') in E$ if $exists i in I$ who cannot discriminate between $omega$ and
  $omega'$, i.e. $omega' in cal(F) (omega)$.
- It is useful to consider some function which associates an edge to the set of players that require
  it
- Let $C(omega)$ denote the connected component which contains $omega$.

#proposition[
  An event $A$ is common knowledge in $omega$ if and only if $C(omega) subset.eq A$.
]

#corollary[
  In the state $omega$, $C(omega)$ is common knowledge and it is the smallest event which is common
  knowledge in $omega$.
]

=== Belief

#definition(title: [Aumann model with belief])[
  An Aumann model with belief is an Aumann model where we add an extra component $p$:
  a probability distribution over $Omega$ such that $p(omega) > 0$ for all $omega in Omega$.

  The distribution $p$ is shared between all players.
]

#proposition[
  Each player $i$ knows an event $A$ in state $omega$ if it attributes a probability of $1$ to that
  event.
  $
    P(A | F_i (omega)) = 1 <==> F_i (omega) subset.eq A
  $
]

#theorem(title: [Aumann])[
  Consider an Aumann model of incomplete with two players $I = {1, 2}$ and an event
  $A subset.eq Omega$.
  Consider also two events
  - $Q_1$ is the event that player $1$ assigns probability $q_1$ to event $A$
  - $Q_2$ is the event that player $2$ assigns probability $q_2$ to event $A$

  If $Q_1$ and $Q_2$ are both common knowledge in $omega$, then $q_1 = q_2$.
]

#proof[TODO.]

TODO: complete here

== Harsanyi model

#definition(title: [Harsanyi model])[
  An Harsanyi game of incomplete information is given by the following list
  $
    angle(
      I, Theta_0,
      (Theta_i)_(i in I), p, S, (s_theta)_(theta in times_(i in I union {0}) Theta_i)
    )
  $
  where:
  - $I$ is a finite set of players.
  - $Theta_0$ it a finite set of _types_ for a fictitious player $0$.
  - $Theta_i$ is a finite set of _types_ for player $i$.
  - $p in Delta(Theta)$ where $Theta = times_(i in I union {0}) Theta_i$ and $Delta(Theta)$ is the
    set of distributions over $Theta$. Each type profile $theta in Theta$ is assigned with strictly
    positive probability.
  - $S$ is the set of states of nature, where each element $s$ is a game
    $angle(I, (A_i, u_i)_(i in I))$
  - $s_theta = angle(I, (A_i(theta), u_i(theta))_(i in I))$ is the _stage game_ which is played for
    type profile $theta in Theta$.
]

Each set $Theta_i$ is private to player $i$, therefore players don't know each others' type.
At the same time, all players don't know about which type of the world $theta_0 in Theta_0$ will be
drawn.
The probability distribution $p$ is common knowledge.

=== Bayesian equilibrium

#definition(title: [Strategy])[
  A strategy $sigma_i$ of a player $i$ is a function which maps the players' type to a distribution
  over the feasible actions for that type.
  $
    sigma_i : Theta_i -> Delta(A_i)
  $
]

This means that each player may have different actions available depending on their type.

#definition(title: [Bayesian equilibrium])[
  A Bayesian Nash equilibrium is a strategy profile $sigma^* = (sigma_i^*)_(i in I)$ such that
  $
    sigma^*_i (theta_i) in argmax_(sigma_i) EE[u_i (sigma_i (theta_i), sigma^*_(-i)) | theta_i] wide
    cases(
      delim: #none,
      forall i in I,
      forall theta_i in Theta_i
    )
  $
]

In this definition, a strategy must be optimal for all possible typo realizations of all players.

=== Nash equilibrium in incomplete information games

In Bayesian equilibrium, each player $i$ chooses a strategy $sigma_i$ _after_ having realized which
type $theta_i$ he is.

However, we can also analyze what is the best strategy _before_ knowing the realization of its own
type.
Let us define the expected ex-ante utility of player $i$:
$
  U_i (sigma_i, sigma_(-i)) = sum_(theta_i in Theta_i) p(theta_i) sum_(theta_(-i) in Theta_(-i))
  p(theta_(-i) | theta_i) u_i (theta_i, theta_(-i), sigma_i, sigma_(-i))
$<eq:ex-ante-utility>

#definition(title: [Nash equilibrium with incomplete information])[
  A Nash equilibrium in an incomplete information game is the strategy profile
  $(sigma^*_i)_(i in I)$ such that
  $
    sigma_i^* in argmax_(sigma_i) U_i (sigma_i, sigma^*_(-i)) wide forall i in I
  $
]

#theorem()[
  In a finite game of incomplete information $G$, a strategy profile $(sigma_i^*)_(i in I)$ is a
  Bayesian equilibrium if and only if it is also a Nash equilibrium.
]

#proof[
  First note that @eq:ex-ante-utility can be written as
  $
    U_i (sigma_i, sigma_(-i)) & = sum_(theta_i in Theta_i) p(theta_i) dot
    EE[u_i (theta_i, theta_(-i), sigma_i, sigma_(-i)) | theta_i] \
    & = sum_(theta_i in Theta_i) p(theta_i) dot
    underbrace(
      EE[u_i lr(size: #150%, (sigma_i (theta_i), sigma_(-i))) | theta_i],
      text("Bayesian expected utility")
    )
  $
  where we are highlighting that strategies $sigma$ are maps from the space of types $Theta$ to the
  space of distributions over actions $Delta(A)$.

  Moreover, we note that we can find the Bayesian expected utility within the ex-ante utility.
  This means that if $sigma^*$ is a Bayesian equilibrium, by definition, it maximizes the expected
  utility function for each $theta_i in Theta_i$: for all $sigma_i: Theta_i -> Delta(A_i)$ we have
  $
    EE[u_i lr(size: #150%, (sigma_i^* (theta_i), sigma_(-i)^*)) | theta_i] & >=
    EE[u_i lr(size: #150%, (sigma_i (theta_i), sigma_(-i)^*)) | theta_i] \
    ==>
    p(theta_i) dot EE[u_i lr(size: #150%, (sigma_i^* (theta_i), sigma_(-i)^*)) | theta_i] & >=
    p(theta_i) dot EE[u_i lr(size: #150%, (sigma_i (theta_i), sigma_(-i)^*)) | theta_i] \
    ==> sum_(theta_i in Theta_i) p(theta_i) dot
    EE[u_i lr(size: #150%, (sigma_i^* (theta_i), sigma_(-i)^*)) | theta_i] & >=
    sum_(theta_i in Theta_i) p(theta_i) dot
    EE[u_i lr(size: #150%, (sigma_i (theta_i), sigma_(-i)^*)) | theta_i] \
    ==>U_i (sigma_i^*, sigma^*_(-i)) &>= U_i (sigma_i, sigma_(-i)^*)
  $

  Conversely, suppose that $sigma^*$ is an ex-ante Nash equilibrium, but, by contradiction, assume
  that $exists hat(theta)_i in Theta_i$ with $p(theta_i) > 0$ such that $exists a_i in A_i$ such that
  $
    EE[u_i (a_i, sigma^*_(-i)) | theta_i] > EE[u_i (sigma^*_i (theta_i), sigma^*_(-i)) | theta_i]
  $
  which would mean that $sigma^*$ is not a Bayesian equilibrium.

  However, this means that if we define the strategy
  $
    hat(sigma)_i (theta_i) = cases(
      a_i wide & "if" theta_i = hat(theta)_i,
      sigma^*_i (theta_i) wide & text("otherwise")
    )
  $
  we would have
  $
    U_i (hat(sigma)_i, sigma^*_(-i)) & = U_i (sigma^*_i, sigma^*_(-i))
    + p(theta_i) ( EE[u_i (a_i, sigma^*_(-i)) | theta_i]
      - EE[u_i (sigma^*_i(theta_i), sigma^*_(-i)) | theta_i]) \
    & > U_i (sigma^*_i, sigma^*_(-i))
  $
  contradicting that $sigma^*_i$ is an ex-ante Nash equilibrium.
]

= Multistage games

== Complete information

#definition(title: [Multistage game (extensive form)])[
  A multistage game with perfect information in extensive form is a list
  $
    G = angle(I, (V, E, x_0), (V_i, u_i)_(i in I))
  $
  where
  - $I$ is a finite set of players
  - $(V, E, x_0)$ is the _game tree_ where $V$ is the set of vertices, $E$ the edges and $x_0 in V$
    is the root of the tree. The set of leaves are denoted by $X^ell$. This is a finite tree.
  - $(V_i)_(i in I)$ is a partition of $V without X^ell$. Each $V_i$ denotes the set of vertices
    where player $i$ takes action.
  - $u_i : X^ell -> RR$ is the utility function for player $i$ based on the leaf we end up in.
]

#definition(title: [Subgame])[
  Given a multistage game $G$, a subgame $G(x)$, with $x in V without X^ell$, is the subgraph of
  $(V, E)$ which includes the vertex $x$ and all its descendants.

  Note that $G = G(x_0)$ therefore $G$ is a subgame of itself.
]

To introduce randomness in multistage game we define also a fictitious player which plays the role
of "luck": this player gets assigned some vertices in the graph and it chooses at random between the
available options, according to some common knowledge distribution.

=== Subgame-perfect equilibrium

#definition(title: [Subgame-perfect equilibrium])[
  A strategy profile $sigma$ is a subgame-perfect equilibrium if, for every subgame, the restriction
  to the strategy profile to this subgames, is a Nash equilibrium for that subgame.
]

Note that there could exist Nash equilibria which are not subgame perfect.


== Incomplete information

We will not give a formal definition of incomplete information multistage games, however the idea is
that it is possible that, when it's player $i$ to choose an action, he doesn't know some previous
decision that was taken higher up in the tree (he knows that a decision was taken, he doesn't know
which one). Then the *information sets* is the partition of vertices of player $i$ which he cannot
distinguish between.

= Repeated Games

Simply repeating a game multiple times doesn't mean that we will be able to improve the outcome.

This is because, if the game has a single Nash equilibrium, at the last period every player will
play it since there are no incentive to do otherwise; then, we can recourse backwards and at
every period we are back to playing the same game, where each player will play rationally since
there is no incentive to do otherwise, they cannot change what will be played in the future.
We can generalize this game for every $n$-period game ($n$ finite).

However, if there is more than one Nash equilibrium, at the last period we can "choose" between
which one to play based on what happened in the previous periods.
This intuition helps us to justify formally why is this.

A *strategy* in a repeated game is a function
$
  sigma_i^t : times_(tau in {0, ..., t-1}) A -> A_i
$
where each element of the domain is a "history" of the game $h^t$ i.e. the collection of all actions
profiles played up to $t-1$.
This means that players can choose their next action based on what happened in the previous periods.

This allows us, when we play the game long enough and there are multiple Nash equilibria, to
"punish" or "reward" the other player for choosing a suboptimal action.

To do this we construct a strategy which plays the desired outcome at time $0$ and, at any
subsequent time, it plays one of the Nash equilibria: if the players "cooperated" and chose the
desired action we play for the remaining periods the "best" Nash equilibrium, otherwise we play the
"bad" Nash equilibrium.

When building such strategy we need to have a large enough difference between the payoffs of the
Nash equilibria _or_ we need to play the game a lot of times. If the conditions are satisfied
however, we can use this mechanism to increase the payoff of the desired outcome at time $0$.

However, players may have a discount factor $delta_i in [0, 1]$ which indicates how much they value
the future payoff w.r.t. the present one. Fixed the amount of times we can play the games and the
payoffs we will get an inequality for the minimum $delta$ such that our strategy can be played.

Note that in this way we can construct a repeated Nash equilibrium, however in repeated games there
are often _many_ Nash equilibria. It is hard to predict which one players are going to play and it
may seem counter-intuitive sometimes that players are actually going to play that strategy, however
we just need to check that a certain strategy is the best reply against the correct conjecture that
the other players are also playing according to that Nash equilibrium.

#example[
  Consider a game with payoff matrix
  $
    mat(
      1\,1, -1\, 3;
      3\, -1, 0\,0
    )
  $
  where the $(1, 1)$ payoff is obtained if both players cooperate, while $(0, 0)$ if both defect.

  Assume that this game is played indefinitely: at each round there is a probability of
  $lambda in [0, 1)$ which the game goes on another round.
]

#solution[
  One possible Nash equilibrium in this case is to play "cooperate" at $t = 0$ and if all previous
  actions profiles played $a^(s < t)$ were $("C", "C")$, otherwise we play $"D"$.

  At any time, we want to look at the following inequality:
  $
    u("C", "C") + sum^oo_(tau = 1) lambda^tau u("C", "C") >=
    u("D", "C") + sum^oo_(tau = 1) lambda^tau u("D", "D")
  $
  where on the left we have the expected utility if both players cooperate indefinitely, while on
  the right we have the expected utility if the first players decides to deviate from the strategy
  at some point (from there on the other player will start playing $"D"$ all the times).

  As long as this inequality is valid, rational players will always choose to cooperate.
  Substituting numbers we get:
  $
    1 + sum^oo_(tau = 1) lambda^tau dot 1 >= 3 + sum^oo_(tau = 1) lambda^tau dot 1 \
    1 + lambda / (1 - lambda) >= 3 \
    lambda >= 2/3
  $

  Therefore, for this specific game, we need $lambda >= 2/3$.
]

#definition(title: [One-shot deviation])[
  Fix a strategy $sigma_i$. Then, a one-shot deviation from $sigma_i$ is a strategy
  $hat(sigma)_i != sigma_i$ such that there exists an _unique_ history $tilde(h)^t in cal(H)$ such
  that
  $
     sigma_i (h^t) = hat(sigma)_i (h^t) wide & forall h^t != tilde(h)^t \
    sigma_i (h^t) != hat(sigma)_i (h^t) wide & h^t = tilde(h)^t
  $
]

We say that a one-shot deviation is profitable if at the history $tilde(h)^t$ the expected utility
from playing according to $hat(sigma)_i$ (while other players play according to $sigma_(-i)$) is
higher than sticking to $sigma_i$.

#theorem[
  A strategy profile $sigma$ is a subgame perfect equilibrium in a repeated game if and only there
  are no profitable one-shot deviations for any player $i in I$.
]

#proof[
  If a strategy is a subgame perfect equilibrium it is easy to check that there is no profitable
  one-shot deviation. Indeed, the definition of subgame perfect tells us that at every period $t$
  the strategy $sigma$ makes us play a Nash equilibrium, therefore there is no incentive to deviate.

  The converse is a bit more involved and gets proven by contrapositive.
  We say that if a strategy $sigma$ is not subgame perfect, then there is a one-shot deviation.
  If $sigma$ is not subgame perfect, then there is _some_ profitable deviation $tilde(sigma)$ but it
  might deviate from $sigma$ at multiple points in history.

  At history $tilde(h)^t$ there is the chance to deviate according to $tilde(sigma)$ and earn
  $epsilon > 0$ from this deviation. However, since there is a discount, we can choose to deviate
  from $sigma$ only for $T$ periods and still get some fraction of $epsilon$. Therefore we can
  define $hat(sigma)$ as the strategy which follows $sigma$ up to $tilde(h)^t$, then for the next
  $T$ periods follows $tilde(sigma)$, and finally switches back to $sigma$ for the remaining
  periods.

  This means that at history $tilde(h)^t compose h^T$ one of the two strategies $hat(sigma)$ and
  $sigma$ has a better payoff:
  - Assume that $hat(sigma)$ has a higher payoff than $sigma$. This means that at
    $tilde(h)^t compose h^T$ the two strategy only differ by a one-shot deviation.
    Then
    $
      caron(sigma) = cases(
        tilde(sigma) wide & "at history" tilde(h)^t compose h^T,
        sigma wide & "otherwise"
      )
    $
    is a profitable one-shot deviation.
  - If $sigma$ has a higher payoff that $hat(sigma)$ at $tilde(h)^t compose h^T$, then it means that
    it was not necessary to deviate from $sigma$ for $T$ periods. Let $macron(sigma)$ be the
    strategy which is defined as $hat(sigma)$ but follows $tilde(sigma)$ only for $T-1$ periods.
    We can then proceed by induction and either find the right deviation or reach a contradiction.
]

#theorem[
  Consider a repeated game with discount factor $delta$. Let $a^"NE"$ be a Nash equilibrium in the
  stage game with associated payoff $v^"NE"$. Let $a^*$ be the "desirable" action profile with
  associated payoff $v^*$ that strictly Pareto-dominates $a^"NE"$.

  Consider the strategy
  $
    sigma_i (h) = cases(
      a_i^* wide & "if" h = varnothing "or" h = {a^*, ..., a^* },
      a_i^"NE" wide & "otherwise"
    )
  $

  Then $sigma$ is a subgame perfect equilibrium if and only if
  $
    v_i^* (a^*) >= (1 - delta) sup_(a_i in A_i) v_i (a_i, a_i^*)
    + delta v_i^"NE" wide forall i in I
  $<eq:sgp-condition>

  This means that $sigma$ is subgame perfect if and only if
  $
    delta >= (sup_(a_i in A_i) v_i (a_i, a_i^*) - v_i (a_i^*)) /
    (sup_(a_i in A_i) v_i (a_i, a_i^*) - v_i(a^"NE")) in [0, 1)
  $<eq:sgp-delta-condition>
]

#proof[
  Start by doing some algebra, indeed to prove that @eq:sgp-condition is correct we need
  $
    v_i^* (a^*) & >= (1 - delta) sup_(a_i in A_i) v_i (a_i, a_i^*) +
                  (1 - delta) sum^oo_(t = 1) delta^t v_i (a^"NE") \
                & = (1 - delta) sup_(a_i in A_i) v_i (a_i, a_i^*) +
                  cancel((1 - delta)) delta/cancel(1 - delta) v_i (a^"NE") \
                & = underbrace(
                    (1 - delta) sup_(a_i in A_i) v_i (a_i, a_i^*),
                    "most profitable\none-shot deviation"
                  ) + delta v_i^"NE"
  $
  and isolating $delta$ we get @eq:sgp-delta-condition.

  Moreover, note that, at histories where there was the deviation, the player who deviates always
  plays $a^"NE"$ and since it is a Nash equilibrium there is no profitable one-shot deviation.

  In @eq:sgp-delta-condition where the numerator represents the "temptation" to deviate today and the
  denominator is the "severity" of the punishment.

  The converse implication is skipped.
]

#remark[
  This theorem holds even for more complex strategies (like alternating cooperation and
  deviation at each period).
]

#example(title: [Repeated Cournot duopoly])[
  Consider the Cournot duopoly with demand $p(q_1, q_2) = max {0, 1-q_1 - q_2}$ and zero production
  cost.
  Show that the firms can achieve monopoly profit in a subgame perfect equilibrium if the discount
  factor is high enough.
]
#solution[
  We have that
  $
    u_i(q_i, q_(-i)) = q_i dot p(q_i, q_(-i))
  $
  and that $q_i^"NE" = 1/3$ is a Nash equilibrium with $v_i^"NE" = (1 - 2/3) 1/3 = 1/9$.

  A monopolist would maximize $pi(Q) = Q(1-Q)$ instead, therefore $Q^M = 1/2$ and $v^M = 1/4$.

  Indeed if firms choose $q_1 = q_2 = 1/4$ we get that $q_1 + q_2 = q_M$ and achieve monopolist
  outcome. In this way each firm would earn $pi^M / 2$ (since they need to split the profit),
  however $v_i^M = pi^M / 2 = 1/8 > v_i^"NE" = 1/9$, therefore firms should prefer that outcome over
  the NE.

  We can choose a trigger strategy such that
  $
    q_i = cases(
      1/4 wide & "when in the whole history" q_(-i) = 1/4,
      1/3 wide & "otherwise"
    )
  $

  Then, to find the right $delta$ we need to solve
  $
    pi^M/2 >= (1 - delta) max_(q_i) ((1 - q_i - q^M/2) q_i)
    + (1 - delta) sum^oo_(t = 1) delta^t v_i^"NE"
  $
  with $pi^M = 1/4$ and $q^M = 1/2$. We get
  $
    1/8 >= (1 - delta) max_(q_i) ((3/4 - q_i)q_i) + delta dot 1/9 \
    ==> 1/8 >= (1 - delta) dot 9/64 + delta dot 1/9 \
    ==> delta >= 9/17
  $
]

This example illustrates that we can obtain a collusive outcome even if the two firms do not talk to
each other. In the real world this would be harder to achieve as there are random factor to take
into account which could be interpreted as deviation from the other firm and bring us back to a Nash
equilibrium.

_In theory_, there are some studies which show that it is still possible, even with some randomness,
to achieve a collusive outcome, but in practice these strategies are so complicated that it is very
unlikely for them to be used in practice.

== Folk Theorem

We define the set of *feasible payoffs* as $V = "convex hull"{v | v = u(a), a in A}$.
Then, we define the set of *feasible and strictly rational payoffs* as
$
  V^* = {v in V mid(|) v > max_(a_i) min_(a_(-i)) u(a_i, a_(-i))}
$
where the max-min term is the maximum payoff player $i$ can get if all other players decide to
coordinate and minimize $i$'s payoff.

#theorem(title: [Infinite Nash Folk theorem])[
  Let $v^* in V^*$ for the stage game $G$. Then, there exists $delta$ such that
  $Gamma^(delta, oo)(G)$ has a Nash equilibrium with that payoff.

  TODO: mhh not sure about this one
]

#theorem(title: [Infinite SPE Folk theorem])[
  Same as the first one but with subgame perfect equilibrium. There are also some extra conditions:
  we need for the game to be flexible enough to allow players to "follow through" threats and
  punishments.
]

#theorem(title: [Finitely Nash Folk theorem])[
  In finite multistage games we can achieve a certain payoff if there is a Nash equilibrium which is
  higher than the minmax payoff.
]

#theorem(title: [Finitely SPE Folk theorem])[
  In finite multistage games we can achieve a certain payoff if there are two Nash equilibria with
  two different payoffs.

  This is so we can punish the game even at the last stage.
]

= Social choice

#let prefer = $op(succ)$
#let prefereq = $op(succ.curly)$
#let prefern = n => $prefer^(#n)$

The traditional model of voting there are $i in cal(N)$ citizens and $x in X$ feasible outcomes.
Each citizen has a preference $prefer_i$ over outcomes.

For the beginning of this class we will assume that all the $prefer_i$ are known and all citizens
voted truthfully. We will consider incentives on following the preferences later.
Moreover we assume that $prefer_i$ is complete and transitive for all $i in cal(N)$.

#definition(title: [Social preference])[
  A social preference $Phi$ is a function which goes from the space of preference profiles over $X$
  and $cal(N)$ to a preference over $X$.
]

== Arrow impossibility theorem

#definition(title: [Unanimity])[
  The social preference $Phi$ satisfies unanimity if, $x prefer_i y$ for all $i in cal(N)$ then
  $x prefer_Phi y$.
]

#definition(title: [Independence of irrelevant alternatives (IIA)])[
  Let $x, y in X$ and consider two preference profiles $(prefer_i)_(i in cal(N))$ and
  $(prefer'_i)_(i in cal(N))$ such that
  $
    x prefer_i y <==> x prefer'_i y wide forall i in cal(N)
  $

  Then $Phi$ is IIA if $x prefer_Phi y <==> x prefer'_Phi y$.
]
The idea is that if all citizens prefer $x$ over $y$, then the addition of other elements $z in X$
should not influence the fact that $x$ is preferred to $y$.

#definition(title: [Dictatorship])[
  A social preference $Phi$ is dictatorial if $exists ! i in cal(N)$ such that $x prefer_i y$ then
  $x prefer_Phi y$.
]

#theorem(title: [Arrow, 1951])[
  Assume $abs(X) >= 3$. If $Phi$ satisfies unanimity, IIA and transitivity, then $Phi$ is
  dictatorial.
]

The proof of Arrow's theorem we are going to present was written by
#link(
  "https://papers.ssrn.com/sol3/papers.cfm?abstract_id=275510",
  [Geanakoplos],
)
and uses four mostly independent lemmas to conclude the result.

#let I = $(upright(I))$
#let II = $(upright(I I))$
#let III = $(upright(I I I))$

#remark(title: "Notation")[
  During the proof we will consider three recurrent preference profiles which, for brevity, will be
  named as follows
  $
    #(1, 2, 3).map(n => [$#numbering("(I)", n) = (prefern((#n))_i)_(i in cal(N))$]).join[$, quad$]
  $

  The preference $prefern(#I)_Phi$ is the social preference induced by $Phi$ in the preference
  profile $(prefern((1))_i)_(i in cal(N))$.
]

#lemma(title: [External Lemma])[
  Pick an arbitrary $y in X$. Whenever $(prefer_i)_(i in cal(N))$ is such that
  $
    x prefer_i y "or" y prefer_i x wide forall i in cal(N), forall x in X
  $
  i.e. either $y$ is ranked first or $y$ is ranked last for each individual, then $Phi$ must be such
  that $x prefer_Phi y$ or $y prefer_Phi x$ for all $x in X$ (i.e. $Phi$ places $y$ on the very top
  or in the very bottom).
]

#proof[
  By contradiction, suppose that $Phi$ does not rank $y$ in an extreme location (i.e.
  $x prefer_Phi y prefer_Phi z$ for some $x, z in X$).
  We will show that we can find an individual preference profile $prefer'_i$ such that $Phi$
  violates some assumption.

  Consider the preference profile $(prefer')_(i in cal(N))$ which ranks $z$ above $x$ for all
  $i in cal(N)$ but leaves unaffected the ranking of $y$ against $z$.

  - By IIA, since $x prefer'_Phi y$ we should still have that $x prefer'_i y$ for all $i in cal(N)$.
  - By unanimity we must have that $z prefer'_Phi x$ since $z prefer'_i y$ for all $i in cal(N)$.
  - Combining the above, by transitivity, we have that $z prefer'_Phi x prefer'_Phi y$.

  However this means that now $z$ is chosen over $y$, which was not the case before. This means that
  $Phi$ violates IIA because from $(prefer_i)_(i in cal(N))$ to $(prefer'_i)_(i in cal(N))$ the ranking of $y$
  against $z$ was not affected.
]

#lemma(title: [Extremely pivotal voter])[
  There exists an individual $i^* (y) in N$ and a preference profile $(prefer_i)_(i in cal(N))$ for which
  $i^*(y)$ is an extremely pivotal voter for $y in X$.

  This means that if $i^* (y)$'s preferences change, $i^* (y)$ has the "power" to move $y$ from the
  very bottom of the social preference ranking to the very top.
]

#proof[
  Consider a preference profiled where $x prefer_i y$ for all $x in X$ and for all $i in cal(N)$.

  - By unanimity we have that $x prefer_Phi y$ for all $x in X$.
  - By unanimity, if all $i in cal(N)$ prefer $y prefer_i x$, then we must have that $y prefer_Phi x$ for
    all $x in X$.

  Now proceed iteratively: at each step change the preference of voter $i$ such that $y$ is now the
  first ranked alternative, rather than the last one.

  Note that at each step $y$ remains extremal $forall i$, this means that, by the previous lemma,
  $y$ will still be extremal for $Phi$.

  But by unanimity $y$ should change from the bottom position to the top one. This happens for sure
  when the last voter changes their preference, therefore there exists some citizen $i^*(y)$ where
  the shift in the social preference occurs.

  Denote with #I the preference profile right before $i^* (y)$ changes their preference about $y$
  and #II the preference profile right after.
]

#lemma(title: [Local dictatorship])[
  If an extremely pivotal voter $i^* (y)$ exists, then they are a limited dictator over all the
  pairs of alternatives $x, z in X$ such that $y != x, z$.

  This means that $i^*(y)$ has the "power" to change the social preference outcome for $x$ and $z$.
]

#proof[
  Consider $x, z in X$ as in the statement and construct the preference profile #III as follows:
  modify #2 such that $x prefern((3))_(i^* (y)) y$ for some $x != y in X$ and allow all other
  $i != i^*(y)$ to change their preference with respect to $x, z$, as long as $y$ remains in its
  extreme position.

  Now we analyze what $Phi$ does when we are in $III$:
  - We have that the ranking of $x$ and $y$ hasn't changed from #I for any voter $i in cal(N)$. Then,
    by IIA we can find another preference profile which leaves unchanged the ranking of $x$ and
    $y$ but ranks $y$ at the bottom for each voter. By the extremal lemma, we get that $y$ should
    be an extrema also in $prefern(III)_Phi$ and since the ranking of $x$ and $y$ hasn't changed
    from #I we get that $x prefern(III)_Phi y$.
  - We have that the ranking of $y$ and $z$ hasn't changed from #II for any voter $i in cal(N)$. Then,
    we can repeat the same argument from the previous point, but this time $y$ is ranked on top,
    therefore we get that $y prefern(III)_Phi z$.

  By transitivity we conclude $x prefern(III)_Phi y prefer(III)_Phi z$.
  However, by IIA we have that $x prefern(III)_Phi z$ independently of $y$.
  This conclusion was reached just by moving $x$ on the top of the ranking of $i^* (y)$, while all
  other voter could have chosen their rankings for $x$ and $z$ arbitrary.

  This means that $i^* (y)$ is a local dictator.
]

#lemma(title: [Global dictatorship])[
  The extremely pivotal voter $i^* (y)$ we defined in the previous lemmas is a dictator over all
  pairs of alternatives $x, y in X$
]

#proof[
  Consider a third element $z in X$ and a preference profile $(prefer_i)_(i in cal(N))$ derived from
  #III which places $z$ at the bottom $forall i in cal(N)$.

  In this preference profile we know by the previous lemmas that $z$ must be ranked at the bottom
  of $prefer_Phi$ and that there exists a player $i^* (z)$ who is a local dictator for all
  $u, v in X$ such that $u, v in X without {z}$.

  Assume by contradiction that $i^*(z) != i^*(y)$.

  In the particular case in which $u = x$ and $v = y$ we have that $i^* (y)$ can change the social
  ranking of $x$ and $y$ in preference profiles #I and #II, defined above, but this would
  contradict the fact that $i^*(z)$ is a local dictator, therefore $i^*(z)$ and $i^*(y)$ must be
  the same person.

  Since the choice of $z$ was arbitrary $i^* (y)$ is a global dictator for all pairs $x, y in X$.
]

=== What to give up

We are stuck in a situation where we have to give up some assumption in order to have a
non-dictatorship, despite all the assumptions seem quite reasonable.

Our choices are:
- Violate transitivity, e.g. with majority vote.
- Violate unanimity, such as fixing a social preference without a vote.
- Violate IIA, e.g. with runoff or plurality vote.
- Have a dictator.

We can however put a constraint on the domain of $Phi$.

For example, if we assume all preferences are single-peaked, i.e. $X$ is ordered by $>$ and if
$x > y > z$, then either $y prefer x$ or $y prefer z$ or both, majority rule is a non-dictatorial
social preference which satisfies all the assumptions. (Think like the left-right spectrum).

Moreover if $abs(X) = 2$ plurality vote is also a non-dictatorial social preference which satisfies
all assumptions.

== Strategic voting

We now assume that players have a private preference, hold some conjecture about what are other
players' private preferences, and will play strategically and alter their vote according to their
strategy.

As the designer of this game we want the outcome to be Pareto efficient and non-manipulative (i.e.
we want all players to tell the truth about their preferences).

Equivalently to Arrow theorem, there is also a theorem that the only strategic social voting which
is Pareto efficient and non-manipulative is dictatorship.

= Matching Markets

There are two sides and each side has a preference over the other side.
We are going to cover one-to-one matchings (e.g. marriage, organ donors, ...), while we are not
covering many-to-one matchings (many students go to one school).

In both cases we would want a non-price mechanism to find the match.

== Classical marriage market

Let $M$ be the set of men and $W$ the set of women. A match is a pair of functions
$(mu : M -> W union {u}, nu : W -> M union {u})$ such that if $mu (m) = w$ then $nu (w) = m$ and $u$
represents being single.

This model is just an example, however this setup could be used to model various situations, like
the worker-job market.

#definition(title: [Stable match])[
  A match $(mu, nu)$ is stable if
  - It is *individually rational*: each individual $i in M union W$ prefers their match rather
    than being single.
  - There are *no blocking pairs*: it's impossible that two individual will meet and there find
    out they like each other better than their current match. Formally, there is no couple
    $(m, w)$ such that $w prefer_m mu(m)$ and $m prefer_w nu(w)$.
]

=== Deferred acceptance algorithm

We start the algorithm by setting the set of rejections $R^0 (w) = varnothing$ for all $w in W$.

Then at each round $n$:
- Each woman $w in W$ proposes to her preferred man from the set $M without R^(n - 1)(w)$.
- Each man then accepts the proposal he likes best (if all the proposals he received are worse
  than staying single or if he receives no proposals he stays single for now).
- If the proposal of $w$ was rejected we set $R^n (w) = R^(n - 1) (w) union {m}$ where $m$ is the
  man who $w$ proposed to in this round.
- If the proposal was accepted we keep $R^n (w) = R^(n - 1) (w)$.
The algorithm terminates when no proposals are rejected.

Note that at every round a woman $w$ can be rejected, even if she was accepted by $m$ at the
previous round. This is because at the next round a rejected woman $w'$, which was rejected by
some other man $m'$ at the previous round, could propose to a $m$ and, if $w' prefer_m w$, $w$
will end up being rejected.

#theorem[
  The deferred acceptance algorithm (DAA) always converges in a finite amount of time and the matching
  obtained through it is stable.
]

#proof[
  First, we note that, since both $M$ and $W$ are finite sets, the sets $abs(R^n (w)) <= abs(M)$
  and at each step of the algorithm $abs(R^n (n))$ increases. This means that eventually there
  will be no men to propose to, therefore the algorithm terminates.

  Now we show that the matching is individually rational. Indeed women propose to a men who she
  prefers rather than being single, otherwise she would not propose to him. On the other side, men
  accepts a proposal if he prefers that woman to being single, otherwise he would not accept.

  To show that there are no blocking pairs we reason by contradiction.
  Assume that there is a blocking pair $(m, w)$, i.e. $w prefer_m mu (m)$ and $m prefer_m nu (w)$.
  Then this means that $w$ have proposed to $m$ and she was rejected. There are two options:
  1. $m$ rejected $w$ for $mu(m)$, but this contradicts $(m, w)$ being a blocking pair.
  2. $m$ rejected $w$ for another woman $w'$, but this means that $w' prefer_m w prefer_m mu(m)$
    by transitivity, which contradicts $m$ being matched with $mu (m)$ because $m$ should have
    accepted $w'$ instead.
]

#corollary[
  A stable match always exist.
]

#theorem[
  The DAA algorithm with women proposing matches a women $w$ to a man $m$ such that there is no
  other stable matching where $w$ is matched to a man $m'$ such that $m' prefer_w m$.
]

#proof[
  We say that $m'$ is achievable for $w$ if there is a stable matching in which $m'$ and $w$ are
  matched.
  Assume, by contradiction, that this achievable $m'$ exists such that $m' prefer_w m$.

  Consider a first round where a woman $w$ is rejected by $m'$ for $w'$. This means that
  $w' prefer_(m') w$.
  In turns we have that that $m' prefereq_(w') nu(w')$ because proposals are made in order of
  preference.

  We have that $(m', w)$ can never be a part of a stable matching because then $(m', w')$ would
  form a blocking pair.
]

#corollary[
  The DAA algorithm with woman proposing leads to the worst stable matching for men.
]

== Strategic matching markets

However there is an issue where players have an incentive to give a ranking which is not truthful:
sometimes the receiving part is incentivised to rank being single higher up than their actual
preference, so that they reject a suboptimal candidate which proposes first.

#definition[
  / Matching mechanism: a mapping from the reported preference to a matching.
  / Dominant strategy: a preference report for an individual (given their true preferences) which
    is the best response regardless of other individuals.
  / Strategy-proof: a matching mechanism in which the dominant strategy for all individuals is
    truthfully reporting their preferences.
]

#theorem(title: [Roth, 1982])[
  There is no strategy-proof matching mechanism that always selects a stable matching.
]

= Mechanism design

== Vickrey-Clarke-Groves mechanism

#example[
  The government wants to build an airport. Let $X$ be the set of options and for each $x in X$ have
  an associated cost $c(x)$. Each individual has a private type $Theta_i$.
]

#model[
  We want to maximize
  $
    V(x) = sum_(i in cal(N)) V_i (x)
  $
  if $V(x) <= 0$ the airport will not be built.

  We might want to ask each citizen to evaluate each option $x$, giving us, for each citizen, a
  vector $hat(v)_i in RR^abs(X)$ containing the score of each option and then maximize
  $
    hat(V)(x) = sum_(i in cal(N)) hat(v)_i (x)
  $
  but we might have a problem where citizens are incentivised to misrepresent their preferences.

  We can solve this by giving to each citizen an additional payoff, given by
  $
    t_i (x) = sum_(j != i) hat(v)_j (x)
  $
  so that reporting their actual strategy is a weakly dominant strategy. This is called the VCG
  mechanism.

  This works, however it is very expensive to implement.

  In the model proposed above each citizen gets the same payoff in the end (a part given by their
  preference and one part given by $t_i$).

  To reduce the cost of this design we can select a function $b_i$ which maps others' citizens report
  into a bill to be paid by $i$. The total bill that each citizen $i$ will need to pay is
  $
    b_i (hat(v)_(-i)) - sum_(j != i) hat(v)_j (x)
  $
  this allows us to reduce the cost of the strategy while we are not influencing the report of each
  citizen, since, for each $i$, $b_i$ is constant as it depends on preferences they cannot influence.

  This is mechanism is called the *pivot mechanism*.

  Let us use as $b_i$ the function
  $
    b_i (hat(v)_i) = max{ 0, max_(x in X) sum_(j != i) hat(v)_j (x)}
  $
  where the sum is the value of the socially optimal option without citizens $i$.

  This is a good choice because if the outcome with ($x^*$) or without ($x'$) citizen $i$
  participating changes, then $i$ will pay
  $
    sum_(j != i) hat(v)_j (x') - sum_(j != i) hat(v)_j (x^*)
  $
  i.e. $i$ will pay the change of preference of all other citizens if they are the pivotal voter.

  Since it is optimal for each citizen to truthfully reveal their preference we know that
  $
    V_i (x^*) + sum_(j != i) hat(v)_j (x^*) >= V_i (x') + sum_(j != i) hat(v)_j (x') \
    ==> V_i (x^*) + sum_(j != i) hat(v)_j (x^*) - sum_(j != i) hat(v)_j (x') >= V_i (x')
  $
  which means that $i$ is weakly better if $x^*$ is implemented rather than $x'$, this means that
  there is always an incentive to participating in the mechanism.
]

== Example: selling a coffee

A seller wants to sell a coffee at the highest possible profit and he has a cost function
$c(q) = q^2/2$.

There is just one buyer which has a type $theta in {theta_"high", theta_"low"}$ with
$theta_"high" > theta_"low" > 0$. The buyer's payoff is $theta q - p$.

The seller has a conjecture on the type of the buyer: $P(theta_"high") = mu$.

If the seller knew for sure the type of the buyer we would have a very simple maximization problem
$
  q_i^* = argmax_q (theta_i q - q^2 /2)
$
which gives us as result
$
  cases(
    q_i^* = theta_i,
    p_i^* = theta_i^2
  )
$

But most likely the seller doesn't know the type of the buyer. An intuitive approach would be to
have two items in the menu: a large coffee (which maximizes the seller's payoff when the buyer is
$theta_"high"$) and a small coffee (meant for when the buyer is $theta_"low"$).

However, then each buyer will have an incentive to misrepresent their preference: say $theta =
theta_"high"$. If the buyer buys the small coffee he gets
$
  theta_H q_L - p_L = theta_H theta_L - theta_L^2 \
  ==> underbrace((theta_H - theta_L), >0) underbrace(theta_L, >0) > 0
$

Therefore, in order to maximize my profits as a seller I need to satisfy some constraints:
$
  cases(
    theta_H q_H - p_H & #h(1em)>= & #h(1em) theta_H q_L - p_L wide & "IC-H",
    theta_L q_L - p_L & #h(1em)>= & #h(1em) theta_L q_H - p_H wide & "IC-L",
    theta_H q_H - p_H & #h(1em)>= & #h(1em) 0 wide & "IR-H",
    theta_L q_L - p_L & #h(1em)>= & #h(1em) 0 wide & "IR-L",
  )
$
Where IC-H and IC-L are the *incentive constraints*, i.e. we want that the option the seller
prepared for a certain type of customer is actually more appealing to that type of customer than the
alternative; IR-H and IR-L represent *individual rationality*, i.e. buyers should still get a
non-negative utility from buying coffee.

But not all these constrains are necessary.
#lemma[
  IC-H and IR-L imply IR-H.
]
#proof[
  $
    theta_H q_H - p_H >=^"(IC-H)" theta_H q_L p_L >^(theta_H > theta_L) theta_L q_L - p_L >=^"(IR-L)" 0
  $
]

#lemma[
  IC-H and IC-L imply $q_H > q_L$.
]
#proof[
  Sum IC-H and IC-L and simplify to get
  $
    underbrace((theta_H + theta_L), >0) (q_L - q_H) >= 0 \
    ==> q_H >= q_L
  $
]

#lemma[
  IR-L must hold with equality at optimum.
]
#proof[
  By hypothesis we can find $epsilon > 0$ such that we can increase $p_L$ by $epsilon$ and IR-L
  still holds.

  We also increase $p_H$ by $epsilon$ so that $epsilon$ cancels and we are sure that IC-L and IC-R
  still holds.
  IR-H holds since it is implied by IC-H and IR-L.
]
#lemma[
  IC-H must hold with equality at optimum.
]
#proof[
  Consider $theta_H q_H p_H > theta_H q_L - p_L$, we argue that we can increase $p_H$ by
  $epsilon > 0$.

  $exists epsilon$ since IC-H is still satisfied, IR-L is unaffected and IC-L is still satisfied
  as choosing $(q_H, p_H)$ as $theta_L$ is even less appealing.
]

#lemma[
  IC-H holding with equality and $q_H >= q_L$ together imply IC-L.
]

#proof[
  Write IC-H as
  $
    p_H - p_L = theta_H (q_H - q_L)
  $
  and IC-L as
  $
    p_H - p_L >= theta_L (q_H - q_L)
  $

  This means that
  $
    theta_H (q_H - q_L) >= theta_L (q_H - q_L)
  $
  since $q_H >= q_L$ we get that $theta_H >= theta_L$ which is indeed true.

  Since all these steps are "if and only if" we conclude that IC-L holds.
]

#proposition[
  The constraints reduce to
  $
    cases(
      p_L = theta_L q_L,
      p_H = theta_H q_H - (theta_H - theta_L) q_L
      q_H >= q_L
    )
  $
]
#proof[
  Immediate from the lemmas above.
]

In the new solution we apply a "discount information rent" to $theta_H$, this is needed as an
incentive for $theta_H$ to reveal their true type.

The seller therefore needs to solve
$
  & max_((q_H, q_L)) mu(theta_H q_H - (theta_H - theta_L) q_L - q_M^2 / 2)
    + (1 - mu) (theta_L q_L - q_L^2/2) \
  & "s.t." q_H >= q_L
$
We can just use the first order conditions:
$
  cases(
    q_H^* = theta_H,
    q_L^* = theta_L - mu/(1-mu) (theta_H - theta_L)
  )
$
where $mu$ is the weight of $theta_H$ compared to $theta_L$.

== General definition

There is a way to formally define a mechanism design problem, however, in short, a mechanism is a
tuple $Gamma = (A, (q, t))$, where $A$ is the set of action profiles, $q$ is a function which maps
strategies into outcomes and $t$ is a function which maps strategies to transfers to the designer
(e.g. taxes).

We put the following assumptions:
- The payoff function is quasi-linear: $u_i (theta, q(a), t_i(a)) = u_i(q(a), theta) - t_i(a)$
- The types are independent: $p(theta) = product_(i in I) p_i (theta)$
- The space of types is one-dimensional and convex:
  $Theta_i = [overline(theta), underline(theta)] subset.eq RR$.

=== Bayesian equilibrium mechanism design

For now we assume that players are smart enough to play according to Bayesian equilibrium.

#lemma(title: [Revelation principle])[
  Given a mechanism $Gamma$ and $sigma$ a BNE strategy in $Gamma$, there exists another mechanism
  $Gamma'$ where $A_i = Theta$ for all $i in I$ which has a BNE strategy $sigma'$ such that the
  equilibrium outcome of $sigma$ under $Gamma$ and $sigma'$ under $Gamma'$ coincide.

  Then, $sigma'_i (theta_i) = theta_i$ for all $theta_i in Theta_i$ and for all $i in I$.
]

This means that the designer can optimize just between direct games, i.e. the ones where players are
just asked to reveal a type. This lemma tells us that if we had a BNE in the original mechanism,
players will reveal their true type.

#definition(title: [Bayesian incentive compatibility])[
  A mechanism is Bayesian incentive compatible if $forall i in I$ and $forall theta_i in Theta_i$ we
  have
  $
    sigma_i (theta_i) in argmax_(tilde(sigma)_i) EE[v_i (q (a_i, a_(-i)); theta_i) - t_i (a_i, a_(-i)
      | theta_i, tilde(sigma)_i, sigma_(-i)]
  $
]

This means that for any agent $i$ of type $theta_i$, given that all other agents choose strategies
$sigma_(-i)$, it is optimal for $i$ to choose $sigma_i (theta_i)$.
This is equivalent to saying that the players play according to a Bayesian equilibrium in the game
induced by the mechanism.

We will now prove sufficient and necessary conditions for a mechanism to respect Bayesian incentive
compatibility as in the definition above. Assuming types are IIDs, let $F(theta_i)$ denote the cdf
of the distribution of types $forall i in I$.
We further simplify agents' preferences and assume they are linear in
$theta_i$: $v_i (q; theta_i) = theta_i v(q)$, where $v(q)$ is increasing and weakly concave.

Let $V_i (theta'_i) = theta_i EE[(q_i (theta'_i, theta_(-i))]$ (note that $v(q) = q$) and
$T_i (theta'_i) = EE[t_i (theta'_i, theta_(-i)]$, where expectations are taken over the types of
other agents.


#theorem[
  A direct mechanism $Gamma = (q, (t_i)_(i in I))$ is incentive compatible if and only if for all
  $i in I$:
  - $V_i (theta_i)$ is increasing
  - $forall theta_i in [underline(theta), macron(theta)]$ we have
    $
      T_i (theta_i) = T_i (underline(theta)) + (theta_i V_i (theta_i)
      - underline(theta) V_i (underline(theta)) - integral_(underline(theta))^(theta_i) V_i (x) dd(x)
    $
]

#proof[
  TODO
]

=== Dominant-strategy mechanism design

If instead we assume that players are too stupid to play BNEs we get dominant-strategy mechanism
design, where we only assume that players play weakly dominant strategies.

Turns out that the revelation principle also holds for dominant strategies, therefore the
dominant-strategy incentive compatibility states that each players should play rational strategies.

== Revenue maximizing mechanism design

Here we want to maximize the profit from selling a certain product.

=== Monopoly screening

Consider a single buyer with two possible types, and a seller who has a cost of $C(q) = c q$ with
$c > 0$.
Let the utility that a buyer gets be $theta v(q) - t$ where $t$ is the price for $q$ units. We can
interpret $theta v(q)$ as the "willingness to buy".

Let $v(0) = 0$, $v'(q) > 0$, $v''(q) < 0$ for all $q$. Let $macron(theta) v'(0) > c$ and
$lim_(q -> oo) macron(theta) v'(q) < c$ so that some buyer will buy something but no one will buy an
infinite quantity.

From the theorem above we get that
$
  t(theta) = t(underline(theta)) + (theta v(q(theta)) - underline(theta) v(q(underline(theta)))
  - integral_(underline(theta))^theta v(q(theta)) dd(x)
$
imposing $t(underline(theta)) = underline(theta) v(q(underline(theta)))$ (participation constraint
is satisfied with equality for the lowest type) we get
$
  t(theta) = theta v(q(theta)) - underbracket(
    integral_(underline(theta))^theta v(q(theta)) dd(x),
    "information rent"
  )
$

We can take the expectation over the distribution of $theta$ to get the expected profit
$
  EE[pi(theta)] & = integral_(underline(theta))^macron(theta) (theta v(q(theta)) -
    integral_(underline(theta))^theta v(q(theta)) dd(x) - c q(theta)) f(theta) dd(theta) \
  & = integral_underline(theta)^macron(theta) underbracket(
    (v(q(theta))(theta - (1- F(theta))/f(theta)) - c
      q(theta)), "virtual surplus"
  ) f(theta) dd(theta)
$
where we have done some Fubini magic. This is the seller's profit, the objective they maximize:
$
  max_(q(dot)) EE[pi(theta)] \
  "s.t." q(theta) "is increasing"
$

To solve this problem we first ignore the constraint on $q$, then we check if the $q$ we found is
increasing. If it is we are done, otherwise we cry.

We can find $q$ by maximizing the integral pointwise, i.e. for each $theta$. We compute the
derivative of the integrand and we get:
$
  v'(q(theta)) (theta - (1-F(theta))/f(theta)) - c
$
We have the following cases:
- If $theta - (1- F(theta))/f(theta) < 0$ the expression is always negative, therefore we set
  $q(theta) = 0$.
- Else, if $v'(0) (theta - (1-F(theta))/f(theta)) - c <= 0$ we also set $q(theta) = 0$ as the
  derivative is negative.
- Else, it means that there exists a strictly positive quantity which solves
  $
    v'(q(theta)) (theta - (1-F(theta))/f(theta)) = c
  $

Therefore, the optimal allocation is
$
  q^* (theta) = cases(
    0 wide & "if" display(v'(q(theta)) (theta - (1-F(theta))/f(theta)) - c < 0),
    display({q : v'(q) (theta - (1-F(theta))/f(theta)) = c}) wide & "otherwise"
  )
$

Moreover, a sufficient condition for $q$ to be increasing is that the hazard rate
$f(theta)/(1-F(theta))$ is increasing.

=== Auctions

Consider now a setting where multiple buyers with type
$theta_i in [underline(theta), macron(theta)]$ compete for a single item. Here the allocation rule
$q_i (theta)$ is the probability that the buyer $i$ gets the item.

From the buyer prospective, the expected probability of getting the item is
$
  Q_i (theta) = integral_(Theta_(-i)) q_i (theta, theta_(-i)) f(theta_(-i)) dd(theta_(-i))
$
Let $T_i (theta)$ be the expected transfer for buyer $i$, therefore the buyer expected utility is
$U_i (theta_i) = theta_i Q_i (theta_i) - T_i (theta_i)$.

The seller's revenue is
$
  sum_(i in I) (integral_(Theta_i) q_i (theta_i) (theta_i - (1-F(theta_i))/f(theta_i)) f(theta) dd(theta))
$

As before the virtual surplus is
$
  psi_i (theta_i) = theta_i - (1 - F(theta_i))/(f(theta_i))
$
therefore the optimal allocation rule is
$
  q^*_i (theta) = cases(
    1 wide & "if" i = argmax_(i in I) psi_i (theta_i) "and" psi_i (theta_i) > 0,
    0 wide & "otherwise"
  )
$

