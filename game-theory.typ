#import "lib/template.typ": template
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

