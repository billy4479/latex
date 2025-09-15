#import "lib/template.typ": template
#import "lib/theorem.typ": *

#show: template.with(
  title: "Mathematical Modelling for Finance",
  author: "Giacomo Ellero",
  date: "A.Y. 2025/2026",
)

#show: great-theorems-init

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

