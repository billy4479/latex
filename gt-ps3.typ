#import "lib/template.typ": template

#show: template.with(
  titleString: "Game Theory - Problem Set 3",
  author: "Giacomo Ellero - 3243701",
  date: "01/12/2025",
  header: false,
  nameInFooter: false,
  toc: false,
  font: "New Computer Modern",
  bigHeading: false,
  pageBreaksAfterHeadings: false,
  numberEquationsAtHeader: 0,
)

#set heading(numbering: none)

= Exercise 1

In the scene, Nash takes into account the actions of other players, which inevitably have an effect
on what outcome his friend group get.

When looking for a Nash equilibrium we also want to consider what other players are thinking about
doing (i.e. each player need to hold correct conjectures about other players behavior).

However, while Nash shows to his friends that "individual ambition" does not give the most efficient
payoff, the strategy that he suggests to his friends in the scene is not a Nash equilibrium, since
each player would get a strictly higher payoff by deviating from it.

= Exercise 2

== Formal model

Let $I$ be the set of players. We assign payoffs according to which girl each player end up with:
- $7$ if he get the blonde.
- $5$ if everyone gets any other girl.
- $4$ if he get with some other girl but some other player is able to get with the blonde.
  I chose to decrease the payoff by one in this case compared to the one where everyone goes
  with another girl in order to model envy
  #footnote[
    This $-1$ also helps by making sure that the payoff of the mixed NA strategy is strictly worse
    than the payoff of "no one goes for the blonde".
    This is needed so that, in the repeated game scenario, it is possible to construct a NE which
    actually punishes the player who deviates from the strategy.
    Note that even if this payoff was $5$, the action $a = (O, O)$ wouldn't be a NE.
  ].
- $0$ if they are rejected.

As in the scene, we assume that if at least two players go for the blonde they will be both rejected
and that there are at least $abs(I)$ other girls. Furthermore, we assume that if player $i$ goes for
the blonde they always succeeds if they are the only player going for the blonde, while going for
any other girls results in a success (since there is at least one other girls for each player).

We will focus on the version of this game where $I = {1, 2}$ (payoff matrix in @table:payoff), but
the same reasoning can be applied for any number of players.

#figure(
  table(
    columns: (auto, auto, auto),
    table.header([], [*Blonde*], [*Other*]),
    [*Blonde*], [$0, 0$], [$7, 4$],
    [*Other*], [$4, 7$], [$5, 5$],
  ),
  caption: [Payoff matrix of the generic "blonde girl" game for two players.],
)<table:payoff>

In this formulation we have no pure Nash equilibrium, however we can still find a mixed one.
$
  cases(
    alpha_2 (B) u_1(B, B) + (1 - alpha_2 (B)) u_1 (B, O)
    = alpha_2 (B) u_1 (O, B) + (1 - alpha_2 (B)) u_1 (O, O),
    alpha_1 (B) u_2(B, B) + (1 - alpha_1 (B)) u_2 (O, B)
    = alpha_1 (B) u_2 (B, O) + (1 - alpha_1 (B)) u_2 (O, O),
  ) \
  cases(
    0 alpha_2 (B) + 7(1 - alpha_2 (B)) = 4 alpha_2 (B) + 5(1 - alpha_2 (B)),
    0 alpha_1 (B) + 7(1 - alpha_1 (B)) = 4 alpha_1 (B) + 5(1 - alpha_1 (B)),
  ) \
  cases(
    7 - 7 alpha_2 (B) = 5 - alpha_2 (B),
    7 - 7 alpha_1 (B) = 5 - alpha_1 (B),
  ) \
  cases(
    alpha_2 (B) = 2/6 = 1/3,
    alpha_1 (B) = 2/6 = 1/3,
  )
$
which means players will play "go for the blonde" $1/3$ of the times.
Let us denote this action profile with $alpha_G$, its expected payoff is $u_i (alpha_G) = 5 - 1/3$
for all players $i in I$.

== Making $(O, O)$ a NE

=== Changing the payoffs of existing actions

Of course we always have the option to modify completely the payoffs. For example we could say that
the friends are very empathic, therefore if they all get the payoff of the player which has the
lowest payoff: for this variation we would have the following payoff matrix.
#figure(
  table(
    columns: (auto, auto, auto),
    table.header([], [*Blonde*], [*Other*]),
    [*Blonde*], [$0, 0$], [$4, 4$],
    [*Other*], [$4, 4$], [$5, 5$],
  ),
  caption: [Modification of @table:payoff so that $(O, O)$ is a NE.],
)<table:payoff-mod>

This is just @table:payoff with the payoffs of $(B, O)$ and $(O, B)$ changed so that both players
have the same payoff (as in our definition of empathy before). In this scenario $(O, O)$ is the only
NE, since no player has an incentive to deviate from it.

However this change (to me) feels unnatural and like it completely changes the game being played.

=== Adding an action and repeating the game

If we want to make $(O, O)$ a NE without changing the game completely we can turn this into a
repeated game and add another action
$
  D = "Drink a beer with the boys and ignore the girls"
$

The payoffs of this action are
#figure(
  table(
    columns: (auto, auto, auto, auto),
    table.header([], [*Blonde*], [*Other*], [*Drink*]),
    [*Blonde*], [$0, 0$], [$7, 4$], [$-1, -1$],
    [*Other*], [$4, 7$], [$5, 5$], [$-1, -1$],
    [*Drink*], [$-1, -1$], [$-1, -1$], [$1, 1$],
  ),
  caption: [Payoff matrix of the "blonde girl and drink" stage game for two players.],
)<table:payoff-drink>

The reason these payoffs were chosen with the following reasoning:
- If I play $D$ and everyone else also plays $D$ we are going to have a good time therefore we get a
  positive payoff.
- If I play $D$ but some other player goes for a girl and leaves me alone I'll be sad, get drunk and
  make a mess. At this point the other player will need to clean up my mess and we will both get a
  negative payoff.
This means that to get a positive payoff either all of us go for the girls or we all go drinking
together.

In this formulation of the stage game we have introduced a pure NE: $a_D = (D, D)$. However we still
have that $u_i (a_D) < u_i (alpha_G)$.

Now we allow players to play this game multiple times, for example we say that this group of friends
goes to the bar every night.
Consider the strategy
$
  sigma_i (t) = cases(
    O wide & "if" h^t = {(O, O), ..., (O, O)},
    D wide & "otherwise"
  )
$

We now want to find the discount factor $delta in (0, 1)$ so that this strategy is a subgame-perfect
equilibrium. For that we need to check that following inequality is valid
$
  u_1 (O, O) + sum^oo_(tau = 1) delta^tau u_1 (O, O) >= u_1 (B, O) + sum^oo_(tau = 1) delta^tau u_1 (D, D)
$
(Since the payoffs are the same for player 2, $delta$ will be the same for both players.)

We get that
$
  5 + 5 delta/(1 - delta) >= 7 + delta/(1-delta) \
  delta/(1 - delta) >= 1/2\
  delta >= 1/3
$
therefore when the discount factor is higher than $1/3$ $sigma$ is a subgame-perfect equilibrium
strategy which allows player to get the best outcome $(O, O)$.

Therefore, if we consider the payoff of the repeated game, $(O, O)$ is the only NE.

= Exercise 3

Yes, in the game described in @table:payoff to maximize individual outcome players should play
$alpha_G$, therefore their actions would leave some payoff on the table, meaning this is not a
Pareto efficient solution.

Indeed, if we define the collective utility function as $U(a) = sum_(i in I) u_i (a)$, the only
action profile which maximizes $U$ is $(O, O)$.
