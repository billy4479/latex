#import "lib/template.typ": template

#show: template.with(
  titleString: "Game Theory - Problem Set 2",
  author: "Giacomo Ellero - 3243701",
  date: "24/11/2025",
  header: false,
  nameInFooter: false,
  toc: false,
  font: "New Computer Modern",
  bigHeading: false,
  pageBreaksAfterHeadings: false,
)

#set heading(numbering: none)
#set math.equation(numbering: "(1)")

= Exercise 1

The introduction to the podcast shows with an example that the knowledge of something is often
enough to reach the desired outcome of a game.

Note however, contrary to what is written in the introductory paragraph, common knowledge of
rationality is not enough to end up in the correct Nash equilibrium. Indeed, common knowledge of
rationality implies we will end up playing a Nash equilibrium but without further assumptions we
cannot determine _which_ Nash equilibrium will be played.

Let us represent the game as follows:

#figure(
  table(
    columns: (auto, auto, auto),
    table.header([], [*R*], [*L*]),
    [*R*], [1, 1], [0, 0],
    [*L*], [0, 0], [1, 1],
  ),
  caption: [Payoff matrix of the boat-collision game.],
)<table:payoff>

Indeed, if both boats choose to go in the same direction the collision is avoided and both players
get a payoff of $1$, while if they choose opposite directions the boats collide and both players get
a payoff of $0$.

Indeed both R and L are rational moves, as they are the best reply to some conjecture.
Moreover, we have two pure Nash equilibria $(R, R)$ and $(L, L)$ and a mixed one, where players
choose $R$ or $L$ with probability $1/2$. However, even with common knowledge of rationality,
players have no way of knowing which Nash equilibrium to play.

Instead, if both players have common knowledge that they should prefer $(R, R)$ to $(L, L)$, we end
up in a situation where we always get a payoff of $(1, 1)$.

= Exercise 2

If one captain (say captain A) knew the rule but doesn't know whether the other captain (captain B)
knows the rule or not, we are still in a situation where A doesn't know which one is the correct
conjecture on the actions of B.

Therefore A cannot be sure of which Nash equilibrium B wants to play. Player A may even choose to
deviate from the rule if they believe that B is more likely to play $L$. In general we will get a
lower expected payoff because of this uncertainty.

= Exercise 3

We have a static game with the set of players $I = {A, B}$, actions $A_i = {R, L}$ for all $i in I$,
and payoff matrix as in @table:payoff.

Indeed $(R, R)$ is a Nash equilibrium, since, given the correct conjecture that the other player is
playing $R$, there is no incentive to deviate.

= Exercise 4

The issue of private knowledge is exactly that player $A$ doesn't know how to choose which
equilibrium to play. Knowing what _I_ should play, doesn't help me determining the correct
conjecture about what the _other_ player is going to do.

On the contrary, common knowledge of the rule makes sure both players hold correct conjectures on
what the other player is going to do and, since the rule is designed such that if both players play
accordingly we to end up in one of the "best" NE, we end up in such NE.


