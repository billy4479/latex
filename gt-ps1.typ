#import "lib/template.typ": template

#show: template.with(
  titleString: "Game Theory - Problem Set 1",
  author: "Giacomo Ellero - 3243701",
  date: "23/09/2025",
  header: false,
  nameInFooter: false,
  toc: false,
  font: "New Computer Modern",
)

#set heading(numbering: none)
#set math.equation(numbering: "(1)")

= Exercise 1

Assume that in the game "Problem Set 1" there are two players, me and my friend: denote the set of
players $ I = {"me", "friend"} $

For all $i in I$ the set of actions we are allowed to choose from is defined as
$ A_i = {"individual", "cooperate"} $

The utility for each player is given by the following table
#block(width: 100%)[
  #set align(center)
  #table(
    columns: (auto, auto, auto),
    table.header([], [*individual*], [*cooperate*]),
    [*individual*], [10, 10], [9, 5],
    [*cooperate*], [5, 9], [9, 9],
  )
]

Therefore our static game is fully defined by
$
  (I, (A_i)_(I in i), (u_i)_(i in I))
$
where $u_i$ is the utility function for each player and it takes values as described in the table
above.

My reasoning for assigning these payoffs is that this first problem set is simple enough that even a
single player by itself can reason around it and hopefully get a good grade without the need of a
team mate. I will also argue that, since a single player is able to complete the problem set by
itself, the effort of collaborating with another person actually causes the utility of the case
where both players cooperate to be lower than the case where they both complete it individually.

Meanwhile, if one of the players decides to freeride, the player who chooses to collaborate will
have to spend more time and effort trying to collaborate with someone who doesn't want to, therefore
has a lower payoff, while the freerider gets a higher payoff since it still got a decent mark
without doing any work.

= Exercise 2

It can be easily seen that the only justifiable action in this game is to play individually.
This is because, no matter what the other player does, playing individually yields consistently
better.
Moreover, if we assume that both player are rational, both players will choose to work individually,
therefore both of them will also obtain the best possible payoff.

Note that this conclusion is only possible because of the assumption that the problem set is easy
enough for one player to do it by itself, if the problem set was harder, longer, or involved some
calculations and proofs, players would probably benefit more from collaborating, therefore the
payoffs would be different and so would be the conclusion on which strategy is best.

