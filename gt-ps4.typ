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

= Exercise 2

== Top trading cycles

Top Trading Cycles (TTC) is an algorithm which works as follows:
- Let $mu_t : S -> U$ be the function which, at each round of the algorithm $t$, assigns a student
  $s in S$ to their university $mu_t (s) in U$. Since every university accepts just one student in
  our simplified model we can invert it to get $mu^(-1)_t : U -> S$.
- At $t = 0$, we set $mu^0$ to be an arbitrary assignment.
- We represent the universities as nodes on a directed graph. Let $V_t$ be the set of vertices of
  the graph at each step $t$, initially $V_0 = U$.
- For each round of the algorithm $t = 1, 2, ...$
  - For each university $u$:
    - Consider the student $s = mu^(-1)_(t-1) (u)$
    - Define $u^* in V_(t-1)$ as the preferred university for student $s$.
    - Draw an edge from $u$ to $u^*$ (if $u = u^*$ we still draw an edge going back to itself)
  - By construction, the graph will always have at least one cycle. For each cycle $C in cal(C)$:
    - If $abs(C) = 1$ we do nothing.
    - For each $(u, u') in C$ and let $s = mu_(t - 1)^(-1) (u)$ and $s' = mu_(t - 1)^(-1) (u')$ be
      the students previously assigned to $u$ and $u'$. Then, following the edge of the graph, we
      set $mu_t (s) = u'$. In this way, every student in the graph "shifts" to his preferred
      university.
  - Set $V_t = V_(t - 1) without (union.big_(C in cal(C)) C)$ (i.e. we remove all the nodes which at $t-1$ are in a
    cycle). These nodes which were removed already had their best possible match.
  - Eventually all nodes will be removed.

By construction, this algorithm is Pareto efficient for students.
However, it takes into account only the students' preferences, not the universities' ones, so we can
easily see that this algorithm is not stable as it is possible to encounter blocking pairs.

Moreover, the final matching is dependent on the initial assignment $mu^0$, which the algorithm does
not tell us how to find.
We also don't know how the order in which cycles should be resolved: indeed solving one before the
other has an impact on the final matching.

We will now demonstrate this algorithm with the example preferences we used in the previous
exercise.

We will start with the configuration
$
  (s_1, u_2), wide (s_2, u_4), wide (s_3, u_1), wide (s_4, u_3)
$

As we can see, in this case, we end up with the (stable) matching
$
  (s_1, u_1), wide (s_2, u_4), wide (s_3, u_2), wide (s_4, u_3)
$
