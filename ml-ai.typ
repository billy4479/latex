#import "lib/template.typ": *
#import "lib/theorem.typ": *
#import "lib/utils.typ": *

#show: template.with(
  titleString: "Machine Learning &\nArtficial Intelligence",
  author: "Giacomo Ellero",
  date: "A.Y. 2025/2026",
)

#show: thm-init

= Supervised learning

Let the training set be
$
  S = ((x^mu, y^mu))_(mu in [m]) wide cases(
    delim: #none, "where" x in cal(X)\, y in cal(Y),
    "and" m in NN "is the number of samples"
  )
$
Usually $cal(X) in RR^N$ is the input set, while $cal(Y)$ is the label set which could be ${-1, 1}$,
some categories e.g. ${"cat", "dog", "human", ...}$ (we assign a number to each label in this case,
usually using a one-hot encoded vector).

== Probabilistic approach

Assume that $(X^mu, Y^mu)$ are random variables, but in this case $mu = 1, ...$ is infinite, however
we have only observed a finite number of realizations of these variables (e.g. $1$ to $m$). Then we
are given the $m + 1$ realization but just for $X^(m + 1)$ and we want to describe the probability
distribution of $Y^(m + 1)$.
$
  prob(Y^(m + 1) = y | (X^mu, Y^mu) = (x^mu, y^mu) "for" mu in [m], X^(m + 1) = x) = med ?
$
for brevity we will write $prob(y | S, x)$.

=== Classical ML Theory <sec:classical-ml-theory>

This is a *frequentist* approach: we assume that samples are i.i.d. and that there exists a true
distribution $cal(D)$. This means that $S tilde D^m$.
$
    cal(D)_x (x) & = sum_(y in cal(Y)) cal(D) (x, y) wide &    "marginal" \
  cal(D) (y | x) & = (cal(D)(x, y)) / (cal(D)_x (x)) wide & "conditional"
$

This means that $prob(y | S, x) = cal(D) (y | x)$.

We also add a *deterministic assumption*: $exists f: cal(X) -> cal(Y)$ such that
$cal(D) (y | x) = bb(1)_(y = f(x))$, implying $f(x) = argmax_y cal(D)(y | x)$.

Given a candidate $h: cal(X) -> cal(Y)$ we measure the error as
$
  R_(cal(D))(h) = prob_(cal(D)_x) (h(x) != f(x)) = EE_(cal(D)_x) [bb(1)_(h(x) != f(x))]
$
This is called the *true risk*, but it is unknowable. We focus on the *empirical risk* instead.
$
  R_S (h) = 1/m sum_(mu in [m]) bb(1)_(h(x^mu) = y^mu)
$

We want to minimize the empirical risk, we want to find an algorithm
$
  "ERM": (cal(X) times cal(Y))^m -> cal(Y)^cal(X)
$
where $cal(Y)^cal(X)$ is the set of functions from $cal(X)$ to $cal(Y)$.
We want that
$
  "ERM"(S) in argmin_h R_S (h) = h_S
$
(if there are multiple minima we just pick one).

However considering the whole $cal(Y)^cal(X)$ can be misleading, since then we can easily construct
a function which classifies correctly just the training sample (but nothing else) which will have
$R_S = 0$. To avoid this problem we consider a different $cal(H) subset cal(Y)^cal(X)$ and we look
for minimizers of $"ERM"$ just within $cal(H)$.

=== PAC-bounds

We want that, $forall epsilon, delta in (0, 1)$
$
  prob_(cal(D)^m) ["error measure" <= epsilon] >= 1 - delta
$

We say that an hypothesis space $cal(H)$ is PAC-learnable if
$
  & exists cal(A): (cal(X) times cal(Y))^m -> cal(H), \
  & exists m_(cal(H)): (0, 1)^2 -> NN \
  "s.t." & \
  & forall (epsilon\, delta) in (0\, 1)^2 \
  & forall cal(D)_x \
  & forall f "realizable in" cal(H) \
  ==>&
  m >= m_cal(H) (epsilon, delta) => prob_(cal(D)^m) [R_(cal(D)) (cal(A)(S)) <= epsilon] >= 1-delta
$
where $m_cal(H)$ is a function that, given the required $epsilon$ and $delta$ gives us the desired
number of samples.

This is very powerful in theory, however the realizability assumption usually does not hold,
realizability means that
$
  exists h^* in cal(H) wide "s.t." R_(cal(D))(h^*) = 0
$

#theorem[
  Every finite hypothesis class $cal(H)$ is PAC-learnable, with $cal(A) = "ERM"_cal(H)$ and
  $
    m_(cal(H))(epsilon, delta) = ceil((log(abs(cal(H))/delta))/epsilon)
  $
]<thm:pac-learnable-finite>

#proof[
  We will work on the equivalent expression
  $
    prob_(cal(D)^m) [R_(cal(D)) (h_S)) > epsilon] <= delta
  $
  and set a series of upper bounds until we reach $abs(cal(H)) e^(-m epsilon)$ and then we impose
  $<= delta$ so that we get the result.

  Let us define the set of "bad" hypothesis and the set of misleading training set:
  $
    cal(H)_B & = {h in cal(H) | R_(cal(D)) (h) > epsilon} \
           M & = {S | exists h in cal(H)_B, R_S (h) = 0} \
             & = union.big_(h in cal(H)) {S | R_S (h) = 0}
  $
  We obtain that $h_S in cal(H)_B => S in M$. Then
  $
    prob_(cal(D)^m) [R_(cal(D)) (h_S)) > epsilon] & = prob_(cal(D)^m) [h_S in cal(H)_B] \
    & <= prob_(cal(D)^m) [S in M] \
    & = prob_(cal(D)^m) [union.big_(h in cal(H)) {S | R_S (h) = 0}] \
    & <= sum_(h in cal(H)_B) prob_(cal(D)^m) [R_S (h) = 0] \
    & = sum_(h in cal(H)_B) product^m_(mu = 1) prob_(cal(D)^m) [h(x^mu) = f(x^mu)] \
    & = sum_(h in cal(H)_B) (prob_(cal(D)^m) [h(x^mu) = f(x^mu)])^m \
    & < sum_(h in cal(H)_B) (1 - epsilon)^m \
    & <= abs(cal(H)) (1 - epsilon)^m \
    & <= abs(cal(H)) e^(-m epsilon)
  $
]

#definition(title: [Shattering])[
  Given a set of inputs $C =(x^mu)_(mu in [m])$ and an hypothesis class of binary classifiers
  $cal(H)$, we say that $cal(H)$ shatters $C$ if every possible labeling of $C$ is realizable in
  $cal(H)$.

  Equivalently, given any set of labels $(y^mu)_(mu in [m]) in {-1, +1}^m$ and a true assignment
  $h_T (C) -> (y^mu)$, we have
  $
    forall (y^mu), h_T, quad exists h in cal(H) quad "s.t." h(x^mu) = h_T (x^mu) quad
    forall x^mu in C
  $
]

#definition(title: [VC-dimension])[
  Let $cal(H)$ be an hypothesis class. Then, its VC-dimension is the maximal size of a set $C$ which
  can be shattered by $cal(H)$.
]

To show that $"VCdim"(cal(H)) >= d$ we must prove that $exists C$ such that $abs(C) = d$ and for all
possible labelings of $C$ $cal(H)$ contains a correct classifier.

To show that $"VCdim"(cal(H)) = d$ we must prove that $exists.not C$ such that $abs(C) = d + 1$ and
$cal(H)$ shatters $C$.

To prove that a hypothesis class cannot shatter a certain set $C$ we want to find a set of labels
$(y^mu)_(mu in [m])$ such that there is no classifier in $cal(H)$ which is able to classify a
certain input according to $y^mu$.

#example(title: [VC-dimension of perceptrons in $RR^2$])[
  The VC-dimension of a perceptron on $RR^2$ is $3$.
  - If $abs(C) = 1$ we can always find an hyperplane which classifies correctly that single point.
  - If $abs(C) = 2$ we can always find an hyperplane which classifies all the possible 4 cases
    (either hyperplane external to both points or in between them, flip sign as needed).
  - If $abs(C) = 3$, taking any $C$ different from 3 points on a line, we can always find a
    hyperplane.
  - If $abs(C) = 4$, for any $C$ we can construct a labelling which is an instance of the XOR
    problem.
]

#theorem[
  An hypothesis class $cal(H)$ is PAC-learnable if and only if its $"VCdim"(cal(H)) = d$ is finite,
  with $cal(A) = "ERM"_cal(H)$ and
  $
    m_(cal(H))(epsilon, delta) = ceil((log 1/delta + d log 1/epsilon)/epsilon)
  $
]

#proof[ Not needed. ]


=== Removing determinism

At the beginning of @sec:classical-ml-theory, we introduced an assumption on determinism. We now
remove it. This does not remove deterministic models, but just allows non-deterministic ones.
Then the true risk is
$
  R_(cal(D)) (h) = EE_(x, y tilde cal(D)) [bb(1)_(h(x) tilde y)]
$

#remark[
  Even if our true distribution is non-deterministic, $h: cal(X) -> cal(Y)$ is still a deterministic
  function, looking for a full distribution is an unnecessary complication.
]

#proof[
  The idea is that, given the distribution of $cal(D)(y | x)$, the best non-deterministic classifier
  $p: (cal(X), cal(Y)) -> [0, 1]$ which minimizes the error is
  $
    p(y | x) = cases(1 wide & y = argmax_(y') cal(D)(y' | x), 0 wide & "otherwise")
  $
]

In this new situation we will always have an intrinsic error, defined as
$
  epsilon_"intrinsic" = R_(cal(D)) (h_(cal(D))^"opt") > 0 wide "where"
  h_"opt" = argmin_(h in cal(Y)^cal(X)) R_(cal(D)) (h)
$
This is error is unavoidable and comes from the fact that the input data does not give us enough
information to learn the label with enough accuracy.

#definition(title: [Agnostic PAC-learnable])[
  $cal(H)$ is agnostic PAC-learnable if
  $
           & exists cal(A): (cal(X) times cal(Y))^m -> cal(H), \
           & exists m_(cal(H)): (0, 1)^2 -> NN \
    "s.t." & \
           & forall (epsilon_"est"\, delta) in (0\, 1)^2 \
           & exists cal(D) \
           & forall f "realizable in" cal(H) \
       ==> & m >= m_cal(H) (epsilon, delta) ==>
             prob_(cal(D)^m) [R_(cal(D)) (cal(A)(S))
               <= epsilon_"intr" + epsilon_"app" + epsilon_"est"]
             >= 1-delta
  $
  where
  $
    epsilon_"app" = R_(cal(D)) (argmin_(h in cal(H)) R_(cal(D)) (h)) - epsilon_"intr" > 0
  $
]

Note that all these 3 components of the error come from different phenomena: $epsilon_"intr"$ comes
from the distribution of the data itself; $epsilon_"app"$ comes from the approximation which our
classifier makes (can be reduced by increasing the VC-dimension of $cal(H)$); $epsilon_"est"$ is the
we can reduce by increasing the number of samples and optimizing the classifier better, note that
sometimes this can increase as the VC-dimensiosend them to people who missedn of $cal(H)$ grows due to over-fitting.o

This theory is very pessimistic. Usually in real life the number of samples needed is much lower.

Moreover, according to this theory, LLMs, which have a huge VC-dimension should have an
$epsilon_"est" > 1$ and should not be able to classify anything. This is because
@thm:pac-learnable-finite tells us that if $epsilon <= (log abs(cal(H)))/m$, we lose all confidence,
since the bound for the probability becomes larger than 1.

== Bayesian optimization

We know that
$
  cal(D) (x, y) = cal(D)_x (x) cal(D) (y | x)
$
and that we want to find $cal(D) (y | x)$. But we don't have to start from scratch: sometimes we
know some information about the data, therefore we can use some prior.

We choose to fit $cal(D) (y | x)$ according to some parametric family of distributions
$overline(p)_theta : cal(X) -> [0, 1]^abs(cal(Y))$

#example(title: "Perceptron")[
  In a perceptron we have that
  $
    hat(y)_(overline(w), b) (overline(x))= "sign"(overline(w) dot.op overline(x)) + b)
  $
  therefore our $p_theta$ could be
  $
    p_(overline(w), b)^y = exp(y (overline(w) dot.op overline(x) + b))/(exp(
      overline(w) dot.op
      overline(x) + b
    ) + exp(- overline(w) dot.op overline(x) + b))
  $
  where we exponentiate so that we get a positive probability and the denominator is the
  normalization.

  Then to find the bayesian optimal we look for
  $
    argmax_(y = plus.minus 1) p^y_(overline(w), b) (overline(x))
    & = argmax_(y = plus.minus 1) y (overline(w) dot.op overline(x) + b) \
    & = hat(y)_(overline(w) dot.op overline(x) + b)
  $
]

As we can see this does not help us with classification, since, as we saw before, the classification
is done by a deterministic function. However it is relevant if we care about the distribution.

Given a training set $S$ we have that, by using Bayes theorem,
$
  prob(y | S, overline(x)) & = integral dd(theta) prob(y | theta, overline(x))
                             prob(theta | S) \
                           & = integral dd(theta) dot.op p^y_theta (overline(x))
                             (prob(S | theta) prob(theta))/ prob(S)
$
Then we can compute
$
  prob(S | theta) & = product_(mu in [m])
                    prob((overline(x)^mu, y^mu) | theta) \
                  & = product_(mu in [m]) prob(overline(x)^mu | theta)
                    prob(y^mu | theta, overline(x^mu)) \
                  & = product_(mu in [m]) cal(D)_x (overline(x)^mu)
                    p^(y^mu)_theta (overline(x)^mu) \
          prob(S) & = integral dd(theta) prob(S | theta) prob(theta) \
                  & = (product_(mu in [m]) cal(D)_x (overline(x)^mu))
                    integral dd(theta) (product_(mu in [m]) p_theta^(y^mu) (overline(x)^mu))
                    prob(theta)
$
And substituting from above we get
$
  prob(y | S, overline(x)) & = integral dd(theta) dot.op p^y_theta (overline(x)^mu)
                             (prob(S | theta) prob(theta))/ prob(S) \
                           & = (integral dd(theta) dot.op p^(y^mu)_theta (overline(x)^mu)
                             dot.op prob(theta) (product_(mu in [m])
                               p^(y^mu)_theta (overline(x)^mu)))
                             / (integral dd(theta) dot.op prob(theta) (product_(mu in [m])
                               p_theta^(y^mu) (overline(x)^mu))) \
                           & = EE[p^y_theta (overline(x))]
$
where the $cal(D)_x$ term simplified. To see that the this is actually an expectation we isolate
$dd(theta) dot.op p_theta^y (overline(x)^mu)$ in the numerator, then everything else is a "weight"
depending on $theta$.

However note that the space of parameters $theta in Theta$ might be extremely large, and computing
those integrals numerically is basically impossible.

We will resort to some approximation. Start by rewriting the denominator
$
  prob(theta) (product_(mu in [m]) p^(y^mu)_theta (overline(x)^mu))
  = exp(-m underbracket(cal(L)^"XEnt"_S (theta) - 1/m log prob(theta), phi(theta)))
$
where
$
  cal(L)^"Xent"_S (theta) &= -1/m sum_(mu in [m]) log p_theta^(y^mu) (overline(x)^mu) \
  & = 1/m sum_(mu in [m]) ( - sum_y q^mu_y log p_theta^(y^mu) (overline(x)^mu)) \
  & = 1/m sum_(mu in [m]) H(overline(q)^mu, overline(p)_theta (overline(x)^mu)) \
$
where $overline(q)^mu$ is the one-hot encoded version of $y$ and $H$ is the cross entropy. This is
useful since the cross entropy of a one-hot encoded probability is the $D_"KL"$ divergence.

Now observe that as $m -> oo$ we have that $cal(L)^"XEnt"$ is of order 1, hence it "should" converge
to some value, while the prior (the part with $prob(theta)$) becomes less and less important.
Also, in the large limit, our probability will concentrate towards the minimum of $phi(theta)$ and
we could approximate the expectation as
$
  EE[p^y_theta (overline(x))] & approx p^y_(theta^*) (overline(x)) \
  "where" wide theta^* & in argmin_theta phi(x) \
  & = argmin_theta (cal(L)^"XEnt"_S (theta) - 1/m log prob(theta))
$

This is a very crude approximation. A way to refine it is to use all the global minima we find for
$theta$ and averaging them out.

To summarize until now:
+ Get a dataset $S$.
+ Choose a parametrical model $overline(p)_theta$.
+ Choose a prior $prob(theta)$.
+ Compute $theta^* = argmin_theta phi(theta)$ (THIS IS THE HARD PART), max-a-posteriori.
+ Find the Bayes optimal $hat(y)_(theta^*) (overline(x)) = argmax_y p^y_(theta^*) (overline(x))$
  (this is usually easy to compute).

=== Multilayer perceptron

This is the first step: choosing $overline(p)_theta$.

#theorem(title: [Universal approximation])[
  Let $K subset.eq RR^N$, a function $g: K -> RR$ and a precision $epsilon > 0$.
  Then, there exists a 1-hidden layer network $f: K -> RR$ such that
  $
    sup_(x in K) abs(f(x) - g(x)) < epsilon
  $

]

#definition(title: [Multilayer perceptron])[
  A multilayer perceptron is a function $f: cal(X) subset.eq RR^N -> cal(Y)$ such that $cal(Y) = K$.

  Fix $L$ the number of layers and $N_ell$ be the size of each layer at $ell = 0, 1, ..., L$, in
  particular $N_0 = N$ and $N_L = K$.

  Let $overline(x)^0 = overline(x)$, then the *pre-activation* value is
  $
    overline(z)^ell = W^ell overline(x)^(ell - 1) + overline(b)^ell
  $
  where $W^ell$ is a $N_ell times N_(ell - 1)$ matrix, $overline(x)$ is a vector with dimension
  $N_(ell -1)$ and $overline(b)^ell$ is a vector with dimension $N_ell$.

  Then the *activation* value is
  $
    overline(x)^ell = cases(
      overline(z)^ell wide & "if" ell = L,
      sigma(overline(z)^ell) wide & "otherwise"
    )
  $
  where $sigma: RR -> RR$ is a possibly non-linear function which gets applied element-wise.

  Then, we want our network to output probabilities, therefore we pass $overline(x)^L$ to a softmax
  function.
  $
    f(overline(x)) = p^y_theta (overline(x)) = exp(x^L_y)/(sum_(y in cal(Y)) exp(x^L_y))
  $
]

#remark[
  The softmax function is called like that since, if we add a parameter $alpha > 0$
  $
    exp(alpha x^L_y)/(sum_(y in cal(Y)) exp(alpha x^L_y))
  $
  and let $alpha -> oo$ we get actually the $argmax$ function.

  In our neural network we don't need to include $alpha$ since it is included in the weights of the
  last layer.
]

Now that we have this model we want to compute the cross entropy.
$
  cal(L)^"XEnt"_mu = - log p_theta^(y_mu) (overline(x)^mu) = - x^L_(y^mu) + log sum_y' exp(x^L_(y'))
$

=== Optimizing

Now we want to find the $theta^*$ which minimizes the cross entropy.
In general we will look for $overline(x)^* = argmin f(overline(x))$, in our specific case
$overline(x) = theta$ and $f = cal(L)^"XEnt"_S$.

The main approach is an iterative one: at $t = 0$ we pick an initial guess $overline(x)^0$ and at
$t = 1, 2, ...$ let $overline(x)^(t + 1) = overline(x)^t + delta overline(x)^t$.
This is a very general problem description: how do we choose the initial guess? when do we stop? how
to choose $delta$?
