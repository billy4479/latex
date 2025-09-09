#import "lib/template.typ": template

#show: template.with(
  title: "Mathematical Modelling for Finance",
  author: "Giacomo Ellero",
  date: "A.Y. 2025/2026",
)

= Introduction
Stochastic processes are mathematical tools to model uncertainty and randomness.
We will discuss two types of applications: modelling of stochastic phenomena and computational
algorithms which need a probabilistic approach.

== Formal definition

TODO: translate from latex
```latex
More in particular stochastic processes are probabilistic models for random quantities which
\emph{evolve over time}. Formally a stochastic process is a collection of random variables
\begin{equation}
	\{ X_t \mid \quad t \in T \} \quad \text{or} \quad  (X_t)_{t \in T}
\end{equation}
where $T$ is the index set and
\begin{equation}
	X_t : \Omega \to \mathcal X
\end{equation}

The index space $T$ usually is one of $[0, +\infty)$ (\emph{continuous time}) or $\{1, 2, \dots\}$
(\emph{discrete time}).
Meanwhile $\mathcal X$ can also uncountable (e.g. $\R^d$, giving a \emph{continuous space}) or
finite or countable which gives a \emph{discrete space}.

As an example we can consider $\mathcal X = \R$, $T = [0, +\infty)$ and each realization $X_t$ is a
possible trajectory in the plane $\mathcal X$ $T$. This means that each $X_t$ is a function from $T$
to $\mathcal X$.

\begin{example}{Gambler's ruin}{gamblers-ruin}
	A gambler plays a game where he wins $1$ with probability $p$ and loses with probability $1-p$.

	He starts with $x_0$ money and stops when he reaches $0$ or a prefixed $N$.
\end{example}

\begin{proof}[Model]
	We denote by $(X_t)_{t \in T}$ the stochastic process with $\mathcal X = \{0, 1, \dots, N\}$ and
	$T = \{0, 1, \dots\} = \N$. Each $X_t$ is the \say{trajectory} that the money the gambler own
	takes.
\end{proof}

\subsection{Discrete-time Markov chains}
This is a way to model discrete-time stochastic processes with $n$ random variables.
First we need to specify the law (i.e. the joint distribution)
\begin{equation}
	\mathcal L(X_0, \dots, X_n)
\end{equation}

However, when $n$ is very large it is convenient to decompose it using conditional distributions:
\begin{lemma}{Sequential decomposition}{sequential-decomposition}
	Given a random vector $(X_0, \dots, X_n)$ on $\mathcal X^{n+1}$ we have
	\begin{equation}
		P(X_0, \dots, X_n) = P(X_0 = x_0) \prod^{n-1}_{i = 0} P(X_{i+1} = x_{i+1} \mid X_i = x_i, \dots,
		X_0 = x_0)
	\end{equation}
\end{lemma}

\begin{proof}
	Follows from the definition of conditional probability: we get a telescopic product.
\end{proof}

\begin{corollary}{Simulating stochastic processes}{simulating-stochastic-processes}
	To simulate $(x_0, \dots, x_n) \sim \mathcal L(X_0, \dots, X_n)$ we can
	\begin{itemize}
		\item $X_0 \sim \mathcal L(X_0) \to x_0$
		\item $X_1 \sim \mathcal L(X_1 \mid X_0 = x_0) \to x_1$
		\item ... and so on
	\end{itemize}
\end{corollary}

However this is usually too complex, since the number of random variables we depend on keeps
increasing.

\begin{definition}{Markov chain}{markov-chain}
	A discrete-time stochastic process is a Markov chain if
	\begin{equation}
		P(X_{t+1} = x_{t+1} \mid X_t = x_t, \dots, X_0 = x_0) = P(X_{t+1} = x_{t+1} \mid X_t = x_t)
	\end{equation}
	for all $t \in \N$ and $\forall (X_0, \dots, X_{t+1}) \in \mathcal X^{t+1}$.
\end{definition}

The intuition is that what happened in the system in the past no longer influences the next state,
we just need a snapshot of the current state of the system to be able to make predictions about the
next state.

This basically means that $X_{t+1}\perp (X_0, \dots, X_{t-1}) \mid X_t$, i.e. $X_{t+1}$ is independent
from all previous states once we know $X_t$.

Going back to \cref{ex:gamblers-ruin} we see that it can be modelled using a Markov chain, since the
probability of the gambler's money at the next state $t + 1$ to be $x_{t+1}$ is
\begin{equation}
	\begin{cases}
		p   & \text{if } x_{t+1} = x_t + 1 \\
		1-p & \text{if } x_{t+1} = x_t - 1 \\
		0   & \text{otherwise}
	\end{cases}
\end{equation}
```
