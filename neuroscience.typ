#import "lib/template.typ": *
#import "lib/theorem.typ": *
#import "lib/utils.typ": *

#show: template.with(
  titleString: "Mathematical Modelling for Neuroscience",
  author: "Giacomo Ellero",
  date: "A.Y. 2025/2026",
)

#show: thm-init

= Neural coding

We choose a certain neuron and, when a stimulus is shown to the subject, we record the activity of
that neuron.
We will try to answer the following questions:
- How much information is contained in a single neuron (or a population of neuron) response? How
  many neurons do I need to obtain a certain information?
- Is there an optimal way of transmitting information?
- Are neurons close to this optimal way?


