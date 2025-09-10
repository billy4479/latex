#import "@preview/headcount:0.1.0": *
#import "@preview/great-theorems:0.1.0": *


#let makeThm = (name, color, darken: 0%) => {
  let counter = counter("thm_" + name)

  return mathblock(
    blocktitle: [#name],
    prefix: count => text(color.darken(darken))[*#name #count*],
    counter: counter,
    numbering: dependent-numbering("1.1", levels: 1),
    titlix: title => text(color.darken(darken))[ #title

    ],
    fill: color.lighten(90%),
    stroke: (left: 3pt + color),
    inset: (
      y: 8pt,
      left: 3pt + 8pt,
      right: 8pt,
    ),
  )
}

#let makeProof = name => {
  return mathblock(
    blocktitle: name,
    prefix: [_#name._],
    // suffix: place(bottom + right, $square$), // https://github.com/jbirnick/typst-great-theorems/issues/8
    suffix: [#h(1fr) $square$],
  )
}

#let theorem = makeThm("Theorem", red)
#let proposition = makeThm("Proposition", orange)
#let lemma = makeThm("Lemma", purple)
#let corollary = makeThm("Corollary", maroon)
#let definition = makeThm("Definition", blue)
#let example = makeThm("Example", green)

#let proof = makeProof("Proof")
#let solution = makeProof("Solution")
#let model = makeProof("Model")
