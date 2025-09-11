#import "@preview/headcount:0.1.0": *
#import "@preview/great-theorems:0.1.0": *

#let thmCounter = counter("thm")
#let makeThm = (name, color, darken: 0%) => {
  return mathblock(
    blocktitle: [#name],
    prefix: count => text(color.darken(darken))[*#name #count* #h(0.5em)],
    counter: thmCounter,
    numbering: dependent-numbering("1.1", levels: 1),
    titlix: title => text(color.darken(darken))[ #title

    ],
    breakable: true,
    fill: color.lighten(90%),
    stroke: (left: 3pt + color),
    inset: (
      top: 8pt,
      bottom: 8pt + 2pt,
      left: 3pt + 8pt,
      right: 8pt,
    ),
  )
}

#let makeProof = name => {
  return mathblock(
    blocktitle: name,
    prefix: [_#name._ #h(0.5em)],
    breakable: true,
    // suffix: place(bottom + right, $square$), // https://github.com/jbirnick/typst-great-theorems/issues/8
    suffix: [#h(1fr) $square$],
  )
}

#let theorem = makeThm("Theorem", red)
#let proposition = makeThm("Proposition", orange)
#let lemma = makeThm("Lemma", purple)
#let corollary = makeThm("Corollary", maroon)
#let remark = makeThm("Remark", gray)
#let definition = makeThm("Definition", blue)
#let example = makeThm("Example", green)

#let proof = makeProof("Proof")
#let solution = makeProof("Solution")
#let model = makeProof("Model")
