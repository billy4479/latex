#import "@preview/lovelace:0.3.1": pseudocode-list

#let alg-color = teal

#let alg-init(body) = {
  show heading.where(level: 1): it => {
    counter("algorithm").update(0)
    it
  }
  body
}

#let algorithm(body, title: none, ..args) = {
  counter("algorithm").step()
  block(
    width: 100%,
    breakable: false,
    fill: alg-color.lighten(90%),
    stroke: (left: 3pt + alg-color),
    inset: (
      top: 8pt,
      bottom: 8pt + 2pt,
      left: 3pt + 8pt,
      right: 8pt,
    ),
  )[
    #context {
      let lvl = counter(heading).get().first()
      let n = counter("algorithm").get().first()
      text(fill: alg-color)[#strong[Algorithm #numbering("1.1", lvl, n)] #h(0.5em) #title]
    }
    #set math.equation(numbering: none)
    #pseudocode-list(
      stroke: 1pt + alg-color.lighten(30%),
      line-number-alignment: top + right,
      ..args,
      body,
    )
  ]
}
