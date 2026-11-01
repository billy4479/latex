#import "@preview/lovelace:0.3.1": pseudocode-list

#let alg-color = teal

#let alg-init(body) = {
  show heading.where(level: 1): it => {
    counter("algorithm").update(0)
    it
  }
  body
}

// Algorithms are wrapped in a `great-theorem-counted` figure with the
// numberfunc metadata expected by `great-theorems-init`, so that a label can
// be attached with `<alg:name>` and referenced with `@alg:name`, exactly like
// theorems.
#let algorithm(body, title: none, ..args) = figure(
  kind: "great-theorem-counted",
  supplement: "Algorithm",
  outlined: false,
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
    #counter("algorithm").step()
    // Number stored for the reference show rule in `great-theorems-init`.
    #metadata(loc => numbering(
      "1.1",
      counter(heading).at(loc).first(),
      counter("algorithm").at(loc).first(),
    ))
    #label("great-theorems:numberfunc")
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
  ],
)
