#let template(title: none, author: none, date: "today", doc) = {
  set page(paper: "a4", numbering: "1 of 1", margin: (x: 1.5cm, y: 1.5cm))
  set text(font: "Ubuntu", size: 12pt)
  set par(justify: true)
  set heading(numbering: "1.")
  set math.equation(numbering: "(1)")

  align(center)[
    #text(17pt)[ * #title * ]

    #text(15pt, date)

    #text(author)
  ]

  outline()
  pagebreak()

  doc
}
