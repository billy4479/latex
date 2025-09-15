#let template(title: none, author: none, date: "today", doc) = {
  set page(paper: "a4", numbering: "1 of 1", margin: (x: 1.5cm, y: 1.5cm))
  set text(font: "Google Sans", size: 14pt, weight: "regular")
  set par(justify: true)

  let linkColor = aqua.darken(20%).saturate(40%)
  show ref: it => underline(text(linkColor, it))
  show link: it => underline(text(linkColor, it))

  set heading(numbering: "1.")

  // start - https://sitandr.github.io/typst-examples-book/book/snippets/math/numbering.html
  /// original author: laurmaedje

  // reset counter at each chapter
  // if you want to change the number of displayed
  // section numbers, change the level there
  show heading.where(level: 2): it => {
    counter(math.equation).update(0)
    it
  }

  // import "@preview/equate:0.3.2": equate
  // show: equate.with(breakable: true, sub-numbering: true)

  set math.equation(numbering: n => {
    // numbering("(1.1)", counter(heading).get().first(), n)
    // if you want change the number of number of displayed
    // section numbers, modify it this way:
    let count = counter(heading).get()
    let h1 = count.first()
    let h2 = count.at(1, default: 0)
    numbering("(1.1.1)", h1, h2, n)
  })

  // end


  align(center)[
    #text(17pt)[ * #title * ]

    #text(15pt, date)

    #text(author)
  ]

  outline()
  pagebreak()

  doc
}
