#let template(
  titleString: none,
  author: none,
  date: "today",
  toc: true,
  header: true,
  nameInFooter: true,
  font: "Google Sans",
  fontSize: 14pt,
  doc,
) = {
  set text(font: font, size: fontSize)
  set par(justify: true)

  import "@preview/hydra:0.6.2": hydra
  set page(
    paper: "a4",
    margin: (x: 2em, y: 4em),
    numbering: "1 of 1",
    header: context {
      if (here().page() != 1 and header) {
        emph(upper(hydra(1)))
        h(1fr)
        emph(hydra(2))
        line(length: 100%)
      }
    },
    footer: context {
      set align(center)
      set text(fontSize - 2pt)
      link(
        (page: 1, x: 0pt, y: 0pt),
        counter(page).display(
          "1 of 1",
          both: true,
        ),
      )
      if (nameInFooter) {
        linebreak()
        author
      }
    },
  )

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
  show heading.where(level: 1): it => {
    counter(math.equation).update(0)
    it
  }

  // import "@preview/equate:0.3.2": equate
  // show: equate.with(breakable: true, sub-numbering: true)

  set math.equation(
    numbering: n => {
      // numbering("(1.1)", counter(heading).get().first(), n)
      // if you want change the number of number of displayed
      // section numbers, modify it this way:
      let count = counter(heading).get()
      let h1 = count.first()
      let h2 = count.at(1, default: 0)
      numbering("(1.1.1)", h1, h2, n)
    },
    supplement: "Eq.",
  )

  // end

  show heading.where(level: 1): set text(size: fontSize + 20pt)
  show heading.where(level: 2): set text(size: fontSize + 10pt)
  show heading.where(level: 3): set text(size: fontSize + 5pt)
  show heading.where(level: 4): set text(size: fontSize + 2pt)
  show title: set text(size: fontSize + 30pt)

  align(center)[
    #title[ * #titleString * ]

    #text(fontSize + 5pt, date)

    #text(author)
  ]

  show heading.where(level: 1): it => {
    pagebreak()
    it
  }


  if (toc) {
    outline()
    pagebreak()
  }

  doc
}
