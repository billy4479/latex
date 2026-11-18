#set page(paper: "a4", margin: (x: 15mm, y: 14.5mm))
#set text(font: "FiraCode Nerd Font", size: 9pt, lang: "it")
#set par(leading: 0.15em)

#let bigliettino(numero) = {
  align(center + horizon)[
    #block(breakable: false)[

      #text(font: "Noto Color Emoji", emoji.excl.double)
      Laurea Jack
      #text(font: "Noto Color Emoji", emoji.excl.double)
      2026

      #text(font: "Noto Color Emoji", [ 🥳 🎓 🤓 ✨ ])

      #image("assets/bigliettini/g" + str(numero) + ".png", width: 60%)
    ]
  ]
}

#table(
  columns: (auto,) * 4,
  inset: 1em,
  stroke: (paint: luma(75%), thickness: 0.4pt, dash: "dashed"),
  ..range(70).map(i => bigliettino(calc.rem(i, 3) + 1)),
)
