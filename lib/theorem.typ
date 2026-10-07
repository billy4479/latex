#import "@preview/headcount:0.1.0": *
#import "@preview/great-theorems:0.1.2": *
#import "algorithm.typ": alg-color

#let proof-rule = purple.lighten(40%)

// Accent color of each statement kind, used to color the proof of a statement
// like the statement itself.
#let thm-colors = (
  "Theorem": red,
  "Proposition": orange,
  "Lemma": purple,
  "Corollary": maroon,
  "Remark": gray,
  "Definition": blue,
  "Example": green,
)

// Kind name of a statement, from its (string or content) supplement.
#let kind-of(supplement) = {
  if type(supplement) == str {
    supplement
  } else if supplement.has("text") {
    supplement.text
  } else {
    ""
  }
}

#let makeThm = (name, color, darken: 0%) => {
  return mathblock(
    blocktitle: name,
    prefix: count => text(color.darken(darken))[*#name #count* #h(0.5em)],
    counter: counter("thm"),
    numbering: dependent-numbering("1.1", levels: 1),
    titlix: title => text(color.darken(darken))[ #title ],
    breakable: false,
    fill: color.lighten(90%),
    stroke: (left: 3pt + color),
    inset: (
      top: 8pt,
      bottom: 8pt + 2pt,
      left: 3pt + 8pt,
      right: 8pt,
    ),
    bodyfmt: body => [

      #body
    ],
  )
}

#let thm-init(body) = {
  show: great-theorems-init

  // Strips the recolored proof figure (see below).
  show figure.where(kind: "proof-colored"): set align(start)
  show figure.where(kind: "proof-colored"): set block(breakable: true)
  show figure.where(kind: "proof-colored"): fig => fig.body

  // A proof is colored like the statement it follows: the proof figure is
  // rebuilt with the accent color of the nearest preceding statement.
  show figure.where(kind: "great-theorem-uncounted"): it => {
    if kind-of(it.supplement) == "Proof" {
      let thms = query(
        selector(figure.where(kind: "great-theorem-counted")).before(it.location(), inclusive: false),
      )
      let color = if thms.len() > 0 {
        thm-colors.at(kind-of(thms.last().supplement), default: proof-rule)
      } else {
        proof-rule
      }
      figure(kind: "proof-colored", supplement: it.supplement, outlined: false)[
        #block(
          width: 100%,
          stroke: (left: 2pt + color),
          inset: (top: 4pt, bottom: 4pt, left: 14pt, right: 4pt),
        )[
          #it.body
        ]
      ]
    } else {
      it
    }
  }

  show heading.where(level: 1): it => {
    counter("thm").update(0)
    it
  }

  body
}

#let makeProof = (name, nested: false, color: none) => {
  // A plain top-level `proof` bakes no block style: it is rebuilt by the show
  // rule in `thm-init` with the color of the statement it follows. Everything
  // else (subproofs, solutions, models) styles itself.
  let baked = color != none or nested
  let block-args = if baked {
    let args = (
      inset: (
        top: 4pt,
        bottom: 4pt,
        left: if nested { 30pt } else { 14pt },
        right: 4pt,
      ),
    )
    if color != none {
      args.stroke = (left: 2pt + color)
    }
    args
  } else {
    ()
  }
  return proofblock(
    blocktitle: name,
    prefix: [_#name._ #h(0.5em)],
    prefix_with_of: of => [_Proof of #of._ #h(0.5em)],
    suffix: place(bottom + right, if nested { $square.filled$ } else { $square$ }), // https://github.com/jbirnick/typst-great-theorems/issues/8
    ..block-args,
  )
}

#let theorem = makeThm("Theorem", red)
#let proposition = makeThm("Proposition", orange)
#let lemma = makeThm("Lemma", purple)
#let corollary = makeThm("Corollary", maroon)
#let remark = makeThm("Remark", gray)
#let definition = makeThm("Definition", blue)
#let example = makeThm("Example", green)

// Proof of a statement. The statement label is optional and can be passed
// positionally or as `of:`:
//   #proof[ ... ]                          // proof of the preceding statement
//   #proof(<prop:rayleigh>)[ ... ]         // "Proof of Proposition 3.3.", colored like it
//   #proof(of: <prop:rayleigh>)[ ... ]     // same as above
// The header links back to the statement.
#let proof(..args) = {
  let named = args.named()
  let of = named.at("of", default: none)
  let pos = args.pos()
  if pos.len() > 0 and type(pos.first()) == label {
    of = pos.remove(0)
  }
  if of == none {
    makeProof("Proof")(..named, ..pos)
  } else {
    context {
      let el = query(of).first()
      let color = thm-colors.at(kind-of(el.supplement), default: proof-rule)
      // "Subproof" (not "Proof") so that the recoloring show rule in
      // `thm-init` leaves this already-styled proof alone.
      makeProof("Subproof", color: color)(of: of, ..named, ..pos)
    }
  }
}

#let solution = makeProof("Solution", color: alg-color)
#let model = makeProof("Model", color: alg-color)

// Proof of a sub-result nested inside another proof, e.g.
// #subproof(<lem:power-sum>)[ ... ]
// Same as a proof with a label, but indented and ended by a filled tombstone.
#let subproof(target, body) = context {
  let el = query(target).first()
  let color = thm-colors.at(kind-of(el.supplement), default: proof-rule)
  makeProof("Subproof", nested: true, color: color)(of: target, body)
}
