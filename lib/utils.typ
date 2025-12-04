#let var = math.op($VV"ar"$)
#let cov = math.op($CC"ov"$)
#let prob = math.op($PP"rob"$)

#let argmin = math.op($"arg min"$, limits: true)
#let argmax = math.op($"arg max"$, limits: true)

// https://github.com/johanvx/typst-undergradmath/issues/10#issuecomment-1500662390
#let varnothing = $text(font: "New Computer Modern", nothing)$

// Inspired by https://github.com/Leedehai/typst-physics/blob/38ceed750b74f3577147a3b22fe5e2d61be21245/physica.typ#L206
#let angle = (..body) => {
  $lr(chevron.l #(body.pos().join(math.comma)) chevron.r)$
}

#let bigO = math.op($cal(O)$)
#let littleO = math.op($cal(o)$)
