/-!
# Minimal SVG plots, written by Lean itself

Used by the demos to produce the figures of the book.
-/

namespace LeanDL.Plot

/-- A scatter plot of several named point sets on a square `[lo, hi]²` canvas. -/
def scatterSvg (size : Nat) (lo hi : Float) (title : String)
    (series : List (String × String × Array (Float × Float))) : String := Id.run do
  let s := size.toFloat
  let sx (x : Float) : Float := (x - lo) / (hi - lo) * s
  let sy (y : Float) : Float := s - (y - lo) / (hi - lo) * s
  let mut out := s!"<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 {size} {size + 30}\" font-family=\"sans-serif\" font-size=\"12\">\n"
  out := out ++ s!"<rect width=\"{size}\" height=\"{size + 30}\" fill=\"white\"/>\n"
  out := out ++ s!"<line x1=\"0\" y1=\"{sy 0}\" x2=\"{size}\" y2=\"{sy 0}\" stroke=\"#ccc\"/><line x1=\"{sx 0}\" y1=\"0\" x2=\"{sx 0}\" y2=\"{size}\" stroke=\"#ccc\"/>\n"
  for (_, color, pts) in series do
    for (x, y) in pts do
      out := out ++ s!"<circle cx=\"{sx x}\" cy=\"{sy y}\" r=\"2.2\" fill=\"{color}\" fill-opacity=\"0.65\"/>\n"
  out := out ++ s!"<text x=\"6\" y=\"{size + 20}\">{title}</text>\n"
  let mut lx := 0.0
  for (name, color, _) in series do
    out := out ++ s!"<circle cx=\"{s - 150 + lx}\" cy=\"{s + 16}\" r=\"4\" fill=\"{color}\"/><text x=\"{s - 142 + lx}\" y=\"{s + 20}\">{name}</text>\n"
    lx := lx + 75.0
  return out ++ "</svg>\n"

/-- Normalised histograms of several named samples over `[lo, hi]`, drawn as translucent bars. -/
def histSvg (w h : Nat) (lo hi : Float) (bins : Nat) (title : String)
    (series : List (String × String × Array Float)) : String := Id.run do
  let wf := w.toFloat
  let hf := h.toFloat
  let mut counts : List (String × Array Float) := []
  let mut top := 1.0e-9
  for (name, color, vals) in series do
    let mut c := Array.replicate bins 0.0
    for v in vals do
      let i := min (bins - 1) (max 0 (Float.floor ((v - lo) / (hi - lo) * bins.toFloat)).toUInt64.toNat)
      c := c.set! i (c[i]! + 1.0 / vals.size.toFloat)
    top := max top (c.foldl max 0.0)
    counts := counts ++ [(color, c)]
    let _ := name
  let mut out := s!"<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 {w} {h + 40}\" font-family=\"sans-serif\" font-size=\"12\">\n"
  out := out ++ s!"<rect width=\"{w}\" height=\"{h + 40}\" fill=\"white\"/>\n"
  let bw := wf / bins.toFloat
  for (color, c) in counts do
    for i in [0:bins] do
      let bh := c[i]! / top * (hf - 10.0)
      out := out ++ s!"<rect x=\"{i.toFloat * bw + 1.0}\" y=\"{hf - bh}\" width=\"{bw - 2.0}\" height=\"{bh}\" fill=\"{color}\" fill-opacity=\"0.5\"/>\n"
  out := out ++ s!"<line x1=\"0\" y1=\"{hf}\" x2=\"{w}\" y2=\"{hf}\" stroke=\"#555\"/>\n"
  out := out ++ s!"<text x=\"4\" y=\"{h + 20}\">{lo}</text><text x=\"{w - 28}\" y=\"{h + 20}\">{hi}</text>\n"
  out := out ++ s!"<text x=\"{w / 2 - 80}\" y=\"{h + 20}\">{title}</text>\n"
  let mut lx := 0.0
  for (name, color, _) in series do
    out := out ++ s!"<rect x=\"{wf - 150.0 + lx}\" y=\"6\" width=\"10\" height=\"10\" fill=\"{color}\"/><text x=\"{wf - 136.0 + lx}\" y=\"16\">{name}</text>\n"
    lx := lx + 70.0
  return out ++ "</svg>\n"

/-- A number with at most two decimals and no trailing zeros. -/
def fmt (x : Float) : String :=
  let r := Float.round (x * 100.0) / 100.0
  if r == 0.0 then "0"
  else
    let cs := (toString r).toList.reverse.dropWhile (· == '0')
    let cs := if cs.head? == some '.' then cs.tail else cs
    String.mk cs.reverse

/-- A line chart with axes, grid and legend. Points outside the y-range are clipped. -/
def lineSvg (w h : Nat) (xlo xhi ylo yhi : Float) (title xlabel ylabel : String)
    (series : List (String × String × Array (Float × Float))) : String := Id.run do
  let ml := 56.0
  let mt := 26.0
  let pw := w.toFloat - ml - 12.0
  let ph := h.toFloat - mt - 40.0
  let sx (x : Float) : Float := ml + (x - xlo) / (xhi - xlo) * pw
  let sy (y : Float) : Float := mt + ph - (y - ylo) / (yhi - ylo) * ph
  let mut out := s!"<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 {w} {h}\" font-family=\"sans-serif\" font-size=\"12\">\n"
  out := out ++ s!"<rect width=\"{w}\" height=\"{h}\" fill=\"white\"/>\n"
  out := out ++ s!"<clipPath id=\"c\"><rect x=\"{ml}\" y=\"{mt}\" width=\"{pw}\" height=\"{ph}\"/></clipPath>\n"
  for i in [0:5] do
    let fx := xlo + (xhi - xlo) * i.toFloat / 4.0
    let fy := ylo + (yhi - ylo) * i.toFloat / 4.0
    out := out ++ s!"<line x1=\"{sx fx}\" y1=\"{mt}\" x2=\"{sx fx}\" y2=\"{mt + ph}\" stroke=\"#e6e6e6\"/>"
    out := out ++ s!"<line x1=\"{ml}\" y1=\"{sy fy}\" x2=\"{ml + pw}\" y2=\"{sy fy}\" stroke=\"#e6e6e6\"/>"
    out := out ++ s!"<text x=\"{sx fx}\" y=\"{mt + ph + 16.0}\" text-anchor=\"middle\">{fmt fx}</text>"
    out := out ++ s!"<text x=\"{ml - 6.0}\" y=\"{sy fy + 4.0}\" text-anchor=\"end\">{fmt fy}</text>\n"
  out := out ++ s!"<rect x=\"{ml}\" y=\"{mt}\" width=\"{pw}\" height=\"{ph}\" fill=\"none\" stroke=\"#555\"/>\n"
  for (_, color, pts) in series do
    let path := String.intercalate " " (pts.toList.map fun (x, y) => s!"{sx x},{sy y}")
    out := out ++ s!"<polyline clip-path=\"url(#c)\" fill=\"none\" stroke=\"{color}\" stroke-width=\"2\" points=\"{path}\"/>\n"
  let mut row := 0.0
  for (name, color, _) in series do
    out := out ++ s!"<rect x=\"{ml + pw - 150.0}\" y=\"{mt + 8.0 + row}\" width=\"12\" height=\"4\" fill=\"{color}\"/><text x=\"{ml + pw - 132.0}\" y=\"{mt + 14.0 + row}\">{name}</text>\n"
    row := row + 16.0
  out := out ++ s!"<text x=\"{ml}\" y=\"16\" font-weight=\"bold\">{title}</text>\n"
  out := out ++ s!"<text x=\"{ml + pw / 2.0}\" y=\"{h.toFloat - 6.0}\" text-anchor=\"middle\">{xlabel}</text>\n"
  out := out ++ s!"<text transform=\"translate(14,{mt + ph / 2.0}) rotate(-90)\" text-anchor=\"middle\">{ylabel}</text>\n"
  return out ++ "</svg>\n"

/-- A heat map of a matrix with entries in `[0, 1]`; the numbers are written in the cells. -/
def heatSvg (cell : Nat) (title rowLabel colLabel : String) (m : Array (Array Float)) : String := Id.run do
  let rows := m.size
  let cols := (m[0]!).size
  let c := cell.toFloat
  let w := cols.toFloat * c + 60.0
  let h := rows.toFloat * c + 70.0
  let mut out := s!"<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 {w} {h}\" font-family=\"sans-serif\" font-size=\"11\">\n"
  out := out ++ s!"<rect width=\"{w}\" height=\"{h}\" fill=\"white\"/>\n"
  out := out ++ s!"<text x=\"50\" y=\"16\" font-weight=\"bold\">{title}</text>\n"
  for i in [0:rows] do
    out := out ++ s!"<text x=\"44\" y=\"{30.0 + i.toFloat * c + c / 2.0 + 4.0}\" text-anchor=\"end\">{i}</text>\n"
    for j in [0:cols] do
      let v := m[i]![j]!
      out := out ++ s!"<rect x=\"{50.0 + j.toFloat * c}\" y=\"{30.0 + i.toFloat * c}\" width=\"{c}\" height=\"{c}\" fill=\"#2e5aa8\" fill-opacity=\"{v}\" stroke=\"#ccc\"/>"
      if v > 0.0 then
        out := out ++ s!"<text x=\"{50.0 + j.toFloat * c + c / 2.0}\" y=\"{30.0 + i.toFloat * c + c / 2.0 + 4.0}\" text-anchor=\"middle\" fill=\"{if v > 0.5 then "white" else "#222"}\">{fmt v}</text>"
    out := out ++ "\n"
  for j in [0:cols] do
    out := out ++ s!"<text x=\"{50.0 + j.toFloat * c + c / 2.0}\" y=\"{44.0 + rows.toFloat * c}\" text-anchor=\"middle\">{j}</text>"
  out := out ++ s!"\n<text x=\"{50.0 + cols.toFloat * c / 2.0}\" y=\"{h - 6.0}\" text-anchor=\"middle\">{colLabel}</text>\n"
  out := out ++ s!"<text transform=\"translate(10,{30.0 + rows.toFloat * c / 2.0}) rotate(-90)\" text-anchor=\"middle\">{rowLabel}</text>\n"
  return out ++ "</svg>\n"

end LeanDL.Plot
