import Mathlib.Data.Rat.Defs
import Mathlib.Data.List.Permutation
import Mathlib.Data.Nat.Factorial.Basic

namespace LiebBridge.Certificate

abbrev Shape := List Nat
abbrev Box := Nat × Nat
abbrev Tableau := List Box

structure Witness where
  k : Nat
  eta : Shape
  mu : Shape
  sign : ℚ
  weight : ℚ
  coefficients : List (Shape × ℚ)
  deriving DecidableEq

def contains (nu eta : Shape) : Bool :=
  decide (eta.length ≤ nu.length) &&
    (eta.zipIdx.all fun p => decide (p.1 ≤ nu.getD p.2 0))

def skewBoxes (eta nu : Shape) : List Box :=
  nu.zipIdx.flatMap fun p =>
    ((List.range p.1).filter fun j => decide (eta.getD p.2 0 ≤ j)).map
      fun j => (p.2, j)

def standard (t : Tableau) : Bool :=
  (t.zipIdx).all fun p =>
    let b := p.1
    let before := t.take p.2
    (if b.2 = 0 then true else
      if t.contains (b.1, b.2 - 1) then before.contains (b.1, b.2 - 1) else true) &&
    (if b.1 = 0 then true else
      if t.contains (b.1 - 1, b.2) then before.contains (b.1 - 1, b.2) else true)

def tableaux (eta nu : Shape) : List Tableau :=
  if contains nu eta then (skewBoxes eta nu).permutations'.filter standard else []

def prefixShape (eta : Shape) (t : Tableau) (k : Nat) : Shape :=
  ((List.range (eta.length + t.length)).map fun i =>
    eta.getD i 0 + ((t.take k).filter fun b => b.1 == i).length).filter (fun n => n != 0)

def content (b : Box) : ℤ := (b.2 : ℤ) - (b.1 : ℤ)

def swapAdjacent (t : Tableau) (i : Nat) : Tableau :=
  t.mapIdx fun j b =>
    if j = i then t.getD (i + 1) (0, 0)
    else if j = i + 1 then t.getD i (0, 0) else b

def seminormalStep (tabs : List Tableau) (i : Nat)
    (state : Tableau × ℚ) : List (Tableau × ℚ) :=
  let t := state.1
  let c := state.2
  let d : ℚ := (content (t.getD (i + 1) (0, 0)) - content (t.getD i (0, 0)) : ℤ)
  let v := swapAdjacent t i
  [(t, c / d)] ++ (if tabs.contains v then [(v, c * (1 + 1 / d))] else [])

def traceWord (eta nu mu : Shape) (k : Nat) (word : List Nat) : ℚ :=
  let tabs := tableaux eta nu
  (tabs.map fun t =>
    if prefixShape eta t k == mu then
      let states := word.reverse.foldl
        (fun ss i => ss.flatMap (seminormalStep tabs i)) [(t, (1 : ℚ))]
      (states.map fun s => if s.1 == t then s.2 else 0).sum
    else 0).sum

def computedCoeff (w : Witness) (nu : Shape) : ℚ :=
  if w.k = 1 then traceWord w.eta nu w.mu 1 [0]
  else if w.k = 2 then
    (traceWord w.eta nu w.mu 2 [1, 0, 2, 1] +
      w.sign * traceWord w.eta nu w.mu 2 [2, 1, 0, 2, 1]) / 2
  else 0

def sparseCoeff (entries : List (Shape × ℚ)) (nu : Shape) : ℚ :=
  (entries.map fun p => if nu = p.1 then p.2 else 0).sum

def storedCoeff (w : Witness) (nu : Shape) : ℚ := sparseCoeff w.coefficients nu

def partitionsAux : Nat → Nat → Nat → List Shape
  | 0, n, _ => if n = 0 then [[]] else []
  | fuel + 1, n, cap =>
    if n = 0 then [[]] else
      ((List.range (min n cap)).reverse).flatMap fun i =>
        (partitionsAux fuel (n - (i + 1)) (i + 1)).map fun p => (i + 1) :: p

def partitions14 : List Shape := partitionsAux 14 14 14

def hookProduct (shape : Shape) : Nat :=
  (shape.zipIdx.flatMap fun p => (List.range p.1).map fun j =>
    p.1 - j + ((shape.drop (p.2 + 1)).filter fun v => decide (j < v)).length).foldl (· * ·) 1

def hookDegree (shape : Shape) : Nat := Nat.factorial shape.sum / hookProduct shape

end LiebBridge.Certificate
