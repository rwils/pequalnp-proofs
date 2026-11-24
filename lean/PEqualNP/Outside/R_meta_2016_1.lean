import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2016_1
    (hNot :
      ¬∃ (c : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo c ∧
        (∃ (g : PEqualNP.CircuitLowerBounds.Gate), g ∈ c.gates ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
        c.size = (11 : ℕ) ∧
        PEqualNP.MetaComplexity.circuitFun (7 : ℕ) c =
          fun (x : Fin (7 : ℕ) → Bool) =>
            [(1 : ℕ), (12 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (35 : ℕ), (46 : ℕ), (36 : ℕ)].any
              fun (e : ℕ) => x (Fin.ofNat (7 : ℕ) (e / (10 : ℕ))) && x (Fin.ofNat (7 : ℕ) (e % (10 : ℕ))))
    (hMonoGe2Single :
      have f : (Fin (7 : ℕ) → Bool) → Bool := fun (x : Fin (7 : ℕ) → Bool) =>
        [(1 : ℕ), (12 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (35 : ℕ), (46 : ℕ), (36 : ℕ)].any
          fun (e : ℕ) => x (Fin.ofNat (7 : ℕ) (e / (10 : ℕ))) && x (Fin.ofNat (7 : ℕ) (e % (10 : ℕ)));
      ¬∃ (c : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo c ∧
        (∀ (g : PEqualNP.CircuitLowerBounds.Gate), g ∈ c.gates → g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) ∧
        c.size = (11 : ℕ) ∧
        (2 : ℕ) ≤ (c.gates.filter fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
          g.op.eval [Bool.true, Bool.false] && g.inputs.contains (2 : ℕ)).length ∧
        PEqualNP.MetaComplexity.circuitFun (7 : ℕ) c = f ∧
        ∃ (a : ℕ) (b : ℕ) (d : PEqualNP.CircuitLowerBounds.Circuit),
          d.output = c.output + (1 : ℕ) ∧
          List.Forall₂
            (fun (g1 g2 : PEqualNP.CircuitLowerBounds.Gate) =>
              g1.op = g2.op ∧
              List.Forall₂ (fun (i j : ℕ) => j = i + (1 : ℕ) ∨ j = (0 : ℕ) ∧ (i = a ∨ i = b)) g1.inputs g2.inputs)
            c.gates d.gates ∧
          ∀ (x : Fin (7 : ℕ) → Bool), d.eval (Bool.true :: List.ofFn x) = (f x || x (2 : Fin (7 : ℕ))))
    (hMonoLt2Both :
      have f : (Fin (7 : ℕ) → Bool) → Bool := fun (x : Fin (7 : ℕ) → Bool) =>
        [(1 : ℕ), (12 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (35 : ℕ), (46 : ℕ), (36 : ℕ)].any
          fun (e : ℕ) => x (Fin.ofNat (7 : ℕ) (e / (10 : ℕ))) && x (Fin.ofNat (7 : ℕ) (e % (10 : ℕ)));
      ¬∃ (c : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo c ∧
        (∀ (g : PEqualNP.CircuitLowerBounds.Gate), g ∈ c.gates → g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) ∧
        c.size = (11 : ℕ) ∧
        (c.gates.filter fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
          g.op.eval [Bool.true, Bool.false] && g.inputs.contains (2 : ℕ)).length < (2 : ℕ) ∧
        PEqualNP.MetaComplexity.circuitFun (7 : ℕ) c = f ∧
        ∀ (m : Bool), ∃ (a : ℕ) (b : ℕ) (d : PEqualNP.CircuitLowerBounds.Circuit),
          d.output = c.output + (1 : ℕ) ∧
          List.Forall₂
            (fun (g1 g2 : PEqualNP.CircuitLowerBounds.Gate) =>
              g1.op = g2.op ∧
              List.Forall₂ (fun (i j : ℕ) => j = i + (1 : ℕ) ∨ j = (0 : ℕ) ∧ (i = a ∨ i = b)) g1.inputs g2.inputs)
            c.gates d.gates ∧
          ∀ (x : Fin (7 : ℕ) → Bool),
            d.eval (Bool.true :: List.ofFn x) = if m then (f x || x (0 : Fin (7 : ℕ)) || x (3 : Fin (7 : ℕ))) else (f x || x (2 : Fin (7 : ℕ)))) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ¬∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 ∧ x2.size = (11 : ℕ) ∧ (PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x2 = fun (x3 : Fin (7 : ℕ) → Bool) => x1 (Fin.insertNth (0 : Fin (9 : ℕ)) Bool.false (Fin.insertNth (3 : Fin (8 : ℕ)) Bool.false x3))) ∧ ∀ (x3 : Bool), ∃ (x4 : ℕ) (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Circuit), x6.output = x2.output + (1 : ℕ) ∧ List.Forall₂ (fun (x7 x8 : PEqualNP.CircuitLowerBounds.Gate) => x7.op = x8.op ∧ List.Forall₂ (fun (x9 x10 : ℕ) => x10 = x9 + (1 : ℕ) ∨ x10 = (0 : ℕ) ∧ (x9 = x4 ∨ x9 = x5)) x7.inputs x8.inputs) x2.gates x6.gates ∧ ∀ (x7 : Fin (7 : ℕ) → Bool), x6.eval (Bool.true :: List.ofFn x7) = x1 (Fin.insertNth (0 : Fin (9 : ℕ)) x3 (Fin.insertNth (3 : Fin (8 : ℕ)) (!x3) x7)) := by
  let g9 : (Fin 9 → Bool) → Bool := fun x1 =>
    [1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85].any fun x2 =>
      x1 (Fin.ofNat 9 (x2 / 10)) && x1 (Fin.ofNat 9 (x2 % 10))
  let f : (Fin 7 → Bool) → Bool := fun x =>
    [1, 12, 4, 15, 26, 35, 46, 36].any fun e =>
      x (Fin.ofNat 7 (e / 10)) && x (Fin.ofNat 7 (e % 10))
  have eBase : ∀ x : Fin 7 → Bool,
      g9 (Fin.insertNth 0 false (Fin.insertNth 3 false x)) = f x := by decide +kernel
  have eSingle : ∀ x : Fin 7 → Bool,
      g9 (Fin.insertNth 0 false (Fin.insertNth 3 true x)) = (f x || x 2) := by decide +kernel
  have ePair : ∀ x : Fin 7 → Bool,
      g9 (Fin.insertNth 0 true (Fin.insertNth 3 false x)) = (f x || x 0 || x 3) := by decide +kernel
  intro x1
  rintro ⟨c, hfin, hsize, hfun, hrest⟩
  have hfun' : PEqualNP.MetaComplexity.circuitFun 7 c = f := by
    rw [hfun]
    funext x
    exact eBase x
  by_cases hhas : ∃ g ∈ c.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · exact hNot ⟨c, hfin, hhas, hsize, hfun'⟩
  · have hno : ∀ (g : PEqualNP.CircuitLowerBounds.Gate),
        g ∈ c.gates → g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not :=
      fun g hg hnot => hhas ⟨g, hg, hnot⟩
    by_cases hlt :
        (c.gates.filter fun g =>
          g.op.eval [Bool.true, Bool.false] && g.inputs.contains 2).length < 2
    · apply hMonoLt2Both
      refine ⟨c, hfin, hno, hsize, hlt, hfun', fun m => ?_⟩
      cases m
      · obtain ⟨a, b, d, ho, hg, he⟩ := hrest false
        exact ⟨a, b, d, ho, hg, fun x => (he x).trans (eSingle x)⟩
      · obtain ⟨a, b, d, ho, hg, he⟩ := hrest true
        exact ⟨a, b, d, ho, hg, fun x => (he x).trans (ePair x)⟩
    · apply hMonoGe2Single
      obtain ⟨a, b, d, ho, hg, he⟩ := hrest false
      exact ⟨c, hfin, hno, hsize, Nat.le_of_not_lt hlt, hfun', a, b, d, ho, hg,
        fun x => (he x).trans (eSingle x)⟩
