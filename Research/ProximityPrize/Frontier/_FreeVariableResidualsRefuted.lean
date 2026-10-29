/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Research.ProximityPrize.Frontier._FrobeniusEnergyDescent
import Research.ProximityPrize.Frontier._ArxSteinWraparoundNoGo
import Research.ProximityPrize.Frontier.Sweep_A02_AutocorrelationRecursion

/-!
# Three free-variable residuals are false as stated

Each of the three named residuals below quantifies over a variable that the intended
mathematical object is supposed to pin down, but that the recorded `Prop` leaves free.
As recorded, each is therefore a universally false statement, and every consumer written
`*_of_<Residual>` is vacuous.

* `FrobeniusEnergyDescent.FiberCountResidual` quantifies over all reals `Ep EC W Wick` with
  `Ep = EC + W` and `EC ≤ Wick`, and asserts `W ≤ Wick - EC`. The fiber count `W` is free, so
  `EC = Wick = 0`, `W = 1` refutes it (`not_fiberCountResidual`), and so does every quadruple
  with `Wick - EC < W` (`not_fiberCountResidual_of_lt`).
* `ARX1.SteinWickResidual C` quantifies over every `Nr n r p : ℕ` with `1 ≤ r`, `p ≠ 0`, and
  asserts `dcCount Nr n r p ≤ C * wickBudget n r`. The collision count `Nr` is free, not tied to
  `n`, `r` or `p`. At `n = r = p = 1` the claim reads `Nr - 1 ≤ C` for every `Nr`, so no constant
  `C` works (`not_steinWickResidual`).
* `AutocorrelationRecursion.CrossBandResidual n` asserts `DMTarget n r Er` for every `r` in the
  band `[1, ⌈e·n/2⌉)` and every real `Er ≥ 0`. The energy `Er` is free, so
  `Er = (2r-1)‼·n^r + 1` refutes it at any band rung (`not_crossBandResidual_of_band`); the band
  is nonempty for every `n ≥ 1` (`not_crossBandResidual`).

These are statement-level refutations only. The intended quantities — the reduction-map fiber
count at the saddle depth, the DC-subtracted wraparound count `A_r = N_r - n^{2r}/p` with `N_r`
the actual collision count, and the depth-`r` additive energy of `μ_n` — are not defined by these
`Prop`s and are not touched here. The Wick/BGK wall and the production Delta Star problem remain
open. This file does not close #164.
-/

set_option autoImplicit false

noncomputable section

namespace ProximityGap.Frontier.FreeVariableResidualsRefuted

/-! ## `FiberCountResidual` -/

/-- Any split `Ep = EC + W` with `EC ≤ Wick` and `Wick - EC < W` refutes `FiberCountResidual`. -/
theorem not_fiberCountResidual_of_lt (Ep EC W Wick : ℝ)
    (hsplit : Ep = EC + W) (hcharZero : EC ≤ Wick) (hW : Wick - EC < W) :
    ¬ FrobeniusEnergyDescent.FiberCountResidual := by
  intro h
  have := h Ep EC W Wick hsplit hcharZero
  linarith

/-- `FiberCountResidual` is false: `EC = Wick = 0`, `W = Ep = 1` is a split with `1 ≤ 0 - 0`
demanded. -/
theorem not_fiberCountResidual : ¬ FrobeniusEnergyDescent.FiberCountResidual :=
  not_fiberCountResidual_of_lt 1 0 1 0 (by norm_num) le_rfl (by norm_num)

/-! ## `SteinWickResidual` -/

/-- At `n = r = p = 1`, `dcCount Nr 1 1 1 = Nr - 1` and `wickBudget 1 1 = 1`. -/
theorem dcCount_one_one_one (Nr : ℕ) : ARX1.dcCount Nr 1 1 1 = (Nr : ℝ) - 1 := by
  simp [ARX1.dcCount]

theorem wickBudget_one_one : ARX1.wickBudget 1 1 = 1 := by
  simp [ARX1.wickBudget, Nat.doubleFactorial]

/-- No constant `C` makes `SteinWickResidual C` true: the free collision count `Nr` escapes
every bound. Witness `Nr = ⌈C⌉₊ + 2` at `n = r = p = 1`. -/
theorem not_steinWickResidual (C : ℝ) : ¬ ARX1.SteinWickResidual C := by
  intro h
  have hC := h (⌈C⌉₊ + 2) 1 1 1 le_rfl (by norm_num)
  rw [dcCount_one_one_one, wickBudget_one_one] at hC
  have hceil : C ≤ (⌈C⌉₊ : ℝ) := Nat.le_ceil C
  push_cast at hC
  linarith

/-! ## `CrossBandResidual` -/

open scoped Nat in
/-- At any rung `r` of the band, the free energy `Er = (2r-1)‼·n^r + 1` violates `DMTarget`, so
`CrossBandResidual n` fails. -/
theorem not_crossBandResidual_of_band (n r : ℕ) (hr : 1 ≤ r)
    (hband : r < Nat.ceil ((Real.exp 1 * (n : ℝ)) / 2)) :
    ¬ ArkLib.ProximityGap.AutocorrelationRecursion.CrossBandResidual n := by
  intro h
  have hpos : (0 : ℝ) ≤ ((2 * r - 1)‼ : ℕ) * (n : ℝ) ^ r + 1 := by positivity
  have hE := h r hr hband (((2 * r - 1)‼ : ℕ) * (n : ℝ) ^ r + 1) hpos
  unfold ArkLib.ProximityGap.AutocorrelationRecursion.DMTarget at hE
  linarith

/-- The band `[1, ⌈e·n/2⌉)` contains `r = 1` for every `n ≥ 1`, since `e/2 > 1`. -/
theorem one_lt_ceil_band (n : ℕ) (hn : 1 ≤ n) :
    1 < Nat.ceil ((Real.exp 1 * (n : ℝ)) / 2) := by
  rw [Nat.lt_ceil]
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  push_cast
  nlinarith

/-- `CrossBandResidual n` is false for every `n ≥ 1`. -/
theorem not_crossBandResidual (n : ℕ) (hn : 1 ≤ n) :
    ¬ ArkLib.ProximityGap.AutocorrelationRecursion.CrossBandResidual n :=
  not_crossBandResidual_of_band n 1 le_rfl (one_lt_ceil_band n hn)

end ProximityGap.Frontier.FreeVariableResidualsRefuted

#print axioms ProximityGap.Frontier.FreeVariableResidualsRefuted.not_fiberCountResidual_of_lt
#print axioms ProximityGap.Frontier.FreeVariableResidualsRefuted.not_fiberCountResidual
#print axioms ProximityGap.Frontier.FreeVariableResidualsRefuted.not_steinWickResidual
#print axioms ProximityGap.Frontier.FreeVariableResidualsRefuted.not_crossBandResidual_of_band
#print axioms ProximityGap.Frontier.FreeVariableResidualsRefuted.not_crossBandResidual
