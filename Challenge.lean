/-
Copyright (c) 2026 Arno Onken. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arno Onken
-/
module

public import Mathlib

/-!
# Challenge: the flashlight transformation of a copula

The statement of the main theorem, without proof, together with the definitions it uses. This
file imports only Mathlib, so it is the complete specification: to trust the result, it suffices
to check this file.

The definitions are copies of those in `Flashlight/Defs.lean`, and the proof is in
`Flashlight.lean`, imported by `Solution.lean`. Run `lake comparator` to check that
`Solution.lean` proves exactly this statement with identical definitions, using only the axioms
permitted in `comparator.json`.
-/

open MeasureTheory Finset

@[expose] public section

noncomputable section

namespace Flashlight

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Definitions -/

/-- The unit cube `[0,1]^ι`. -/
def unitCube (ι : Type*) : Set (ι → ℝ) := {u | ∀ i, u i ∈ unitInterval}

/-- `V_C(B) = ∑_{z ∈ ×_{i=1}^d {u_i, v_i}} (-1)^{N_I(z, u, v)} C(z)` for the box
`B = ×_{i=1}^d [u_i, v_i]`, where the corner `z = s.piecewise v u` takes the value `v_k` for
`k ∈ s` and `u_k` otherwise, so that `N_I(z, u, v) = |sᶜ|`. -/
def boxVolume (C : (ι → ℝ) → ℝ) (u v : ι → ℝ) : ℝ :=
  ∑ s : Finset ι, (-1) ^ sᶜ.card * C (s.piecewise v u)

/-- `C` is a `d`-copula (only its values on `[0,1]^ι` matter). -/
structure IsCopula (C : (ι → ℝ) → ℝ) : Prop where
  /-- `C(1, …, 1) = 1`. For `d ≥ 1` this follows from the uniform marginal distributions; it is
  stated explicitly so that the definition is also correct in dimension `0`. -/
  normalized : C 1 = 1
  /-- `C` is grounded. -/
  grounded : ∀ u ∈ unitCube ι, (∃ i, u i = 0) → C u = 0
  /-- `C` has uniform marginal distributions. -/
  marginals : ∀ i, ∀ t ∈ unitInterval, C (Function.update 1 i t) = t
  /-- `C` is `d`-increasing. -/
  increasing : ∀ u ∈ unitCube ι, ∀ v ∈ unitCube ι, u ≤ v → 0 ≤ boxVolume C u v

/-- `κ_{S,A}(i, u)` is `1 - u_i` if `i ∈ A`, `1` if `i ∈ S \ A` and `u_i` if `i ∈ S̄`. -/
def kappa (S A : Finset ι) (u : ι → ℝ) : ι → ℝ :=
  fun i => if i ∈ A then 1 - u i else if i ∈ S then 1 else u i

/-- `C^F_{α,S}(u) := P_U((⋂_{i ∈ S} {U_i > 1 - u_i}) ∩ (⋂_{i ∈ S̄} {U_i ≤ u_i}))`. -/
def flashlightMeasure (μ : Measure (ι → ℝ)) (S : Finset ι) (u : ι → ℝ) : ℝ :=
  μ.real {x | (∀ i ∈ S, 1 - u i < x i) ∧ ∀ i ∉ S, x i ≤ u i}

/-! ### The theorem -/

/-- **Theorem.** Let `C_α` be a `d`-copula, `S ⊆ I` and `P_U` a probability measure with
`P_U(⋂_{i ∈ I} {U_i ≤ u_i}) = C_α(u)` for `u ∈ [0,1]^d`. Then `C^F_{α,S}` is a `d`-copula and
`C^F_{α,S}(u) = ∑_{A ⊆ S} (-1)^|A| C_α(κ_{S,A}(1, u), …, κ_{S,A}(d, u))` for `u ∈ [0,1]^d`. -/
theorem flashlight (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    {C : (ι → ℝ) → ℝ} (hC : IsCopula C)
    (hμ : ∀ u ∈ unitCube ι, C u = μ.real {x | ∀ i, x i ≤ u i}) (S : Finset ι) :
    IsCopula (flashlightMeasure μ S) ∧
      ∀ u ∈ unitCube ι,
        flashlightMeasure μ S u = ∑ A ∈ S.powerset, (-1) ^ #A * C (kappa S A u) := by
  sorry

end Flashlight
