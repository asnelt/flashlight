/-
Copyright (c) 2026 Arno Onken. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arno Onken
-/
import Mathlib

/-!
# The flashlight transformation of a copula

This file formalizes the following theorem and its proof:

**Theorem.** Let `C_α` be a `d`-copula, `I := {1, …, d}`, `S ⊆ I`,
`P_U(⋂_{i ∈ I} {U_i ≤ u_i}) := C_α(u)` a measure, and
`C^F_{α,S}(u) := P_U((⋂_{i ∈ S} {U_i > 1 - u_i}) ∩ (⋂_{i ∈ S̄} {U_i ≤ u_i}))`.
Then `C^F_{α,S}` is a `d`-copula and can be expressed as
`C^F_{α,S}(u) = ∑_{A ⊆ S} (-1)^|A| C_α(κ_{S,A}(1, u), …, κ_{S,A}(d, u))`,
where `S̄ = I \ S` and `κ_{S,A}(i, u)` is `1 - u_i` if `i ∈ A`, `1` if `i ∈ S \ A` and `u_i` if
`i ∈ S̄`.

## Formalization notes

* The index set `I = {1, …, d}` is modelled by an arbitrary finite type `ι`, and `P_U` by a
  probability measure `μ` on `ι → ℝ` whose distribution function agrees with `C_α` on `[0,1]^ι`.
* A corner `z ∈ ×_{i=1}^d {u_i, v_i}` of a box `B = ×_{i=1}^d [u_i, v_i]` is indexed by the set
  `s` of coordinates with `z_k = v_k`, i.e. `z = s.piecewise v u`. Then
  `N_I(z, u, v) = |sᶜ|`, the number of coordinates at the lower bound.
* The sieve formula for measures [Comtet1974] is not available in Mathlib and is proved below.
* The step `P_U((⋂_{i ∈ A} {U_i ≤ 1 - u_i}) ∩ (⋂_{i ∈ S̄} {U_i ≤ u_i})) = C_α(κ_{S,A}(1, u), …)`
  implicitly replaces the events `{U_i ≤ 1}` for `i ∈ S \ A` by the whole space. This is
  justified here explicitly: since `C_α(1, …, 1) = 1`, the event `⋂_{i ∈ I} {U_i ≤ 1}` has
  probability one, so intersecting with it does not change any probability.

## References

* Text S1 (proof of the theorem): <https://doi.org/10.1371/journal.pcbi.1000577.s001>
* The paper: <https://doi.org/10.1371/journal.pcbi.1000577>
* [Comtet1974] L. Comtet, *Advanced Combinatorics*, D. Reidel Publishing Company, 1974.
-/

open MeasureTheory Finset

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace Flashlight

/-! ### The lemma -/

section Lemma

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Lemma.** Let `(Ω, 𝓕, P)` be a probability space with `A ∈ 𝓕`. Then `P^A := P(• ∩ A)` is a
measure on `𝓕`. -/
def restrictMeasure (P : Measure Ω) (A : Set Ω) (hA : MeasurableSet A) : Measure Ω :=
  -- Verification of the measure properties:
  Measure.ofMeasurable (fun E _ => P (E ∩ A))
    -- 1. `P^A(∅) = P(∅ ∩ A) = P(∅) = 0`.
    (by simp)
    -- 2. For `E₁, E₂, … ∈ 𝓕` pairwise disjoint:
    -- `P^A(⋃ E_i) = P((⋃ E_i) ∩ A) = P(⋃ (E_i ∩ A)) = ∑ P(E_i ∩ A) = ∑ P^A(E_i)`.
    (fun E hE hdisj => by
      rw [Set.iUnion_inter]
      exact measure_iUnion
        (fun i j hij => (hdisj hij).mono Set.inter_subset_left Set.inter_subset_left)
        fun i => (hE i).inter hA)

lemma restrictMeasure_apply (P : Measure Ω) {A : Set Ω} (hA : MeasurableSet A) {E : Set Ω}
    (hE : MeasurableSet E) : restrictMeasure P A hA E = P (E ∩ A) :=
  Measure.ofMeasurable_apply E hE

lemma restrictMeasure_real_apply (P : Measure Ω) {A : Set Ω} (hA : MeasurableSet A) {E : Set Ω}
    (hE : MeasurableSet E) : (restrictMeasure P A hA).real E = P.real (E ∩ A) := by
  rw [measureReal_def, restrictMeasure_apply P hA hE, measureReal_def]

instance (P : Measure Ω) [IsFiniteMeasure P] {A : Set Ω} (hA : MeasurableSet A) :
    IsFiniteMeasure (restrictMeasure P A hA) :=
  ⟨by rw [restrictMeasure_apply P hA MeasurableSet.univ]; exact measure_lt_top _ _⟩

end Lemma

/-! ### The sieve formula for finite measures [Comtet1974] -/

section Sieve

variable {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]

/-- Inclusion–exclusion, complement form. -/
lemma measureReal_inter_biInter_compl (ν : Measure Ω) [IsFiniteMeasure ν] (E : ι → Set Ω)
    (hE : ∀ i, MeasurableSet (E i)) (S : Finset ι) {F : Set Ω} (hF : MeasurableSet F) :
    ν.real (F ∩ ⋂ i ∈ S, (E i)ᶜ) = ∑ A ∈ S.powerset, (-1) ^ #A * ν.real (F ∩ ⋂ i ∈ A, E i) := by
  induction S using Finset.induction_on generalizing F with
  | empty => simp
  | insert a S ha ih =>
    have hX : MeasurableSet (⋂ i ∈ S, (E i)ᶜ) :=
      Finset.measurableSet_biInter _ fun i _ => (hE i).compl
    have hset : F ∩ ⋂ i ∈ insert a S, (E i)ᶜ =
        (F ∩ ⋂ i ∈ S, (E i)ᶜ) \ ((F ∩ E a) ∩ ⋂ i ∈ S, (E i)ᶜ) := by
      rw [Finset.set_biInter_insert]
      ext x
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff]
      tauto
    have hsub : (F ∩ E a) ∩ ⋂ i ∈ S, (E i)ᶜ ⊆ F ∩ ⋂ i ∈ S, (E i)ᶜ :=
      fun x hx => ⟨hx.1.1, hx.2⟩
    rw [hset, measureReal_sdiff hsub ((hF.inter (hE a)).inter hX),
      ih hF, ih (hF.inter (hE a)), sum_powerset_insert ha, sub_eq_add_neg, ← sum_neg_distrib]
    congr 1
    refine sum_congr rfl fun A hA => ?_
    have haA : a ∉ A := fun h => ha (mem_powerset.1 hA h)
    rw [card_insert_of_notMem haA, Finset.set_biInter_insert, pow_succ, Set.inter_assoc]
    ring

lemma sum_range_succ_neg_one_pow (g : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1) ^ k * g k = g 0 - ∑ k ∈ Icc 1 n, (-1) ^ (k - 1) * g k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, sum_Icc_succ_top (by omega), Nat.add_sub_cancel, pow_succ]
    ring

/-- **Sieve formula** (inclusion–exclusion principle) for finite measures:
`ν(⋃_{i ∈ S} E_i) = ∑_{k=1}^{|S|} (-1)^{k-1} ∑_{A ⊆ S, |A| = k} ν(⋂_{i ∈ A} E_i)`. -/
lemma measureReal_biUnion_sieve (ν : Measure Ω) [IsFiniteMeasure ν] (E : ι → Set Ω)
    (hE : ∀ i, MeasurableSet (E i)) (S : Finset ι) :
    ν.real (⋃ i ∈ S, E i) =
      ∑ k ∈ Icc 1 #S, (-1) ^ (k - 1) * ∑ A ∈ powersetCard k S, ν.real (⋂ i ∈ A, E i) := by
  have hU : MeasurableSet (⋃ i ∈ S, E i) := Finset.measurableSet_biUnion _ fun i _ => hE i
  have h := measureReal_inter_biInter_compl ν E hE S MeasurableSet.univ
  rw [← Set.compl_iUnion₂, Set.univ_inter, measureReal_compl hU, sum_powerset] at h
  simp only [Set.univ_inter] at h
  have h' : ∑ k ∈ range (#S + 1), ∑ A ∈ powersetCard k S, (-1) ^ #A * ν.real (⋂ i ∈ A, E i) =
      ∑ k ∈ range (#S + 1), (-1) ^ k * ∑ A ∈ powersetCard k S, ν.real (⋂ i ∈ A, E i) := by
    refine sum_congr rfl fun k _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun A hA => by rw [(mem_powersetCard.1 hA).2]
  rw [h', sum_range_succ_neg_one_pow] at h
  simp only [powersetCard_zero, sum_singleton] at h
  rw [show (⋂ i ∈ (∅ : Finset ι), E i) = Set.univ by simp] at h
  linarith

end Sieve

/-! ### Copulas -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The unit cube `[0,1]^ι`. -/
def unitCube (ι : Type*) : Set (ι → ℝ) := {u | ∀ i, u i ∈ Set.Icc (0 : ℝ) 1}

/-- `V_C(B) = ∑_{z ∈ ×_{i=1}^d {u_i, v_i}} (-1)^{N_I(z, u, v)} C(z)` for the box
`B = ×_{i=1}^d [u_i, v_i]`, where the corner `z = s.piecewise v u` takes the value `v_k` for
`k ∈ s` and `u_k` otherwise, so that `N_I(z, u, v) = |sᶜ|`. -/
def boxVolume (C : (ι → ℝ) → ℝ) (u v : ι → ℝ) : ℝ :=
  ∑ s : Finset ι, (-1) ^ sᶜ.card * C (s.piecewise v u)

/-- `C` is a `d`-copula (only its values on `[0,1]^ι` matter). -/
structure IsCopula (C : (ι → ℝ) → ℝ) : Prop where
  /-- `C` is grounded. -/
  grounded : ∀ u ∈ unitCube ι, (∃ i, u i = 0) → C u = 0
  /-- `C` has uniform margins. -/
  margins : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) 1, C (Function.update 1 i t) = t
  /-- `C` is `d`-increasing. -/
  increasing : ∀ u ∈ unitCube ι, ∀ v ∈ unitCube ι, u ≤ v → 0 ≤ boxVolume C u v

/-! ### The objects of the theorem -/

/-- `κ_{S,A}(i, u)` is `1 - u_i` if `i ∈ A`, `1` if `i ∈ S \ A` and `u_i` if `i ∈ S̄`. -/
def kappa (S A : Finset ι) (u : ι → ℝ) : ι → ℝ :=
  fun i => if i ∈ A then 1 - u i else if i ∈ S then 1 else u i

/-- The right-hand side of the flashlight formula,
`∑_{A ⊆ S} (-1)^|A| C_α(κ_{S,A}(1, u), …, κ_{S,A}(d, u))`. -/
def flashlightSum (C : (ι → ℝ) → ℝ) (S : Finset ι) (u : ι → ℝ) : ℝ :=
  ∑ A ∈ S.powerset, (-1) ^ #A * C (kappa S A u)

/-- `C^F_{α,S}(u) := P_U((⋂_{i ∈ S} {U_i > 1 - u_i}) ∩ (⋂_{i ∈ S̄} {U_i ≤ u_i}))`. -/
def flashlightMeasure (μ : Measure (ι → ℝ)) (S : Finset ι) (u : ι → ℝ) : ℝ :=
  μ.real {x | (∀ i ∈ S, 1 - u i < x i) ∧ ∀ i ∉ S, x i ≤ u i}

/-! ### Elementary lemmas -/

lemma one_mem_Icc : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩

lemma one_sub_mem_Icc {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : 1 - t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨by linarith [ht.2], by linarith [ht.1]⟩

lemma one_mem_unitCube : (1 : ι → ℝ) ∈ unitCube ι := fun _ => one_mem_Icc

lemma update_mem_unitCube {u : ι → ℝ} (hu : u ∈ unitCube ι) (a : ι) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : Function.update u a t ∈ unitCube ι := by
  intro i
  rcases eq_or_ne i a with rfl | hi
  · simpa using ht
  · simpa [hi] using hu i

lemma piecewise_mem_unitCube {u v : ι → ℝ} (hu : u ∈ unitCube ι) (hv : v ∈ unitCube ι)
    (s : Finset ι) : s.piecewise v u ∈ unitCube ι := by
  intro i
  by_cases hi : i ∈ s
  · simpa [hi] using hv i
  · simpa [hi] using hu i

lemma kappa_mem_unitCube (S A : Finset ι) {u : ι → ℝ} (hu : u ∈ unitCube ι) :
    kappa S A u ∈ unitCube ι := by
  intro i
  simp only [kappa]
  split_ifs
  exacts [one_sub_mem_Icc (hu i), one_mem_Icc, hu i]

/-- Being a copula only depends on the values on the unit cube. -/
lemma IsCopula.congr {C D : (ι → ℝ) → ℝ} (hC : IsCopula C)
    (h : ∀ u ∈ unitCube ι, C u = D u) : IsCopula D where
  grounded u hu h0 := h u hu ▸ hC.grounded u hu h0
  margins i t ht := h _ (update_mem_unitCube one_mem_unitCube i ht) ▸ hC.margins i t ht
  increasing u hu v hv huv := by
    have : boxVolume D u v = boxVolume C u v :=
      sum_congr rfl fun s _ => by rw [h _ (piecewise_mem_unitCube hu hv s)]
    exact this ▸ hC.increasing u hu v hv huv

lemma IsCopula.apply_one {C : (ι → ℝ) → ℝ} (hC : IsCopula C) [Nonempty ι] : C 1 = 1 := by
  obtain ⟨a⟩ := ‹Nonempty ι›
  simpa using hC.margins a 1 one_mem_Icc

/-! ### The flashlight formula -/

/-- The event `⋂_{i ∈ I} {U_i ≤ 1}` has probability one, because `P_U(⋂_{i ∈ I} {U_i ≤ 1}) =
C_α(1, …, 1) = 1`. This justifies replacing the events `{U_i ≤ 1}` by the whole space. -/
lemma measure_compl_le_one_eq_zero (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    {C : (ι → ℝ) → ℝ} (hC : IsCopula C)
    (hμ : ∀ u ∈ unitCube ι, C u = μ.real {x | ∀ i, x i ≤ u i}) :
    μ {x : ι → ℝ | ∀ i, x i ≤ 1}ᶜ = 0 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  have hmeas : MeasurableSet {x : ι → ℝ | ∀ i, x i ≤ 1} := by measurability
  have h1 : μ.real {x : ι → ℝ | ∀ i, x i ≤ 1} = 1 := by
    have h := hμ 1 one_mem_unitCube
    simp only [Pi.one_apply] at h
    rw [← h, hC.apply_one]
  rw [← measureReal_eq_zero_iff, measureReal_compl hmeas, h1, probReal_univ, sub_self]

/-- `P_U((⋂_{i ∈ A} {U_i ≤ 1 - u_i}) ∩ (⋂_{i ∈ S̄} {U_i ≤ u_i})) =
C_α(κ_{S,A}(1, u), …, κ_{S,A}(d, u))`. The event on the left-hand side does not contain the
conditions `U_i ≤ κ_{S,A}(i, u) = 1` for `i ∈ S \ A`, but these hold almost surely by
`measure_compl_le_one_eq_zero`. -/
lemma measureReal_eq_kappa (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    {C : (ι → ℝ) → ℝ} (hC : IsCopula C)
    (hμ : ∀ u ∈ unitCube ι, C u = μ.real {x | ∀ i, x i ≤ u i})
    {S A : Finset ι} (hAS : A ⊆ S) {u : ι → ℝ} (hu : u ∈ unitCube ι) :
    μ.real ((⋂ i ∈ A, {x : ι → ℝ | x i ≤ 1 - u i}) ∩ {x | ∀ i ∉ S, x i ≤ u i}) =
      C (kappa S A u) := by
  have hG := measure_compl_le_one_eq_zero μ hC hμ
  -- intersecting with the almost sure event `⋂_{i ∈ I} {U_i ≤ 1}`, both events agree
  have hset : ((⋂ i ∈ A, {x : ι → ℝ | x i ≤ 1 - u i}) ∩ {x | ∀ i ∉ S, x i ≤ u i}) ∩
      {x | ∀ i, x i ≤ 1} = {x | ∀ i, x i ≤ kappa S A u i} ∩ {x | ∀ i, x i ≤ 1} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, kappa]
    constructor
    · rintro ⟨⟨hA, hS⟩, h1⟩
      refine ⟨fun i => ?_, h1⟩
      split_ifs with hiA hiS
      exacts [hA i hiA, h1 i, hS i hiS]
    · rintro ⟨hk, h1⟩
      refine ⟨⟨fun i hiA => by simpa [hiA] using hk i, fun i hiS => ?_⟩, h1⟩
      have hiA : i ∉ A := fun h => hiS (hAS h)
      simpa [hiA, hiS] using hk i
  rw [hμ _ (kappa_mem_unitCube S A hu), measureReal_def, measureReal_def,
    ← measure_inter_conull hG, hset, measure_inter_conull hG]

/-- The flashlight formula `C^F_{α,S}(u) = ∑_{A ⊆ S} (-1)^|A| C_α(κ_{S,A}(1, u), …)`. -/
theorem flashlightMeasure_eq_flashlightSum (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    {C : (ι → ℝ) → ℝ} (hC : IsCopula C)
    (hμ : ∀ u ∈ unitCube ι, C u = μ.real {x | ∀ i, x i ≤ u i}) (S : Finset ι)
    {u : ι → ℝ} (hu : u ∈ unitCube ι) :
    flashlightMeasure μ S u = flashlightSum C S u := by
  -- We start with Eqn (eq:Flashlight). By definition `P_U` is a probability mass function.
  -- Let `B := ⋂_{i ∈ S̄} {U_i ≤ u_i}`.
  set B : Set (ι → ℝ) := {x | ∀ i ∉ S, x i ≤ u i} with hB_def
  have hB : MeasurableSet B := by measurability
  set E : ι → Set (ι → ℝ) := fun i => {x | x i ≤ 1 - u i} with hE_def
  have hE : ∀ i, MeasurableSet (E i) := fun i => by measurability
  -- By the lemma, `P_U^B` is a measure.
  set PB := restrictMeasure μ B hB
  have hT : MeasurableSet (⋂ i ∈ S, {x : ι → ℝ | 1 - u i < x i}) :=
    Finset.measurableSet_biInter _ fun i _ => by measurability
  have hPBB : PB.real Set.univ = PB.real B := by
    rw [restrictMeasure_real_apply μ hB MeasurableSet.univ, restrictMeasure_real_apply μ hB hB,
      Set.univ_inter, Set.inter_self]
  -- We can apply the generalized inclusion exclusion principle for arbitrary measures:
  calc flashlightMeasure μ S u
      -- `= P_U^B(⋂_{i ∈ S} {U_i > 1 - u_i})`
      _ = PB.real (⋂ i ∈ S, {x | 1 - u i < x i}) := by
        rw [restrictMeasure_real_apply μ hB hT, flashlightMeasure]
        congr 1
        ext x
        simp [B]
      -- `= P_U^B(B) - P_U^B(complement of ⋂_{i ∈ S} {U_i > 1 - u_i})`
      _ = PB.real B - PB.real (⋂ i ∈ S, {x | 1 - u i < x i})ᶜ := by
        rw [measureReal_compl hT, hPBB]
        ring
      -- `= P_U^B(B) - P_U^B(⋃_{i ∈ S} {U_i ≤ 1 - u_i})`
      _ = PB.real B - PB.real (⋃ i ∈ S, E i) := by
        rw [Set.compl_iInter₂]
        congr 3
        ext x
        simp [E]
      -- `= P_U^B(B) - ∑_{k=1}^{|S|} (-1)^{k-1} ∑_{A ⊆ S, |A| = k} P_U^B(⋂_{i ∈ A} {U_i ≤ 1 - u_i})`
      -- (Lemma and Sieve)
      _ = PB.real B - ∑ k ∈ Icc 1 #S,
            (-1) ^ (k - 1) * ∑ A ∈ powersetCard k S, PB.real (⋂ i ∈ A, E i) := by
        rw [measureReal_biUnion_sieve PB E hE S]
      -- `= ∑_{k=0}^{|S|} (-1)^k ∑_{A ⊆ S, |A| = k} P_U^B(⋂_{i ∈ A} {U_i ≤ 1 - u_i})`
      _ = ∑ k ∈ range (#S + 1),
            (-1) ^ k * ∑ A ∈ powersetCard k S, PB.real (⋂ i ∈ A, E i) := by
        rw [sum_range_succ_neg_one_pow]
        simp [hPBB]
      -- `= ∑_{A ⊆ S} (-1)^|A| P_U^B(⋂_{i ∈ A} {U_i ≤ 1 - u_i})`
      _ = ∑ A ∈ S.powerset, (-1) ^ #A * PB.real (⋂ i ∈ A, E i) := by
        rw [sum_powerset]
        refine sum_congr rfl fun k _ => ?_
        rw [mul_sum]
        exact sum_congr rfl fun A hA => by rw [(mem_powersetCard.1 hA).2]
      -- `= ∑_{A ⊆ S} (-1)^|A| P_U((⋂_{i ∈ A} {U_i ≤ 1 - u_i}) ∩ (⋂_{i ∈ S̄} {U_i ≤ u_i}))`
      _ = ∑ A ∈ S.powerset, (-1) ^ #A * μ.real ((⋂ i ∈ A, E i) ∩ B) := by
        refine sum_congr rfl fun A _ => ?_
        rw [restrictMeasure_real_apply μ hB (Finset.measurableSet_biInter _ fun i _ => hE i)]
      -- `= ∑_{A ⊆ S} (-1)^|A| C_α(κ_{S,A}(1, u), …, κ_{S,A}(d, u))`
      -- (the events `{U_i ≤ 1}`, `i ∈ S \ A`, are almost sure, see `measureReal_eq_kappa`)
      _ = flashlightSum C S u :=
        sum_congr rfl fun A hA => by
          rw [measureReal_eq_kappa μ hC hμ (mem_powerset.1 hA) hu]

/-! ### `C^F_{α,S}` is a copula -/

section Increasing

/-- `χ_A(i)` is `1` if `i ∈ A` and `0` if `i ∉ A`. -/
def chi (A : Finset ι) (i : ι) : ℝ := if i ∈ A then 1 else 0

/-- `ψ_S(z_k) := χ_S(k)(1 - z_k) + χ_{S̄}(k)(z_k)`. -/
def psi (S : Finset ι) (z : ι → ℝ) : ι → ℝ := fun k => chi S k * (1 - z k) + chi Sᶜ k * z k

lemma kappa_self_eq_psi (S : Finset ι) (z : ι → ℝ) : kappa S S z = psi S z := by
  funext k
  by_cases hk : k ∈ S <;> simp [kappa, psi, chi, hk]

lemma psi_mem_unitCube (S : Finset ι) {z : ι → ℝ} (hz : z ∈ unitCube ι) :
    psi S z ∈ unitCube ι := by
  intro k
  by_cases hk : k ∈ S
  · simpa [psi, chi, hk] using one_sub_mem_Icc (hz k)
  · simpa [psi, chi, hk] using hz k

/-- A corner `z` with `z_{s_A} = v_{s_A}` and the corner with `z_{s_A} = u_{s_A}` have opposite
signs: `(-1)^{N_I(z, u, v) - 1}` and `(-1)^{N_I(z, u, v)}`. -/
lemma neg_one_pow_card_compl_insert {a : ι} {t : Finset ι} (ha : a ∉ t) :
    ((-1 : ℝ)) ^ (insert a t)ᶜ.card = -(-1) ^ tᶜ.card := by
  rw [compl_insert, card_erase_of_mem (by simpa using ha)]
  obtain ⟨n, hn⟩ : ∃ n, tᶜ.card = n + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (card_pos.2 ⟨a, by simpa using ha⟩)).symm⟩
  rw [hn, pow_succ, Nat.add_sub_cancel]
  ring

/-- `(7)`: `(-1)^{N_I(ψ_S(z), ψ_S(u), ψ_S(v))} = (-1)^{N_I(z, u, v)} (-1)^{|S|}`. -/
lemma neg_one_pow_card_compl_symmDiff (s S : Finset ι) :
    ((-1 : ℝ)) ^ (symmDiff s S)ᶜ.card = (-1) ^ sᶜ.card * (-1) ^ #S := by
  -- Let `k := |{z(i) = u(i) | i ∈ I \ S}|` and `l := |{z(i) = v(i) | i ∈ S}|`.
  set k := #(sᶜ \ S)
  set l := #(s ∩ S)
  -- Then `N_I(z, u, v) = k + |S| - l`
  have hN : #sᶜ = k + (#S - l) := by
    have h1 := card_sdiff_add_card_inter sᶜ S
    have h2 := card_sdiff_add_card_inter S s
    have h3 : sᶜ ∩ S = S \ s := by ext; simp [and_comm]
    rw [h3] at h1
    rw [inter_comm] at h2
    omega
  -- and `N_I(ψ_S(z), ψ_S(u), ψ_S(v)) = k + l`.
  have hNψ : #(symmDiff s S)ᶜ = k + l := by
    rw [← card_union_of_disjoint]
    · congr 1
      ext i
      simp only [mem_compl, Finset.mem_symmDiff, mem_union, Finset.mem_sdiff, Finset.mem_inter]
      tauto
    · exact disjoint_left.2 fun i h1 h2 => (mem_compl.1 (mem_sdiff.1 h1).1) (mem_inter.1 h2).1
  -- `(-1)^{N_I(z, u, v)} (-1)^{|S|} = (-1)^{k + 2|S| - l} = (-1)^{k - l} = (-1)^{k + l}`, where
  -- we used that `(-1)^{2|S|} = 1` and `(-1)^{-l} = (-1)^l`.
  have hl : l ≤ #S := card_le_card inter_subset_right
  obtain ⟨m, hm⟩ : ∃ m, #S = l + m := ⟨#S - l, by omega⟩
  have hsq : ((-1 : ℝ) ^ m) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [hNψ, hN, hm, Nat.add_sub_cancel_left]
  calc ((-1 : ℝ)) ^ (k + l) = (-1) ^ (k + l) * ((-1) ^ m) ^ 2 := by rw [hsq, mul_one]
    _ = (-1) ^ (k + m) * (-1) ^ (l + m) := by ring

end Increasing

/-- **Theorem.** `C^F_{α,S}` (here in the form of the right-hand side of the flashlight formula)
is a `d`-copula. -/
theorem isCopula_flashlightSum {C : (ι → ℝ) → ℝ} (hC : IsCopula C) (S : Finset ι) :
    IsCopula (flashlightSum C S) where
  -- 1. Let `u ∈ [0,1]^d` with `∃ a ∈ I : u_a = 0`. We distinguish two cases:
  grounded u hu := by
    rintro ⟨a, ha0⟩
    by_cases ha : a ∉ S
    · -- For `a ∈ S̄`:
      -- `C^F_{α,S}(u) = ∑_{A ⊆ S} (-1)^|A| C_α(κ_{S,A}(1, u), …, 0, …, κ_{S,A}(d, u))`
      -- `= ∑_{A ⊆ S} (-1)^|A| 0 = 0`.
      refine sum_eq_zero fun A hA => ?_
      have haA : a ∉ A := fun h => ha (mem_powerset.1 hA h)
      rw [hC.grounded _ (kappa_mem_unitCube S A hu) ⟨a, by simp [kappa, haA, ha, ha0]⟩, mul_zero]
    · -- For `a ∈ S`:
      rw [not_not] at ha
      -- `C^F_{α,S}(u) = ∑_{A ⊆ S \ {a}} (-1)^{|A ∪ {a}|} C_α(κ_{S,A ∪ {a}}(1, u), …, 1, …)`
      -- `+ ∑_{A ⊆ S \ {a}} (-1)^{|A|} C_α(κ_{S,A}(1, u), …, 1, …)`
      have hS : S.powerset = (insert a (S.erase a)).powerset := by rw [insert_erase ha]
      rw [flashlightSum, hS, sum_powerset_insert (notMem_erase a S), add_comm,
        ← sum_add_distrib]
      -- `= ∑_{A ⊆ S \ {a}} (-1)^{|A| + 1} C_α(κ_{S,A}(1, u), …, 1, …)`
      -- `+ ∑_{A ⊆ S \ {a}} (-1)^{|A|} C_α(κ_{S,A}(1, u), …, 1, …) = 0`.
      refine sum_eq_zero fun A hA => ?_
      have haA : a ∉ A := fun h => notMem_erase a S (mem_powerset.1 hA h)
      have hk : kappa S (insert a A) u = kappa S A u := by
        funext i
        rcases eq_or_ne i a with rfl | hi
        · simp [kappa, haA, ha, ha0]
        · simp [kappa, hi]
      rw [hk, card_insert_of_notMem haA, pow_succ]
      ring
  -- 2. Let `u ∈ [0,1]^d` with `u_i = 1` if `i ≠ a`. We distinguish the same cases:
  margins a t ht := by
    by_cases ha : a ∉ S
    · -- For `a ∈ S̄`:
      -- `C^F_{α,S}(u) = (-1)^{|∅|} C_α(κ_{S,∅}(1, u), …, κ_{S,∅}(d, u))`
      -- `+ ∑_{A ⊆ S, A ≠ ∅} (-1)^|A| C_α(κ_{S,A}(1, u), …, κ_{S,A}(d, u))`
      rw [flashlightSum, sum_eq_single_of_mem ∅ (empty_mem_powerset S)]
      · -- `(2)`: `κ_{S,∅}(a, u) = u_a`; `∀ i ∈ S : κ_{S,∅}(i, u) = 1`;
        -- `∀ i ∈ S̄ \ {a} : κ_{S,∅}(i, u) = 1`. Hence the sum is
        -- `C_α(1, …, 1, u_a, 1, …, 1) = u_a`.
        have hk : kappa S ∅ (Function.update 1 a t) = Function.update (1 : ι → ℝ) a t := by
          funext i
          rcases eq_or_ne i a with rfl | hi
          · simp [kappa, ha]
          · by_cases hiS : i ∈ S <;> simp [kappa, hi, hiS]
        rw [hk, hC.margins a t ht, card_empty, pow_zero, one_mul]
      · -- `(1)`: `∀ A ⊆ S, A ≠ ∅ : a ∈ S̄ ⇒ a ∉ A ⇒ ∃ i ∈ A : i ≠ a`, thus
        -- `κ_{S,A}(i, u) = 1 - u_i = 0` (as `i ≠ a`), and the summand is `(-1)^|A| 0 = 0`.
        intro A hA hA0
        obtain ⟨i, hi⟩ := nonempty_iff_ne_empty.2 hA0
        have hia : i ≠ a := fun h => ha (h ▸ mem_powerset.1 hA hi)
        rw [hC.grounded _ (kappa_mem_unitCube S A (update_mem_unitCube one_mem_unitCube a ht))
          ⟨i, by simp [kappa, hi, hia]⟩, mul_zero]
    · -- For `a ∈ S`:
      rw [not_not] at ha
      -- `C^F_{α,S}(u) = (-1)^{|∅|} C_α(κ_{S,∅}(1, u), …) + (-1)^{|{a}|} C_α(κ_{S,{a}}(1, u), …)`
      -- `+ ∑_{A ⊆ S, A ≠ ∅, A ≠ {a}} (-1)^|A| C_α(κ_{S,A}(1, u), …)`
      rw [flashlightSum, sum_eq_add_of_mem ∅ {a} (empty_mem_powerset S)
        (mem_powerset.2 (singleton_subset_iff.2 ha)) (singleton_ne_empty a).symm]
      · -- `(4)`: `κ_{S,∅}(a, u) = 1`; `∀ i ∈ S \ {a} : κ_{S,∅}(i, u) = 1`;
        -- `∀ i ∈ S̄ : κ_{S,∅}(i, u) = 1`.
        have hk0 : kappa S ∅ (Function.update 1 a t) = 1 := by
          funext i
          rcases eq_or_ne i a with rfl | hi
          · simp [kappa, ha]
          · by_cases hiS : i ∈ S <;> simp [kappa, hi, hiS]
        -- `(5)`: `κ_{S,{a}}(a, u) = 1 - u_a`; `∀ i ∈ S \ {a} : κ_{S,{a}}(i, u) = 1`;
        -- `∀ i ∈ S̄ : κ_{S,{a}}(i, u) = u_i = 1`.
        have hka : kappa S {a} (Function.update 1 a t) =
            Function.update (1 : ι → ℝ) a (1 - t) := by
          funext i
          rcases eq_or_ne i a with rfl | hi
          · simp [kappa]
          · by_cases hiS : i ∈ S <;> simp [kappa, hi, hiS]
        -- `= C_α(1, …, 1) - C_α(1, …, 1, 1 - u_a, 1, …, 1) = 1 - (1 - u_a) = u_a`.
        have h1 : C 1 = 1 := by simpa using hC.margins a 1 one_mem_Icc
        rw [hk0, hka, h1, hC.margins a (1 - t) (one_sub_mem_Icc ht), card_empty,
          card_singleton]
        ring
      · -- `(3)`: `∀ A ⊆ S, A ≠ ∅, A ≠ {a} : ∃ i ∈ A : i ≠ a`, remainder as in `(1)`.
        rintro A hA ⟨hA0, hAa⟩
        obtain ⟨i, hi, hia⟩ : ∃ i ∈ A, i ≠ a := by
          by_contra! h
          obtain ⟨j, hj⟩ := nonempty_iff_ne_empty.2 hA0
          exact hAa (eq_singleton_iff_unique_mem.2 ⟨h j hj ▸ hj, h⟩)
        rw [hC.grounded _ (kappa_mem_unitCube S A (update_mem_unitCube one_mem_unitCube a ht))
          ⟨i, by simp [kappa, hi, hia]⟩, mul_zero]
  -- 3. We show that `C^F_{α,S}` is `d`-increasing, i.e. `V_{C^F_{α,S}}(B) ≥ 0` for all boxes
  -- `B = ×_{i=1}^d [u_i, v_i]`.
  increasing u hu v hv huv := by
    -- `ψ_S(B)`: the box with corners `ψ_S(u_i)` and `ψ_S(v_i)`, ordered per coordinate.
    set u' : ι → ℝ := fun i => min (psi S u i) (psi S v i)
    set v' : ι → ℝ := fun i => max (psi S u i) (psi S v i)
    -- the corners of `B` are mapped by `ψ_S` to the corners of `ψ_S(B)`
    have hcorner : ∀ s : Finset ι, psi S (s.piecewise v u) = (symmDiff s S).piecewise v' u' := by
      intro s
      funext i
      have := huv i
      by_cases hiS : i ∈ S <;> by_cases his : i ∈ s <;>
        simp [psi, chi, u', v', hiS, his, Finset.mem_symmDiff] <;> linarith
    have hV : boxVolume (flashlightSum C S) u v = boxVolume C u' v' := by
      unfold boxVolume flashlightSum
      -- `V_{C^F_{α,S}}(B) = ∑_z (-1)^{N_I(z, u, v)} ∑_{A ⊆ S} (-1)^|A| C_α(κ_{S,A}(1, z), …)`
      -- `= ∑_{A ⊆ S} (-1)^|A| ∑_z (-1)^{N_I(z, u, v)} C_α(κ_{S,A}(1, z), …)`
      simp_rw [mul_sum]
      rw [sum_comm]
      -- `= (-1)^{|S|} ∑_z (-1)^{N_I(z, u, v)} C_α(κ_{S,S}(1, z), …)`
      -- `+ ∑_{A ⊆ S, A ≠ S} (-1)^|A| ∑_z (-1)^{N_I(z, u, v)} C_α(κ_{S,A}(1, z), …)`
      rw [← add_sum_erase _ _ (mem_powerset_self S)]
      -- `(6)`: the second sum vanishes. (For `S = ∅` it is empty, and `C^F_{α,S} = C_α`.)
      -- For `A ⊆ S, A ≠ S` there is an `s_A ∈ S \ A` with `κ_{S,A}(s_A, z) = 1`. Hence the
      -- sum over the corners `z` with `z_{s_A} = u_{s_A}` and the sum over the corners with
      -- `z_{s_A} = v_{s_A}` cancel, since corresponding summands have the signs
      -- `(-1)^{N_I(z, u, v)}` and `(-1)^{N_I(z, u, v) - 1}`.
      have h6 : ∑ A ∈ S.powerset.erase S, ∑ s : Finset ι,
          (-1) ^ sᶜ.card * ((-1) ^ #A * C (kappa S A (s.piecewise v u))) = 0 := by
        refine sum_eq_zero fun A hA => ?_
        obtain ⟨hAS, hA⟩ := mem_erase.1 hA
        obtain ⟨b, hbS, hbA⟩ := exists_of_ssubset (ssubset_of_subset_of_ne (mem_powerset.1 hA) hAS)
        rw [← powerset_univ, ← insert_erase (mem_univ b), sum_powerset_insert (notMem_erase b _),
          ← sum_add_distrib]
        refine sum_eq_zero fun t ht => ?_
        have hbt : b ∉ t := fun h => notMem_erase b _ (mem_powerset.1 ht h)
        have hk : kappa S A ((insert b t).piecewise v u) = kappa S A (t.piecewise v u) := by
          funext i
          rcases eq_or_ne i b with rfl | hib
          · simp [kappa, hbS, hbA]
          · simp [kappa, piecewise_insert, Function.update_of_ne hib]
        rw [hk, neg_one_pow_card_compl_insert hbt]
        ring
      rw [h6, add_zero]
      -- `= (-1)^{|S|} ∑_z (-1)^{N_I(z, u, v)} C_α(χ_S(1)(1 - z_1) + χ_{S̄}(1)(z_1), …)`
      -- `(7)`: `= (-1)^{|S|} ∑_z (-1)^{N_I(ψ_S(z), ψ_S(u), ψ_S(v))} (-1)^{|S|} C_α(ψ_S(z))`
      -- `(8)`: `= ∑_{z ∈ ×_{i=1}^d {ψ_S(u_i), ψ_S(v_i)}} (-1)^{N_I(z, u, v)} C_α(z)
      --   = V_{C_α}(ψ_S(B))`, since `ψ_S` maps the corners of `B` bijectively to the corners
      -- of `ψ_S(B)`.
      have hinv : Function.Involutive fun s : Finset ι => symmDiff s S := fun s => by simp
      refine Fintype.sum_equiv (Function.Involutive.toPerm _ hinv) _ _ fun s => ?_
      simp only [Function.Involutive.coe_toPerm]
      rw [kappa_self_eq_psi, hcorner, neg_one_pow_card_compl_symmDiff]
      ring_nf
      congr! 3
    -- `C_α` is `d`-increasing since it is a copula. Thus,
    -- `V_{C^F_{α,S}}(B) = V_{C_α}(ψ_S(B)) ≥ 0`. This completes the proof.
    rw [hV]
    refine hC.increasing u' (fun i => ?_) v' (fun i => ?_) fun i => min_le_max
    · rcases min_choice (psi S u i) (psi S v i) with h | h <;> rw [show u' i = _ from h]
      exacts [psi_mem_unitCube S hu i, psi_mem_unitCube S hv i]
    · rcases max_choice (psi S u i) (psi S v i) with h | h <;> rw [show v' i = _ from h]
      exacts [psi_mem_unitCube S hu i, psi_mem_unitCube S hv i]

/-- **Theorem.** Let `C_α` be a `d`-copula, `S ⊆ I` and `P_U` a probability measure with
`P_U(⋂_{i ∈ I} {U_i ≤ u_i}) = C_α(u)` for `u ∈ [0,1]^d`. Then `C^F_{α,S}` is a `d`-copula and
`C^F_{α,S}(u) = ∑_{A ⊆ S} (-1)^|A| C_α(κ_{S,A}(1, u), …, κ_{S,A}(d, u))` for `u ∈ [0,1]^d`. -/
theorem flashlight (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    {C : (ι → ℝ) → ℝ} (hC : IsCopula C)
    (hμ : ∀ u ∈ unitCube ι, C u = μ.real {x | ∀ i, x i ≤ u i}) (S : Finset ι) :
    IsCopula (flashlightMeasure μ S) ∧
      ∀ u ∈ unitCube ι,
        flashlightMeasure μ S u = ∑ A ∈ S.powerset, (-1) ^ #A * C (kappa S A u) := by
  have h := fun u (hu : u ∈ unitCube ι) => flashlightMeasure_eq_flashlightSum μ hC hμ S hu
  exact ⟨(isCopula_flashlightSum hC S).congr fun u hu => (h u hu).symm, h⟩

end Flashlight
