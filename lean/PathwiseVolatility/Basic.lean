/-
Copyright (c) 2026 Ryan McCrickerd. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCrickerd
-/
import Mathlib

/-!
# The IVPs of Chapter 2

The thesis's notation: `f t x` is the driving function at time `t` and level `x`, the initial
value is `(τ, ξ)`, and a solution lives on `[τ, T)` with `T ∈ (τ, ∞]`. Times `T` and the bound
`φ̄ (t) ∈ [ξ, ∞]` are extended reals. This file has Definition 1.1 (the set `F`), Problem 1.2
(maximal solutions), and two facts about crossings and slopes used in the proofs.
-/

open Set Filter Topology

namespace PathwiseVolatility

/-- Definition 1.1, the set `F`: `f` is continuous on `ℝ²`, each `f (·, x)` is strictly
increasing, and `f (τ, ξ) > 0` for some `(τ, ξ)`. -/
structure InF (f : ℝ → ℝ → ℝ) : Prop where
  continuous : Continuous (Function.uncurry f)
  strictMono : ∀ x, StrictMono fun t => f t x
  exists_pos : ∃ τ ξ, 0 < f τ ξ

/-- The interval `[τ, T)`, for `T ∈ (τ, ∞]`; `T = ⊤` gives `[τ, ∞)`. -/
def Dom (τ : ℝ) (T : EReal) : Set ℝ := {t | τ ≤ t ∧ (t : EReal) < T}

/-- A solution of the IVP `x' = f (t, x)`, `x (τ) = ξ` on `[τ, T)`. At `τ` the derivative is a
right derivative, as in the thesis. -/
structure IsSolution (f : ℝ → ℝ → ℝ) (τ ξ : ℝ) (T : EReal) (φ : ℝ → ℝ) : Prop where
  lt : (τ : EReal) < T
  init : φ τ = ξ
  deriv : ∀ t ∈ Dom τ T, HasDerivWithinAt φ (f t (φ t)) (Dom τ T) t

/-- Problem 1.2: a maximal solution, one with `T ∨ sup_{[τ, T)} |φ| = ∞`. -/
structure IsMaximalSolution (f : ℝ → ℝ → ℝ) (τ ξ : ℝ) (T : EReal) (φ : ℝ → ℝ) : Prop
    extends IsSolution f τ ξ T φ where
  maximal : T = ⊤ ∨ ¬ BddAbove ((fun t => |φ t|) '' Dom τ T)

variable {f : ℝ → ℝ → ℝ} {τ ξ : ℝ} {T : EReal} {φ : ℝ → ℝ}

theorem InF.continuous_level (hf : InF f) (t : ℝ) : Continuous fun x => f t x :=
  hf.continuous.comp (continuous_const.prodMk continuous_id)

theorem InF.continuous_time (hf : InF f) (x : ℝ) : Continuous fun t => f t x :=
  hf.continuous.comp (continuous_id.prodMk continuous_const)

theorem InF.mono (hf : InF f) (x : ℝ) {s t : ℝ} (hst : s ≤ t) : f s x ≤ f t x :=
  (hf.strictMono x).monotone hst

theorem mem_dom_self (h : (τ : EReal) < T) : τ ∈ Dom τ T := ⟨le_rfl, h⟩

theorem Icc_subset_dom {t : ℝ} (ht : t ∈ Dom τ T) : Icc τ t ⊆ Dom τ T :=
  fun _ hu => ⟨hu.1, (EReal.coe_le_coe_iff.mpr hu.2).trans_lt ht.2⟩

theorem convex_dom : Convex ℝ (Dom τ T) :=
  convex_iff_ordConnected.mpr
    ⟨fun _ hx _ hy _ hz => ⟨hx.1.trans hz.1, (EReal.coe_le_coe_iff.mpr hz.2).trans_lt hy.2⟩⟩

theorem IsSolution.continuousOn (hφ : IsSolution f τ ξ T φ) : ContinuousOn φ (Dom τ T) :=
  fun t ht => (hφ.deriv t ht).continuousWithinAt

/-- The condition of Theorem 3.1, which replaces `f (τ, ξ) > 0`: `f > 0` on a line
`{(τ + c x, ξ - x) : x ∈ (0, ε)}` running down from `(τ, ξ)`. -/
def LineCondition (f : ℝ → ℝ → ℝ) (τ ξ : ℝ) : Prop :=
  ∃ c ε : ℝ, 0 < ε ∧ ∀ x ∈ Ioo 0 ε, 0 < f (τ + c * x) (ξ - x)

/-- `f (τ, ξ) > 0` gives the line condition, with a vertical line. -/
theorem lineCondition_of_pos (hf : InF f) (h : 0 < f τ ξ) : LineCondition f τ ξ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp
    (isOpen_lt continuous_const (hf.continuous_level τ)) ξ h
  refine ⟨0, ε, hε, fun x hx => ?_⟩
  rw [zero_mul, add_zero]
  exact hball (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hx.1, hx.2])

/-- The line condition gives `f (τ, ξ) ≥ 0`, by continuity. -/
theorem LineCondition.nonneg (h : LineCondition f τ ξ) (hf : InF f) : 0 ≤ f τ ξ := by
  obtain ⟨c, ε, hε, hline⟩ := h
  have hpath : Tendsto (fun x : ℝ => (τ + c * x, ξ - x)) (𝓝[>] 0) (𝓝 (τ, ξ)) := by
    have hc : Continuous (fun x : ℝ => (τ + c * x, ξ - x)) := by fun_prop
    have := hc.tendsto 0
    simp only [mul_zero, add_zero, sub_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun x => f (τ + c * x) (ξ - x)) (𝓝[>] 0) (𝓝 (f τ ξ)) :=
    (hf.continuous.tendsto (τ, ξ)).comp hpath
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT hε] with x hx using (hline x hx).le

/-! ### Crossings and slopes -/

/-- A continuous function on `[a, b]` which starts at or below `y` and ends above it leaves `y`
for the last time at some `s ∈ [a, b)`: `g (s) = y`, and `g > y` on `(s, b]`. -/
theorem exists_last_le {g : ℝ → ℝ} {a b y : ℝ} (hab : a ≤ b) (hg : ContinuousOn g (Icc a b))
    (ha : g a ≤ y) (hb : y < g b) : ∃ s ∈ Ico a b, g s = y ∧ ∀ u ∈ Ioc s b, y < g u := by
  set S := Icc a b ∩ g ⁻¹' Iic y with hS
  have hcl : IsClosed S := hg.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hne : S.Nonempty := ⟨a, ⟨le_rfl, hab⟩, ha⟩
  have hbdd : BddAbove S := ⟨b, fun u hu => hu.1.2⟩
  have hmem : sSup S ∈ S := hcl.csSup_mem hne hbdd
  have hsb : sSup S < b := lt_of_le_of_ne hmem.1.2 fun h => by
    have := hmem.2; rw [h] at this; exact absurd this (not_le.mpr hb)
  have habove : ∀ u ∈ Ioc (sSup S) b, y < g u := fun u hu => by
    by_contra h
    exact absurd (le_csSup hbdd ⟨⟨hmem.1.1.trans hu.1.le, hu.2⟩, not_lt.mp h⟩) (not_le.mpr hu.1)
  have hge : y ≤ g (sSup S) := by
    have hcl' : IsClosed (Icc a b ∩ g ⁻¹' Ici y) :=
      hg.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hsub : Ioc (sSup S) b ⊆ Icc a b ∩ g ⁻¹' Ici y := fun u hu =>
      ⟨⟨hmem.1.1.trans hu.1.le, hu.2⟩, (habove u hu).le⟩
    have hcls : sSup S ∈ closure (Ioc (sSup S) b) := by
      rw [closure_Ioc hsb.ne]; exact ⟨le_rfl, hsb.le⟩
    exact (closure_minimal hsub hcl' hcls).2
  exact ⟨sSup S, ⟨hmem.1.1, hsb⟩, le_antisymm hmem.2 hge, habove⟩

/-- A continuous function on `[a, b]` which is positive at `a` and not positive at `b` first
reaches `0` at some `s ∈ (a, b]`: `g (s) = 0`, and `g > 0` on `[a, s)`. -/
theorem exists_first_nonpos {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hg : ContinuousOn g (Icc a b))
    (ha : 0 < g a) (hb : g b ≤ 0) : ∃ s ∈ Ioc a b, g s = 0 ∧ ∀ u ∈ Ico a s, 0 < g u := by
  set S := Icc a b ∩ g ⁻¹' Iic 0 with hS
  have hcl : IsClosed S := hg.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hne : S.Nonempty := ⟨b, ⟨hab, le_rfl⟩, hb⟩
  have hbdd : BddBelow S := ⟨a, fun u hu => hu.1.1⟩
  have hmem : sInf S ∈ S := hcl.csInf_mem hne hbdd
  have has : a < sInf S := lt_of_le_of_ne hmem.1.1 fun h => by
    have := hmem.2; rw [← h] at this; exact absurd this (not_le.mpr ha)
  have hbelow : ∀ u ∈ Ico a (sInf S), 0 < g u := fun u hu => by
    by_contra h
    exact absurd (csInf_le hbdd ⟨⟨hu.1, hu.2.le.trans hmem.1.2⟩, not_lt.mp h⟩) (not_le.mpr hu.2)
  have hge : 0 ≤ g (sInf S) := by
    have hcl' : IsClosed (Icc a b ∩ g ⁻¹' Ici 0) :=
      hg.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hsub : Ico a (sInf S) ⊆ Icc a b ∩ g ⁻¹' Ici 0 := fun u hu =>
      ⟨⟨hu.1, hu.2.le.trans hmem.1.2⟩, (hbelow u hu).le⟩
    have hcls : sInf S ∈ closure (Ico a (sInf S)) := by
      rw [closure_Ico has.ne]; exact ⟨has.le, le_rfl⟩
    exact (closure_minimal hsub hcl' hcls).2
  exact ⟨sInf S, ⟨has, hmem.1.2⟩, le_antisymm hmem.2 hge, hbelow⟩

/-- A derivative within `S` is non-negative if every slope from `s` into `S` is. -/
theorem nonneg_of_slope {g : ℝ → ℝ} {d s : ℝ} {S : Set ℝ} (hd : HasDerivWithinAt g d S s)
    (hS : s ∈ closure (S \ {s})) (h : ∀ u ∈ S, u ≠ s → 0 ≤ slope g s u) : 0 ≤ d := by
  have : (𝓝[S \ {s}] s).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hS
  exact ge_of_tendsto (hasDerivWithinAt_iff_tendsto_slope.mp hd)
    (eventually_nhdsWithin_of_forall fun u hu => h u hu.1 hu.2)

/-- A derivative within `S` is non-positive if every slope from `s` into `S` is. -/
theorem nonpos_of_slope {g : ℝ → ℝ} {d s : ℝ} {S : Set ℝ} (hd : HasDerivWithinAt g d S s)
    (hS : s ∈ closure (S \ {s})) (h : ∀ u ∈ S, u ≠ s → slope g s u ≤ 0) : d ≤ 0 := by
  have : (𝓝[S \ {s}] s).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hS
  exact le_of_tendsto (hasDerivWithinAt_iff_tendsto_slope.mp hd)
    (eventually_nhdsWithin_of_forall fun u hu => h u hu.1 hu.2)

theorem mem_closure_Ioc_diff {s b : ℝ} (hsb : s < b) : s ∈ closure (Ioc s b \ {s}) := by
  have h : Ioo s b ⊆ Ioc s b \ {s} := fun u hu => ⟨Ioo_subset_Ioc_self hu, ne_of_gt hu.1⟩
  exact closure_mono h (by rw [closure_Ioo hsb.ne]; exact ⟨le_rfl, hsb.le⟩)

theorem mem_closure_Icc_diff {a s : ℝ} (has : a < s) : s ∈ closure (Icc a s \ {s}) := by
  have h : Ico a s ⊆ Icc a s \ {s} := fun u hu => ⟨Ico_subset_Icc_self hu, ne_of_lt hu.2⟩
  exact closure_mono h (by rw [closure_Ico has.ne]; exact ⟨has.le, le_rfl⟩)

end PathwiseVolatility
