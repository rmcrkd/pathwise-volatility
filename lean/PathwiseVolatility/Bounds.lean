/-
Copyright (c) 2026 Ryan McCrickerd. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCrickerd
-/
import PathwiseVolatility.Basic

/-!
# Section 2.3: bounds, monotonicity and existence conditions

The upper bound `φ̄ (t) = inf {x > ξ : f (t, x) < 0}` of Lemma 2.6, valued in `[ξ, ∞]`, the
spatial bounds `ξ ≤ φ ≤ φ̄` (Lemma 2.6), strict increase and the maximality condition of
Theorem 2.8, Lemma 2.9 (temporal existence) and the first half of Corollary 2.11.
-/

open Set Filter Topology

namespace PathwiseVolatility

/-- The upper bound of Lemma 2.4 and Lemma 2.6, `φ̄ (t) = inf {x > ξ : f (t, x) < 0}`, with
`inf ∅ = ∞`. -/
noncomputable def upperBound (f : ℝ → ℝ → ℝ) (ξ t : ℝ) : EReal :=
  ⨅ x ∈ {x : ℝ | ξ < x ∧ f t x < 0}, (x : EReal)

variable {f : ℝ → ℝ → ℝ} {τ ξ : ℝ} {T : EReal} {φ : ℝ → ℝ}

/-- `y ≤ φ̄ (t)` says that `y` lies at or below every level `x > ξ` where `f (t, x) < 0`. -/
theorem le_upperBound_iff {t y : ℝ} :
    (y : EReal) ≤ upperBound f ξ t ↔ ∀ x, ξ < x → f t x < 0 → y ≤ x := by
  simp only [upperBound, le_iInf_iff, mem_ofPred_eq, EReal.coe_le_coe_iff, and_imp]

/-- `φ̄ (t)` is finite exactly when `f (t, x) < 0` at some level `x > ξ`. -/
theorem upperBound_lt_top_iff {t : ℝ} :
    upperBound f ξ t < ⊤ ↔ ∃ x, ξ < x ∧ f t x < 0 := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    refine absurd h (not_lt.mpr (le_of_eq ?_))
    simp only [upperBound, mem_ofPred_eq]
    exact (iInf₂_eq_top.mpr fun x hx => absurd hx.2 (not_lt.mpr (hne x hx.1))).symm
  · rintro ⟨x, hx, hfx⟩
    exact (iInf₂_le (f := fun (x : ℝ) (_ : ξ < x ∧ f t x < 0) => (x : EReal)) x ⟨hx, hfx⟩).trans_lt
      (EReal.coe_lt_top x)

/-- Lemma 2.6 (Spatial solution bounds), lower bound, when `f (τ, ξ) > 0`. -/
theorem le_solution_of_pos (hf : InF f) (hpos : 0 < f τ ξ) (hφ : IsSolution f τ ξ T φ) {t : ℝ}
    (ht : t ∈ Dom τ T) : ξ ≤ φ t := by
  by_contra hlt
  obtain ⟨s, hs, hgs, habove⟩ := exists_last_le (g := fun u => -φ u) (y := -ξ) ht.1
    (hφ.continuousOn.mono (Icc_subset_dom ht)).neg (by simp [hφ.init])
    (by simp only [neg_lt_neg_iff]; exact not_le.mp hlt)
  have hφs : φ s = ξ := by simpa using hgs
  have hsT : s ∈ Dom τ T := Icc_subset_dom ht ⟨hs.1, hs.2.le⟩
  have hd := (hφ.deriv s hsT).mono
    (fun u (hu : u ∈ Ioc s t) => Icc_subset_dom ht ⟨hs.1.trans hu.1.le, hu.2⟩)
  have hle : f s (φ s) ≤ 0 := nonpos_of_slope hd (mem_closure_Ioc_diff hs.2) fun u hu _ => by
    have h1 : φ u < φ s := by have := habove u hu; simp only [neg_lt_neg_iff] at this; linarith
    rw [slope_def_field]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [hu.1])
  rw [hφs] at hle
  linarith [hf.mono ξ hs.1]

/-- Lemma 2.6 (Spatial solution bounds), lower bound: `ξ ≤ φ`, under the line condition of
Theorem 3.1. Maximality is not needed. Where `f (τ, ξ) = 0`, a solution which dipped below
`ξ - x` would cross that level for the last time to the left of the line, before `τ + c x`. To get
there from `ξ` it would need a slope below `-1 / c` near `(τ, ξ)`, where `f` is near `0`. -/
theorem le_solution (hf : InF f) (hpos : LineCondition f τ ξ) (hφ : IsSolution f τ ξ T φ)
    {t : ℝ} (ht : t ∈ Dom τ T) : ξ ≤ φ t := by
  rcases eq_or_lt_of_le (hpos.nonneg hf) with h0 | h0
  swap
  · exact le_solution_of_pos hf h0 hφ ht
  obtain ⟨c, ε, hε, hline⟩ := hpos
  by_contra hlt
  push Not at hlt
  -- near `(τ, ξ)`, `|f| < κ = 1 / (|c| + 1)`, and `φ` stays within `δ` of `ξ` for a time `δ'`
  set κ := 1 / (|c| + 1) with hκ
  have hc1 : 0 < |c| + 1 := by positivity
  have hκpos : 0 < κ := by positivity
  obtain ⟨δ, hδ, hfδ⟩ := Metric.continuousAt_iff.mp (hf.continuous.continuousAt (x := (τ, ξ))) κ
    hκpos
  obtain ⟨δ', hδ', hφδ⟩ := Metric.continuousWithinAt_iff.mp
    (hφ.continuousOn τ (mem_dom_self hφ.lt)) δ hδ
  -- a level `ξ - x` below `φ (t)`, with `x` small
  have hmin : 0 < min δ δ' := lt_min hδ hδ'
  set m₀ := min (min (ε / 2) ((ξ - φ t) / 2)) (min δ δ' / 2) with hm₀
  have hm₀pos : 0 < m₀ := lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  set x := m₀ / (|c| + 1) with hx
  have hxpos : 0 < x := by positivity
  have hxm : x ≤ m₀ := div_le_self hm₀pos.le (by linarith [abs_nonneg c])
  have hm₁ : m₀ ≤ ε / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hm₂ : m₀ ≤ (ξ - φ t) / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hm₃ : m₀ ≤ min δ δ' / 2 := min_le_right _ _
  have hxε : x < ε := by linarith
  have hxφ : x < ξ - φ t := by linarith
  have hxδ : (|c| + 1) * x < min δ δ' := by
    rw [hx, mul_div_cancel₀ _ hc1.ne']; linarith
  -- the last time `s ≤ t` at which `φ` is at `ξ - x`
  obtain ⟨s, hs, hgs, habove⟩ := exists_last_le (g := fun u => -φ u) (y := -(ξ - x)) ht.1
    (hφ.continuousOn.mono (Icc_subset_dom ht)).neg
    (by simp only [hφ.init, neg_le_neg_iff]; linarith) (by simp only [neg_lt_neg_iff]; linarith)
  have hφs : φ s = ξ - x := by have : -φ s = -(ξ - x) := hgs; linarith
  have hsT : s ∈ Dom τ T := Icc_subset_dom ht ⟨hs.1, hs.2.le⟩
  -- there `f (s, ξ - x) ≤ 0`, so `s` is left of the line
  have hd := (hφ.deriv s hsT).mono
    (fun u (hu : u ∈ Ioc s t) => Icc_subset_dom ht ⟨hs.1.trans hu.1.le, hu.2⟩)
  have hle : f s (φ s) ≤ 0 := nonpos_of_slope hd (mem_closure_Ioc_diff hs.2) fun u hu _ => by
    have h1 : φ u < φ s := by have := habove u hu; simp only [neg_lt_neg_iff] at this; linarith
    rw [slope_def_field]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [hu.1])
  rw [hφs] at hle
  have hsline : s < τ + c * x := by
    by_contra hge
    push Not at hge
    linarith [lt_of_lt_of_le (hline x ⟨hxpos, hxε⟩) (hf.mono (ξ - x) hge)]
  have hτs : τ < s := lt_of_le_of_ne hs.1 fun h => by rw [← h, hφ.init] at hφs; linarith
  have hcpos : 0 < c := by
    by_contra hc; push Not at hc; nlinarith [mul_nonpos_of_nonneg_of_nonpos hxpos.le hc]
  -- the mean value theorem on `[τ, s]` gives a slope below `-1 / c`
  have hsub : Icc τ s ⊆ Dom τ T := fun u hu => Icc_subset_dom ht ⟨hu.1, hu.2.trans hs.2.le⟩
  obtain ⟨u, hu, hslope⟩ := exists_hasDerivAt_eq_slope φ (fun u => f u (φ u)) hτs
    (hφ.continuousOn.mono hsub) (fun u hu => (hφ.deriv u (hsub (Ioo_subset_Icc_self hu))).hasDerivAt
      (Filter.mem_of_superset (Icc_mem_nhds hu.1 (hu.2.trans hs.2)) (Icc_subset_dom ht)))
  rw [hφs, hφ.init] at hslope
  have hcx : c * x ≤ (|c| + 1) * x := by
    nlinarith [le_abs_self c]
  -- but near `(τ, ξ)`, `|f| < κ ≤ 1 / c`
  have hφu : |φ u - ξ| < δ := by
    have := hφδ (hsub (Ioo_subset_Icc_self hu))
      (by rw [Real.dist_eq, abs_of_pos (by linarith [hu.1])]
          linarith [min_le_right δ δ', hu.2])
    rwa [Real.dist_eq, hφ.init] at this
  have hfu : |f u (φ u)| < κ := by
    have := hfδ (x := (u, φ u)) (by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, abs_of_pos (by linarith [hu.1])]
      exact max_lt (by linarith [min_le_left δ δ', hu.2]) hφu)
    rwa [Real.dist_eq, show Function.uncurry f (τ, ξ) = 0 from h0.symm, sub_zero] at this
  have hval : f u (φ u) * (s - τ) = -x := by
    rw [hslope, div_mul_cancel₀ _ (sub_ne_zero.mpr hτs.ne')]; ring
  have hκc : κ * (c * x) ≤ x := by
    rw [hκ, div_mul_eq_mul_div, one_mul, div_le_iff₀ hc1]
    nlinarith [le_abs_self c]
  have e1 := mul_lt_mul_of_pos_right hfu (sub_pos.mpr hτs)
  have e2 : κ * (s - τ) ≤ κ * (c * x) := mul_le_mul_of_nonneg_left (by linarith) hκpos.le
  have e3 : -f u (φ u) * (s - τ) ≤ |f u (φ u)| * (s - τ) :=
    mul_le_mul_of_nonneg_right (by linarith [neg_abs_le (f u (φ u))]) (by linarith)
  linarith

/-- Lemma 2.6 (Spatial solution bounds), upper bound: `φ ≤ φ̄`. Maximality is not needed, and
neither is `f (τ, ξ) > 0`. -/
theorem solution_le_upperBound (hf : InF f) (hφ : IsSolution f τ ξ T φ) {t : ℝ}
    (ht : t ∈ Dom τ T) : (φ t : EReal) ≤ upperBound f ξ t := by
  rw [le_upperBound_iff]
  intro x hx hfx
  by_contra hlt
  obtain ⟨s, hs, hgs, habove⟩ := exists_last_le (g := φ) (y := x) ht.1
    (hφ.continuousOn.mono (Icc_subset_dom ht)) (by rw [hφ.init]; exact hx.le) (not_le.mp hlt)
  have hsT : s ∈ Dom τ T := Icc_subset_dom ht ⟨hs.1, hs.2.le⟩
  have hd := (hφ.deriv s hsT).mono
    (fun u (hu : u ∈ Ioc s t) => Icc_subset_dom ht ⟨hs.1.trans hu.1.le, hu.2⟩)
  have hge : 0 ≤ f s (φ s) := nonneg_of_slope hd (mem_closure_Ioc_diff hs.2) fun u hu _ => by
    rw [slope_def_field]
    exact div_nonneg (by linarith [habove u hu]) (by linarith [hu.1])
  rw [hgs] at hge
  linarith [hf.mono x hs.2.le]

/-- Lemma 2.6 (Spatial solution bounds): any solution satisfies `ξ ≤ φ ≤ φ̄` on `[τ, T)`. -/
theorem spatial_bounds (hf : InF f) (hpos : LineCondition f τ ξ) (hφ : IsSolution f τ ξ T φ) {t : ℝ}
    (ht : t ∈ Dom τ T) : ξ ≤ φ t ∧ (φ t : EReal) ≤ upperBound f ξ t :=
  ⟨le_solution hf hpos hφ ht, solution_le_upperBound hf hφ ht⟩

/-- Within the bounds, `f (t, φ (t)) ≥ 0`: a solution is never driven downwards. -/
theorem nonneg_along (hf : InF f) (hpos : LineCondition f τ ξ) (hφ : IsSolution f τ ξ T φ) {t : ℝ}
    (ht : t ∈ Dom τ T) : 0 ≤ f t (φ t) := by
  obtain ⟨hlo, hup⟩ := spatial_bounds hf hpos hφ ht
  rcases eq_or_lt_of_le hlo with h | h
  · rw [← h]; linarith [hf.mono ξ ht.1, hpos.nonneg hf]
  · by_contra hneg
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp
      (isOpen_lt (hf.continuous_level t) continuous_const) (φ t) (not_le.mp hneg)
    set y := φ t - min ε (φ t - ξ) / 2 with hy
    have hm : 0 < min ε (φ t - ξ) := lt_min hε (by linarith)
    have hξy : ξ < y := by linarith [min_le_right ε (φ t - ξ)]
    have hyφ : y < φ t := by linarith
    have hfy : f t y < 0 := hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [min_le_left ε (φ t - ξ)])
    exact absurd ((le_upperBound_iff.mp hup) y hξy hfy) (not_le.mpr hyφ)

/-- Theorem 2.8, monotonicity: a solution is non-decreasing. -/
theorem monotoneOn_solution (hf : InF f) (hpos : LineCondition f τ ξ) (hφ : IsSolution f τ ξ T φ) :
    MonotoneOn φ (Dom τ T) :=
  monotoneOn_of_hasDerivWithinAt_nonneg convex_dom hφ.continuousOn
    (fun t ht => (hφ.deriv t (interior_subset ht)).mono interior_subset)
    (fun _ ht => nonneg_along hf hpos hφ (interior_subset ht))

/-- Theorem 2.8, strict increase: a solution is strictly increasing. On an interval where it
were constant, at a level `c`, the ODE would give `f (·, c) = 0` at two different times. -/
theorem strictMonoOn_solution (hf : InF f) (hpos : LineCondition f τ ξ) (hφ : IsSolution f τ ξ T φ) :
    StrictMonoOn φ (Dom τ T) := by
  intro s hs t ht hst
  have hmono := monotoneOn_solution hf hpos hφ
  refine lt_of_le_of_ne (hmono hs ht hst.le) fun heq => ?_
  have hsub : Icc s t ⊆ Dom τ T := fun u hu => Icc_subset_dom ht ⟨hs.1.trans hu.1, hu.2⟩
  have hconst : ∀ u ∈ Icc s t, φ u = φ s := fun u hu =>
    le_antisymm (heq ▸ hmono (hsub hu) ht hu.2) (hmono hs (hsub hu) hu.1)
  have hzero : ∀ u ∈ Ioo s t, f u (φ s) = 0 := by
    intro u hu
    have hnhds : Icc s t ∈ 𝓝 u := Icc_mem_nhds hu.1 hu.2
    have h1 : HasDerivAt φ (f u (φ u)) u :=
      (hφ.deriv u (hsub (Ioo_subset_Icc_self hu))).hasDerivAt (Filter.mem_of_superset hnhds hsub)
    have h0 : HasDerivAt φ 0 u :=
      (hasDerivAt_const u (φ s)).congr_of_eventuallyEq
        (Filter.mem_of_superset hnhds fun v hv => hconst v hv)
    rw [hconst u (Ioo_subset_Icc_self hu)] at h1
    exact h1.unique h0
  have h1 := hzero ((2 * s + t) / 3) ⟨by linarith, by linarith⟩
  have h2 := hzero ((s + 2 * t) / 3) ⟨by linarith, by linarith⟩
  have := hf.strictMono (φ s) (show (2 * s + t) / 3 < (s + 2 * t) / 3 by linarith)
  simp only at this
  linarith

/-- Theorem 2.8, maximality: a maximal solution has `T = ∞` or is unbounded above, the
thesis's `T_* ∨ X_* = ∞`. -/
theorem maximal_unbounded (hf : InF f) (hpos : LineCondition f τ ξ) (hφ : IsMaximalSolution f τ ξ T φ) :
    T = ⊤ ∨ ¬ BddAbove (φ '' Dom τ T) := by
  refine hφ.maximal.imp id fun hnb hb => hnb ?_
  obtain ⟨M, hM⟩ := hb
  refine ⟨max M |ξ|, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  have hlo := le_solution hf hpos hφ.toIsSolution ht
  have hup : φ t ≤ M := hM ⟨t, ht, rfl⟩
  show |φ t| ≤ max M |ξ|
  rcases le_or_gt 0 (φ t) with h | h
  · rw [abs_of_nonneg h]; exact hup.trans (le_max_left _ _)
  · rw [abs_of_neg h]; exact (show -φ t ≤ |ξ| by linarith [neg_abs_le ξ]).trans (le_max_right _ _)

/-- Lemma 2.9 (Temporal existence): if `φ̄ (T₀) < ∞`, a maximal solution exists beyond `T₀`. The
thesis takes `T₀ > τ`, which is not needed. -/
theorem lt_of_upperBound_lt_top (hf : InF f) (hpos : LineCondition f τ ξ) (hφ : IsMaximalSolution f τ ξ T φ) {T₀ : ℝ}
    (hT₀ : upperBound f ξ T₀ < ⊤) : (T₀ : EReal) < T := by
  by_contra hle
  push Not at hle
  obtain ⟨x, hx, hfx⟩ := upperBound_lt_top_iff.mp hT₀
  have hbdd : BddAbove ((fun t => |φ t|) '' Dom τ T) := by
    refine ⟨max |x| |ξ|, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    have htT₀ : t ≤ T₀ := EReal.coe_le_coe_iff.mp (ht.2.le.trans hle)
    have hup : φ t ≤ x := le_upperBound_iff.mp (solution_le_upperBound hf hφ.toIsSolution ht) x hx
      (lt_of_le_of_lt (hf.mono x htT₀) hfx)
    have hlo := le_solution hf hpos hφ.toIsSolution ht
    exact abs_le.mpr ⟨by linarith [neg_abs_le ξ, le_max_right |x| |ξ|],
      by linarith [le_abs_self x, le_max_left |x| |ξ|]⟩
  rcases hφ.maximal with h | h
  · exact absurd (h ▸ hle) (not_le.mpr (EReal.coe_lt_top T₀))
  · exact h hbdd

/-- Lemma 2.9, the extension: if `φ̄ (t) < ∞` for every `t ≥ τ`, then `T = ∞`. -/
theorem eq_top_of_upperBound_lt_top (hf : InF f) (hpos : LineCondition f τ ξ)
    (hφ : IsMaximalSolution f τ ξ T φ) (hb : ∀ t, τ ≤ t → upperBound f ξ t < ⊤) : T = ⊤ := by
  by_contra hT
  have hbot : T ≠ ⊥ := ne_bot_of_gt hφ.lt
  have hτT : τ ≤ T.toReal := by
    have := hφ.lt; rw [← EReal.coe_toReal hT hbot] at this
    exact (EReal.coe_lt_coe_iff.mp this).le
  have := lt_of_upperBound_lt_top hf hpos hφ (hb _ hτT)
  rw [EReal.coe_toReal hT hbot] at this
  exact lt_irrefl _ this

/-- Corollary 2.11 (Spatio-temporal existence), first half: if `f (t, ·)` is negative somewhere
in `[ξ, ∞)` at every `t ≥ τ`, then `T = ∞`. -/
theorem eq_top_of_neg (hf : InF f) (hpos : LineCondition f τ ξ) (hφ : IsMaximalSolution f τ ξ T φ)
    (hneg : ∀ t, τ ≤ t → ∃ x, ξ ≤ x ∧ f t x < 0) : T = ⊤ := by
  refine eq_top_of_upperBound_lt_top hf hpos hφ fun t ht => upperBound_lt_top_iff.mpr ?_
  obtain ⟨x, hx, hfx⟩ := hneg t ht
  refine ⟨x, lt_of_le_of_ne hx fun h => ?_, hfx⟩
  rw [← h] at hfx
  linarith [hf.mono ξ ht, hpos.nonneg hf]

end PathwiseVolatility
