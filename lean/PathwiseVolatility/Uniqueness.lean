/-
Copyright (c) 2026 Ryan McCrickerd. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCrickerd
-/
import PathwiseVolatility.Bounds

/-!
# Section 2.4: maximal uniqueness

Theorem 2.17 and Corollary 2.1, apart from existence. The proof is not the thesis's, which goes
through the solutions' inverses and Lebesgue's theorem (Lemma 2.16). Here a solution started a
little later in time, `t ↦ φ₁ (t + h)`, stays strictly above any other solution `φ₂`: where they
would first meet, at a level `c`, the copy has the slope `f (t + h, c) > f (t, c)`, since
`f (·, c)` is strictly increasing. Letting `h → 0` gives `φ₂ ≤ φ₁`, and by symmetry `φ₁ = φ₂`.
-/

open Set Filter Topology

namespace PathwiseVolatility

variable {f : ℝ → ℝ → ℝ} {τ ξ : ℝ} {T₁ T₂ : EReal} {φ₁ φ₂ : ℝ → ℝ}

/-- For `h > 0`, `φ₂ (t) < φ₁ (t + h)` wherever both are defined. -/
theorem lt_shift (hf : InF f) (hpos : LineCondition f τ ξ) (h₁ : IsSolution f τ ξ T₁ φ₁)
    (h₂ : IsSolution f τ ξ T₂ φ₂) {t h : ℝ} (ht : t ∈ Dom τ T₂) (hh : 0 < h)
    (hth : t + h ∈ Dom τ T₁) : φ₂ t < φ₁ (t + h) := by
  have hmaps : MapsTo (fun u => u + h) (Icc τ t) (Dom τ T₁) := fun u hu =>
    Icc_subset_dom hth ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hg : ContinuousOn (fun u => φ₁ (u + h) - φ₂ u) (Icc τ t) :=
    (h₁.continuousOn.comp (continuous_id.add continuous_const).continuousOn hmaps).sub
      (h₂.continuousOn.mono (Icc_subset_dom ht))
  have hg0 : 0 < φ₁ (τ + h) - φ₂ τ := by
    have := strictMonoOn_solution hf hpos h₁ (mem_dom_self h₁.lt) (hmaps ⟨le_rfl, ht.1⟩)
      (show τ < τ + h by linarith)
    rw [h₁.init] at this
    rw [h₂.init]
    linarith
  by_contra hle
  obtain ⟨s, hs, hgs, hbefore⟩ := exists_first_nonpos (g := fun u => φ₁ (u + h) - φ₂ u) ht.1 hg
    hg0 (show φ₁ (t + h) - φ₂ t ≤ 0 by linarith [not_lt.mp hle])
  have hc : φ₁ (s + h) = φ₂ s := by
    have : φ₁ (s + h) - φ₂ s = 0 := hgs
    linarith
  have hsub : Icc τ s ⊆ Icc τ t := Icc_subset_Icc_right hs.2
  have hd₁ : HasDerivWithinAt (fun u => φ₁ (u + h)) (f (s + h) (φ₁ (s + h))) (Icc τ s) s := by
    have := (h₁.deriv (s + h) (hmaps ⟨hs.1.le, hs.2⟩)).comp s
      ((hasDerivAt_id' s).add_const h).hasDerivWithinAt (hmaps.mono_left hsub)
    rw [mul_one] at this
    exact this
  have hd₂ : HasDerivWithinAt φ₂ (f s (φ₂ s)) (Icc τ s) s :=
    (h₂.deriv s (Icc_subset_dom ht ⟨hs.1.le, hs.2⟩)).mono fun u hu => Icc_subset_dom ht (hsub hu)
  have hd := nonpos_of_slope (hd₁.sub hd₂) (mem_closure_Icc_diff hs.1) fun u hu hne => by
    have hu' : u < s := lt_of_le_of_ne hu.2 hne
    have hgu : 0 < φ₁ (u + h) - φ₂ u := hbefore u ⟨hu.1, hu'⟩
    rw [slope_def_field]
    show (φ₁ (u + h) - φ₂ u - (φ₁ (s + h) - φ₂ s)) / (u - s) ≤ 0
    rw [hc, sub_self, sub_zero]
    exact div_nonpos_iff.mpr (Or.inl ⟨hgu.le, by linarith⟩)
  rw [hc] at hd
  have := hf.strictMono (φ₂ s) (show s < s + h by linarith)
  simp only at this
  linarith

/-- Of two solutions, the second is at most the first wherever both are defined. -/
theorem le_of_solutions (hf : InF f) (hpos : LineCondition f τ ξ) (h₁ : IsSolution f τ ξ T₁ φ₁)
    (h₂ : IsSolution f τ ξ T₂ φ₂) {t : ℝ} (ht₁ : t ∈ Dom τ T₁) (ht₂ : t ∈ Dom τ T₂) :
    φ₂ t ≤ φ₁ t := by
  by_contra hlt
  push Not at hlt
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.continuousWithinAt_iff.mp (h₁.continuousOn t ht₁) (φ₂ t - φ₁ t) (by linarith)
  obtain ⟨r, htr, hrT⟩ := EReal.lt_iff_exists_real_btwn.mp ht₁.2
  have htr' : t < r := EReal.coe_lt_coe_iff.mp htr
  set h := min (δ / 2) ((r - t) / 2) with hh_def
  have hh : 0 < h := lt_min (by linarith) (by linarith)
  have hth : t + h ∈ Dom τ T₁ :=
    ⟨by linarith [ht₁.1], lt_of_le_of_lt
      (EReal.coe_le_coe_iff.mpr (by linarith [min_le_right (δ / 2) ((r - t) / 2)])) hrT⟩
  have h1 := lt_shift hf hpos h₁ h₂ ht₂ hh hth
  have h2 := hball hth (by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [min_le_left (δ / 2) ((r - t) / 2)])
  rw [Real.dist_eq, abs_lt] at h2
  linarith [h2.2]

/-- Two solutions agree wherever both are defined; maximality is not needed. -/
theorem solutions_eqOn (hf : InF f) (hpos : LineCondition f τ ξ) (h₁ : IsSolution f τ ξ T₁ φ₁)
    (h₂ : IsSolution f τ ξ T₂ φ₂) : EqOn φ₁ φ₂ (Dom τ T₁ ∩ Dom τ T₂) := fun _ ht =>
  le_antisymm (le_of_solutions hf hpos h₂ h₁ ht.2 ht.1) (le_of_solutions hf hpos h₁ h₂ ht.1 ht.2)

/-- A maximal solution's interval cannot be strictly shorter than another solution's: the other
solution is bounded on the closed interval `[τ, T₁]`, so the two could not agree on `[τ, T₁)`. -/
theorem not_lt_of_maximal (hf : InF f) (hpos : LineCondition f τ ξ) (h₁ : IsMaximalSolution f τ ξ T₁ φ₁)
    (h₂ : IsSolution f τ ξ T₂ φ₂) : ¬ T₁ < T₂ := by
  intro hlt
  have hT₁ : T₁ ≠ ⊤ := ne_top_of_lt hlt
  have hr : ((T₁.toReal : ℝ) : EReal) = T₁ := EReal.coe_toReal hT₁ (ne_bot_of_gt h₁.lt)
  have hsub : Icc τ T₁.toReal ⊆ Dom τ T₂ := fun u hu =>
    ⟨hu.1, (EReal.coe_le_coe_iff.mpr hu.2).trans_lt (by rw [hr]; exact hlt)⟩
  have hdom : Dom τ T₁ ⊆ Icc τ T₁.toReal := fun u hu =>
    ⟨hu.1, EReal.coe_le_coe_iff.mp (by rw [hr]; exact hu.2.le)⟩
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (h₂.continuousOn.mono hsub)
  rcases h₁.maximal with h | h
  · exact hT₁ h
  · refine h ⟨C, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    have heq := solutions_eqOn hf hpos h₁.toIsSolution h₂ ⟨hu, hsub (hdom hu)⟩
    show |φ₁ u| ≤ C
    rw [heq]
    simpa [Real.norm_eq_abs] using hC u (hdom hu)

/-- Theorem 2.17 (Maximal uniqueness), and Corollary 2.1: two maximal solutions have the same
interval `[τ, T)` and agree on it. -/
theorem maximal_uniqueness (hf : InF f) (hpos : LineCondition f τ ξ) (h₁ : IsMaximalSolution f τ ξ T₁ φ₁)
    (h₂ : IsMaximalSolution f τ ξ T₂ φ₂) : T₁ = T₂ ∧ EqOn φ₁ φ₂ (Dom τ T₁) := by
  have hT : T₁ = T₂ := le_antisymm (not_lt.mp (not_lt_of_maximal hf hpos h₂ h₁.toIsSolution))
    (not_lt.mp (not_lt_of_maximal hf hpos h₁ h₂.toIsSolution))
  exact ⟨hT, fun t ht => solutions_eqOn hf hpos h₁.toIsSolution h₂.toIsSolution ⟨ht, hT ▸ ht⟩⟩

end PathwiseVolatility
