/-
Copyright (c) 2026 Ryan McCrickerd. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCrickerd
-/
import PathwiseVolatility.Bounds

/-!
# Section 2.5: continuous dependence

Theorem 2.18 (Solution map continuity). The proof is not the thesis's, which extracts convergent
subsequences by the Arzelà–Ascoli lemma and identifies their limits by uniqueness, extending the
interval of convergence step by step. Here the solutions are bracketed by time-shifted copies of
the limit solution. For `h > 0`, `f₀ (t + h, x) - f₀ (t, x) ≥ m > 0` on the compact box, since
`f₀ (·, x)` is strictly increasing. Once `f_n` is within `m` of `f₀` there, comparison at first
meeting points gives `φ₀ (t - h) < φ_n (t) < φ₀ (t + h)`, which also keeps `φ_n` from ending
before `T`.
-/

open Set Filter Topology

namespace PathwiseVolatility

/-- Comparison at a first meeting point: if `v < u` at `a`, and wherever the two meet after `a`
the left derivative of `v` is below that of `u`, then `v < u` up to `b`. -/
theorem lt_of_first_meeting {u v : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hu : ContinuousOn u (Icc a b)) (hv : ContinuousOn v (Icc a b)) (h0 : v a < u a)
    (hd : ∀ s ∈ Ioc a b, u s = v s → ∃ du dv, HasDerivWithinAt u du (Icc a s) s ∧
      HasDerivWithinAt v dv (Icc a s) s ∧ dv < du) : v b < u b := by
  by_contra hle
  obtain ⟨s, hs, hgs, hbefore⟩ := exists_first_nonpos (g := fun t => u t - v t) hab (hu.sub hv)
    (show 0 < u a - v a by linarith) (show u b - v b ≤ 0 by linarith [not_lt.mp hle])
  have hsuv : u s = v s := by have : u s - v s = 0 := hgs; linarith
  obtain ⟨du, dv, hdu, hdv, hlt⟩ := hd s hs hsuv
  have := nonpos_of_slope (hdu.sub hdv) (mem_closure_Icc_diff hs.1) fun t ht hne => by
    have ht' : t < s := lt_of_le_of_ne ht.2 hne
    have hgt : 0 < u t - v t := hbefore t ⟨ht.1, ht'⟩
    rw [slope_def_field]
    show (u t - v t - (u s - v s)) / (t - s) ≤ 0
    rw [hsuv, sub_self, sub_zero]
    exact div_nonpos_iff.mpr (Or.inl ⟨hgt.le, by linarith⟩)
  linarith

variable {f₀ : ℝ → ℝ → ℝ} {τ ξ : ℝ} {T₀ : EReal} {φ₀ : ℝ → ℝ}

/-- Theorem 2.18 (Solution map continuity): if `f_n → f₀` uniformly on `[τ, T] × [ξ, X]`, where
`T < T₀` and `X > φ₀ (T)`, then the maximal solutions `φ_n` exist on `[τ, T]` from some `n` on,
and converge to `φ₀` uniformly there. -/
theorem solution_map_continuous (hf₀ : InF f₀) (hpos₀ : LineCondition f₀ τ ξ)
    (hφ₀ : IsMaximalSolution f₀ τ ξ T₀ φ₀) {f : ℕ → ℝ → ℝ → ℝ} {T' : ℕ → EReal}
    {φ : ℕ → ℝ → ℝ} (hf : ∀ n, InF (f n)) (hpos : ∀ n, LineCondition (f n) τ ξ)
    (hφ : ∀ n, IsMaximalSolution (f n) τ ξ (T' n) (φ n)) {T X : ℝ} (hτT : τ < T)
    (hTT₀ : (T : EReal) < T₀) (hX : φ₀ T < X)
    (hconv : ∀ η > 0, ∀ᶠ n in atTop, ∀ t ∈ Icc τ T, ∀ x ∈ Icc ξ X, |f n t x - f₀ t x| < η) :
    ∀ ε > 0, ∀ᶠ n in atTop, (T : EReal) < T' n ∧ ∀ t ∈ Icc τ T, |φ n t - φ₀ t| < ε := by
  intro ε hε
  have hs₀ := hφ₀.toIsSolution
  have hmono₀ := strictMonoOn_solution hf₀ hpos₀ hs₀
  -- a time `r ∈ (T, T₀)`, and the uniform continuity of `φ₀` on `[τ, r]`
  obtain ⟨r, hTr, hrT₀⟩ := EReal.lt_iff_exists_real_btwn.mp hTT₀
  have hTr' : T < r := EReal.coe_lt_coe_iff.mp hTr
  have hdom₀ : ∀ t ∈ Icc τ r, t ∈ Dom τ T₀ := fun t ht =>
    ⟨ht.1, (EReal.coe_le_coe_iff.mpr ht.2).trans_lt hrT₀⟩
  have hξX : ξ < X := by
    have := le_solution hf₀ hpos₀ hs₀ (hdom₀ T ⟨hτT.le, hTr'.le⟩); linarith
  set ε₁ := min ε (X - φ₀ T) with hε₁
  have hε₁pos : 0 < ε₁ := lt_min hε (by linarith)
  obtain ⟨δ, hδ, huc⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous (hs₀.continuousOn.mono hdom₀)) ε₁ hε₁pos
  set h := min (δ / 2) ((r - T) / 2) with hh
  have hhpos : 0 < h := lt_min (by linarith) (by linarith)
  have hhδ : h < δ := (min_le_left _ _).trans_lt (by linarith)
  have hTh : T + h < r := by linarith [min_le_right (δ / 2) ((r - T) / 2)]
  -- `φ₀` moves by less than `ε₁` over a time `h`
  have hclose : ∀ t ∈ Icc τ T, φ₀ (t + h) - φ₀ t < ε₁ := by
    intro t ht
    have := huc (t + h) ⟨by linarith [ht.1], by linarith [ht.2]⟩ t ⟨ht.1, by linarith [ht.2]⟩
      (by rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hhpos]; exact hhδ)
    rw [Real.dist_eq] at this
    linarith [le_abs_self (φ₀ (t + h) - φ₀ t)]
  have hTX : φ₀ (T + h) < X := by
    linarith [hclose T ⟨hτT.le, le_rfl⟩, min_le_right ε (X - φ₀ T)]
  -- the gap `m` between `f₀` and its shift by `h` on the box
  obtain ⟨p₀, hp₀, hmin⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMinOn
    (nonempty_Icc.mpr hτT.le |>.prod (nonempty_Icc.mpr hξX.le))
    (((hf₀.continuous.comp ((continuous_fst.add continuous_const).prodMk continuous_snd)).sub
      hf₀.continuous).continuousOn (s := Icc τ T ×ˢ Icc ξ X))
  set m := f₀ (p₀.1 + h) p₀.2 - f₀ p₀.1 p₀.2 with hm
  have hmpos : 0 < m := by
    have := hf₀.strictMono p₀.2 (show p₀.1 < p₀.1 + h by linarith)
    simp only at this
    linarith
  have hgap : ∀ t ∈ Icc τ T, ∀ x ∈ Icc ξ X, m ≤ f₀ (t + h) x - f₀ t x := fun t ht x hx =>
    hmin (mk_mem_prod ht hx)
  filter_upwards [hconv m hmpos] with n hn
  have hsn := (hφ n).toIsSolution
  -- the upper bracket `φ_n (t) < φ₀ (t + h)`
  have hupper : ∀ t ∈ Icc τ T, t ∈ Dom τ (T' n) → φ n t < φ₀ (t + h) := by
    intro t ht htn
    have hmaps : MapsTo (fun u => u + h) (Icc τ t) (Dom τ T₀) := fun u hu =>
      hdom₀ _ ⟨by linarith [hu.1], by linarith [hu.2, ht.2]⟩
    refine lt_of_first_meeting (u := fun s => φ₀ (s + h)) (v := φ n) ht.1 (hs₀.continuousOn.comp
      (continuous_id.add continuous_const).continuousOn hmaps)
      (hsn.continuousOn.mono (Icc_subset_dom htn)) ?_ fun s hs hmeet => ?_
    · show φ n τ < φ₀ (τ + h)
      rw [hsn.init]
      have := hmono₀ (mem_dom_self hs₀.lt) (hmaps ⟨le_rfl, ht.1⟩) (show τ < τ + h by linarith)
      rwa [hs₀.init] at this
    · have hmeet' : φ₀ (s + h) = φ n s := hmeet
      have hsn' : s ∈ Dom τ (T' n) := Icc_subset_dom htn ⟨hs.1.le, hs.2⟩
      have hsT : s ∈ Icc τ T := ⟨hs.1.le, hs.2.trans ht.2⟩
      have hc : φ n s ∈ Icc ξ X := by
        refine ⟨le_solution (hf n) (hpos n) hsn hsn', ?_⟩
        rw [← hmeet']
        exact (hmono₀.monotoneOn (hmaps ⟨hs.1.le, hs.2⟩) (hdom₀ _ ⟨by linarith, hTh.le⟩)
          (by linarith [hs.2, ht.2])).trans hTX.le
      have hdu : HasDerivWithinAt (fun u => φ₀ (u + h)) (f₀ (s + h) (φ₀ (s + h))) (Icc τ s) s := by
        have := (hs₀.deriv (s + h) (hmaps ⟨hs.1.le, hs.2⟩)).comp s
          ((hasDerivAt_id' s).add_const h).hasDerivWithinAt
          (hmaps.mono_left (Icc_subset_Icc_right hs.2))
        rwa [mul_one] at this
      refine ⟨_, _, hdu, (hsn.deriv s hsn').mono fun u hu => Icc_subset_dom htn
        ⟨hu.1, hu.2.trans hs.2⟩, ?_⟩
      rw [hmeet']
      have h1 := hn s hsT (φ n s) hc
      have h2 := hgap s hsT (φ n s) hc
      linarith [le_abs_self (f n s (φ n s) - f₀ s (φ n s))]
  -- so `φ_n` exists beyond `T`
  have hTn : (T : EReal) < T' n := by
    by_contra hle
    push Not at hle
    rcases (hφ n).maximal with htop | hnb
    · rw [htop] at hle; exact absurd hle (not_le.mpr (EReal.coe_lt_top T))
    · refine hnb ⟨max |ξ| |X|, ?_⟩
      rintro _ ⟨t, ht, rfl⟩
      have htT : t ≤ T := EReal.coe_le_coe_iff.mp (ht.2.le.trans hle)
      have h1 := le_solution (hf n) (hpos n) hsn ht
      have h2 := hupper t ⟨ht.1, htT⟩ ht
      have h3 : φ₀ (t + h) ≤ φ₀ (T + h) :=
        hmono₀.monotoneOn (hdom₀ _ ⟨by linarith [ht.1], by linarith⟩)
          (hdom₀ _ ⟨by linarith, hTh.le⟩) (by linarith)
      show |φ n t| ≤ max |ξ| |X|
      exact abs_le.mpr ⟨by linarith [neg_abs_le ξ, le_max_left |ξ| |X|],
        by linarith [le_abs_self X, le_max_right |ξ| |X|]⟩
  refine ⟨hTn, fun t ht => ?_⟩
  have htn : t ∈ Dom τ (T' n) := ⟨ht.1, (EReal.coe_le_coe_iff.mpr ht.2).trans_lt hTn⟩
  have hup := hupper t ht htn
  have hε₁ε : ε₁ ≤ ε := min_le_left _ _
  rw [abs_lt]
  refine ⟨?_, by linarith [hclose t ht]⟩
  rcases lt_or_ge t (τ + h) with htτ | htτ
  · -- near the start, `φ_n ≥ ξ = φ₀ (τ)` and `φ₀` has moved by less than `ε`
    have h1 := le_solution (hf n) (hpos n) hsn htn
    have := huc t ⟨ht.1, by linarith [ht.2]⟩ τ ⟨le_rfl, by linarith⟩
      (by rw [Real.dist_eq, abs_of_nonneg (by linarith [ht.1])]; linarith)
    rw [Real.dist_eq, hs₀.init] at this
    linarith [le_abs_self (φ₀ t - ξ)]
  · -- later, the lower bracket `φ₀ (t - h) < φ_n (t)`
    have hmaps : MapsTo (fun u => u - h) (Icc (τ + h) t) (Dom τ T₀) := fun u hu =>
      hdom₀ _ ⟨by linarith [hu.1], by linarith [hu.2, ht.2]⟩
    have hlower : φ₀ (t - h) < φ n t := by
      refine lt_of_first_meeting (u := φ n) (v := fun s => φ₀ (s - h)) htτ ((hsn.continuousOn.mono (Icc_subset_dom htn)).mono
        fun u hu => ⟨by linarith [hu.1], hu.2⟩)
        (hs₀.continuousOn.comp (continuous_id.sub continuous_const).continuousOn hmaps) ?_
        fun s hs hmeet => ?_
      · have := strictMonoOn_solution (hf n) (hpos n) hsn (mem_dom_self hsn.lt)
          (Icc_subset_dom htn ⟨by linarith, htτ⟩) (show τ < τ + h by linarith)
        rw [hsn.init] at this
        simpa [hs₀.init] using this
      · have hmeet' : φ n s = φ₀ (s - h) := hmeet
        have hsn' : s ∈ Dom τ (T' n) := Icc_subset_dom htn ⟨by linarith [hs.1], hs.2⟩
        have hsh : s - h ∈ Icc τ T := ⟨by linarith [hs.1], by linarith [hs.2, ht.2]⟩
        have hc : φ n s ∈ Icc ξ X := by
          refine ⟨le_solution (hf n) (hpos n) hsn hsn', ?_⟩
          rw [hmeet']
          exact (hmono₀.monotoneOn (hmaps ⟨hs.1.le, hs.2⟩)
            (hdom₀ _ ⟨hτT.le, hTr'.le⟩) hsh.2).trans hX.le
        have hdv : HasDerivWithinAt (fun u => φ₀ (u - h)) (f₀ (s - h) (φ₀ (s - h)))
            (Icc (τ + h) s) s := by
          have := (hs₀.deriv (s - h) (hmaps ⟨hs.1.le, hs.2⟩)).comp s
            ((hasDerivAt_id' s).sub_const h).hasDerivWithinAt
            (hmaps.mono_left (Icc_subset_Icc_right hs.2))
          rwa [mul_one] at this
        refine ⟨_, _, (hsn.deriv s hsn').mono fun u hu => Icc_subset_dom htn
          ⟨by linarith [hu.1], hu.2.trans hs.2⟩, hdv, ?_⟩
        rw [← hmeet']
        have h1 := hn s ⟨by linarith [hs.1], hs.2.trans ht.2⟩ (φ n s) hc
        have h2 := hgap (s - h) hsh (φ n s) hc
        rw [sub_add_cancel] at h2
        linarith [neg_abs_le (f n s (φ n s) - f₀ s (φ n s))]
    have := hclose (t - h) ⟨by linarith, by linarith [ht.2]⟩
    rw [sub_add_cancel] at this
    linarith

end PathwiseVolatility
