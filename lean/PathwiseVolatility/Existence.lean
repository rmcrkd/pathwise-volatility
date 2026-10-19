/-
Copyright (c) 2026 Ryan McCrickerd. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCrickerd
-/
import PathwiseVolatility.Bounds

/-!
# Section 2.3: spatial existence

Lemma 2.10 (Spatial existence) and Corollary 2.11 (Spatio-temporal existence). In the thesis a
maximal solution is a bijection onto `[ξ, X_*)`; here `X_* > X` reads as `φ (t) > X` for some
`t`, and `X_* = ∞` as `φ` unbounded above. The thesis's condition `lim_{t → ∞} f (t, x) > 0`
reads as `f (t, x) > 0` for some `t`, which is the same since `f (·, x)` is increasing.
-/

open Set Filter Topology

namespace PathwiseVolatility

variable {f : ℝ → ℝ → ℝ} {τ ξ : ℝ} {T : EReal} {φ : ℝ → ℝ}

/-- Lemma 2.10 (Spatial existence): a maximal solution exceeds the level `X` exactly when
`f (·, x)` is positive at some time for every `x ∈ [ξ, X]`. -/
theorem exceeds_iff (hf : InF f) (hpos : LineCondition f τ ξ) (hφ : IsMaximalSolution f τ ξ T φ) (X : ℝ) :
    (∃ t ∈ Dom τ T, X < φ t) ↔ ∀ x ∈ Icc ξ X, ∃ s, 0 < f s x := by
  constructor
  · -- the solution passes through each level `x ∈ [ξ, X]`, where `f ≥ 0`
    rintro ⟨t, ht, hXt⟩ x hx
    obtain ⟨s, hs, hsx⟩ := intermediate_value_Icc ht.1
      (hφ.continuousOn.mono (Icc_subset_dom ht))
      (show x ∈ Icc (φ τ) (φ t) by rw [hφ.init]; exact ⟨hx.1, by linarith [hx.2]⟩)
    have h0 : 0 ≤ f s x := by
      have := nonneg_along hf hpos hφ.toIsSolution (Icc_subset_dom ht hs)
      rwa [hsx] at this
    have := hf.strictMono x (show s < s + 1 by linarith)
    simp only at this
    exact ⟨s + 1, by linarith⟩
  · intro h
    by_contra hno
    push Not at hno
    have hξX : ξ ≤ X := by
      have := hno τ (mem_dom_self hφ.lt); rwa [hφ.init] at this
    -- `φ` is bounded above, so `T = ∞`
    have hT : T = ⊤ := (maximal_unbounded hf hpos hφ).resolve_right
      fun hnb => hnb ⟨X, by rintro _ ⟨t, ht, rfl⟩; exact hno t ht⟩
    subst hT
    -- a single time `n` at which `f (n, ·) > 0` on `[ξ, X]`, by compactness
    obtain ⟨n, hn⟩ := isCompact_Icc.elim_directed_cover (fun n : ℕ => {x | 0 < f n x})
      (fun n => isOpen_lt continuous_const (hf.continuous_level n))
      (fun x hx => by
        obtain ⟨s, hs⟩ := h x hx
        obtain ⟨n, hn⟩ := exists_nat_ge s
        exact mem_iUnion.mpr ⟨n, lt_of_lt_of_le hs (hf.mono x hn)⟩)
      (fun i j => ⟨max i j,
        fun x (hx : 0 < f i x) => lt_of_lt_of_le hx (hf.mono x (by exact_mod_cast le_max_left i j)),
        fun x (hx : 0 < f j x) => lt_of_lt_of_le hx (hf.mono x (by exact_mod_cast le_max_right i j))⟩)
    obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hξX)
      (hf.continuous_level n).continuousOn
    set c := f n x₀ with hc
    have hcpos : 0 < c := hn hx₀
    -- from `t₀ = max τ n` on, `φ' ≥ c`, so `φ` grows past `X`
    set t₀ := max τ (n : ℝ) with ht₀
    have hdom : ∀ t, τ ≤ t → t ∈ Dom τ ⊤ := fun t ht => ⟨ht, EReal.coe_lt_top t⟩
    have hslope : ∀ t, t₀ ≤ t → c ≤ f t (φ t) := by
      intro t ht
      have hτt : τ ≤ t := (le_max_left _ _).trans ht
      have hφt : φ t ∈ Icc ξ X :=
        ⟨le_solution hf hpos hφ.toIsSolution (hdom t hτt), hno t (hdom t hτt)⟩
      exact (show c ≤ f n (φ t) from hmin hφt).trans (hf.mono (φ t) ((le_max_right _ _).trans ht))
    have hmono : MonotoneOn (fun u => φ u - u * c) (Ici t₀) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici t₀)
        (f' := fun u => f u (φ u) - c) ?_ ?_ ?_
      · exact (hφ.continuousOn.mono fun u hu => hdom u ((le_max_left _ _).trans hu)).sub
          (continuous_id.mul continuous_const).continuousOn
      · intro u hu
        rw [interior_Ici] at hu ⊢
        have hτu : τ ≤ u := (le_max_left _ _).trans hu.le
        exact ((hφ.deriv u (hdom u hτu)).mono fun v hv =>
          hdom v ((le_max_left _ _).trans (le_of_lt hv))).sub (hasDerivAt_mul_const c).hasDerivWithinAt
      · intro u hu
        rw [interior_Ici] at hu
        linarith [hslope u hu.le]
    set t₁ := t₀ + (X - ξ) / c + 1 with ht₁
    have ht₀₁ : t₀ ≤ t₁ := by
      have : 0 ≤ (X - ξ) / c := div_nonneg (by linarith) hcpos.le
      linarith
    have hstep := hmono (Set.mem_Ici.mpr le_rfl) ht₀₁ ht₀₁
    simp only at hstep
    have hφt₀ : ξ ≤ φ t₀ := le_solution hf hpos hφ.toIsSolution (hdom t₀ (le_max_left _ _))
    have hgrow : (t₁ - t₀) * c = X - ξ + c := by
      rw [ht₁, show t₀ + (X - ξ) / c + 1 - t₀ = (X - ξ) / c + 1 by ring, add_mul,
        div_mul_cancel₀ _ hcpos.ne', one_mul]
    have := hno t₁ (hdom t₁ ((le_max_left _ _).trans ht₀₁))
    linarith

/-- Lemma 2.10 (Spatial existence), for `X_* = ∞`: a maximal solution is unbounded above exactly
when `f (·, x)` is positive at some time for every `x ≥ ξ`. -/
theorem unbounded_iff (hf : InF f) (hpos : LineCondition f τ ξ) (hφ : IsMaximalSolution f τ ξ T φ) :
    ¬ BddAbove (φ '' Dom τ T) ↔ ∀ x, ξ ≤ x → ∃ s, 0 < f s x := by
  constructor
  · intro hnb x hx
    obtain ⟨_, ⟨t, ht, rfl⟩, hxt⟩ := not_bddAbove_iff.mp hnb x
    exact (exceeds_iff hf hpos hφ x).mp ⟨t, ht, hxt⟩ x ⟨hx, le_rfl⟩
  · intro h
    refine not_bddAbove_iff.mpr fun X => ?_
    obtain ⟨t, ht, hXt⟩ := (exceeds_iff hf hpos hφ X).mpr fun x hx => h x hx.1
    exact ⟨φ t, mem_image_of_mem φ ht, hXt⟩

/-- Corollary 2.11 (Spatio-temporal existence): `inf_{x ≥ ξ} f (t, x) < 0` for every `t ≥ τ`
gives `T_* = ∞`, and `sup_{t ≥ τ} f (t, x) > 0` for every `x ≥ ξ` gives `X_* = ∞`. -/
theorem spatio_temporal (hf : InF f) (hpos : LineCondition f τ ξ) (hφ : IsMaximalSolution f τ ξ T φ) :
    ((∀ t, τ ≤ t → ∃ x, ξ ≤ x ∧ f t x < 0) → T = ⊤) ∧
      ((∀ x, ξ ≤ x → ∃ t, τ ≤ t ∧ 0 < f t x) → ¬ BddAbove (φ '' Dom τ T)) :=
  ⟨eq_top_of_neg hf hpos hφ, fun h => (unbounded_iff hf hpos hφ).mpr fun x hx =>
    let ⟨t, _, ht⟩ := h x hx; ⟨t, ht⟩⟩

end PathwiseVolatility
