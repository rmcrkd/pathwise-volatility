/-
Copyright (c) 2026 Ryan McCrickerd. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCrickerd
-/
import PathwiseVolatility.Maximal
import PathwiseVolatility.Existence
import PathwiseVolatility.Dependence
import PathwiseVolatility.Zeros

/-!
# Section 3.1: simplifying the problem

Definitions 1.3 (the set `G`), 1.5 (the set `Φ`) and 1.6 (the set `Φ̄`), Problem 1.4, and
Theorem 3.3 (Well-posedness for Problem 1.4), parts 1 to 3.

Functions in `G` are defined on `ℝ₊²`; here they are functions on `ℝ²` of which only the values on
`ℝ₊²` matter. As in the thesis's proof of Theorem 3.3, each `g ∈ G` is extended to a function in `F`
with eq. (3.6), written as `f (t, x) = g (t⁺, x⁺) + g (0, x⁺) - g (t⁻, x⁺)`. The extension satisfies
the line condition of Theorem 3.1 at `(0, 0)`, so the results of Chapter 2 apply to it, and its
solutions from `(0, 0)` stay in `ℝ₊²`, where it agrees with `g`.
-/

open Set Filter Topology

namespace PathwiseVolatility

/-- Definition 1.3, the set `G`: `g` is continuous on `ℝ₊²`, `g (0, 0) ≥ 0`, each `g (·, x)` is
strictly increasing on `ℝ₊`, `inf_{x ≥ 0} g (t, x) < 0` for each `t ≥ 0`, and
`sup_{t ≥ 0} g (t, x) > 0` for each `x ≥ 0`. -/
structure InG (g : ℝ → ℝ → ℝ) : Prop where
  continuousOn : ContinuousOn (Function.uncurry g) (Ici 0 ×ˢ Ici 0)
  nonneg_zero : 0 ≤ g 0 0
  strictMonoOn : ∀ x, 0 ≤ x → StrictMonoOn (fun t => g t x) (Ici 0)
  exists_neg : ∀ t, 0 ≤ t → ∃ x, 0 ≤ x ∧ g t x < 0
  exists_pos : ∀ x, 0 ≤ x → ∃ t, 0 ≤ t ∧ 0 < g t x

/-- Problem 1.4: a global solution `φ ∈ C¹₀ (ℝ₊, ℝ₊)` of `x' = g (t, x)`, `x (0) = 0`. -/
structure IsGlobalSolution (g : ℝ → ℝ → ℝ) (φ : ℝ → ℝ) : Prop where
  init : φ 0 = 0
  nonneg : ∀ t, 0 ≤ t → 0 ≤ φ t
  deriv : ∀ t, 0 ≤ t → HasDerivWithinAt φ (g t (φ t)) (Ici 0) t

/-- Definition 1.5, the set `Φ`: the bijections of `ℝ₊` in `C¹₀ (ℝ₊, ℝ₊)`. -/
structure InΦ (φ : ℝ → ℝ) : Prop where
  init : φ 0 = 0
  bijOn : BijOn φ (Ici 0) (Ici 0)
  deriv : ∃ φ' : ℝ → ℝ, ContinuousOn φ' (Ici 0) ∧ ∀ t, 0 ≤ t → HasDerivWithinAt φ (φ' t) (Ici 0) t

/-- Definition 1.6, the set `Φ̄`: the strictly increasing, unbounded càdlàg paths in
`D (ℝ₊, ℝ₊)`. -/
structure InΦbar (φ : ℝ → ℝ) : Prop where
  nonneg : ∀ t, 0 ≤ t → 0 ≤ φ t
  strictMonoOn : StrictMonoOn φ (Ici 0)
  rightCont : ∀ t, 0 ≤ t → ContinuousWithinAt φ (Ici t) t
  leftLim : ∀ t, 0 < t → ∃ l, Tendsto φ (𝓝[<] t) (𝓝 l)
  unbounded : ¬ BddAbove (φ '' Ici 0)

/-- The extension of eq. (3.6), `f (t, x) = g (t⁺, x⁺) + g (0, x⁺) - g (t⁻, x⁺)`: it is `g (t, x⁺)`
for `t ≥ 0`, and `2 g (0, x⁺) - g (-t, x⁺)` for `t < 0`. -/
def extendG (g : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  g (max t 0) (max x 0) + g 0 (max x 0) - g (max (-t) 0) (max x 0)

variable {g : ℝ → ℝ → ℝ}

theorem dom_top (τ : ℝ) : Dom τ ⊤ = Ici τ := by
  ext t; exact ⟨fun h => h.1, fun h => ⟨h, EReal.coe_lt_top t⟩⟩

theorem extendG_of_nonneg {t x : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) : extendG g t x = g t x := by
  simp [extendG, max_eq_left ht, max_eq_left hx, max_eq_right (neg_nonpos.mpr ht)]

theorem InG.continuous_extendG (hg : InG g) : Continuous (Function.uncurry (extendG g)) := by
  have hpair : ∀ {a b : ℝ × ℝ → ℝ}, Continuous a → Continuous b → (∀ p, 0 ≤ a p) →
      (∀ p, 0 ≤ b p) → Continuous fun p => g (a p) (b p) := by
    intro a b ha hb ha0 hb0
    exact hg.continuousOn.comp_continuous (ha.prodMk hb) fun p => ⟨ha0 p, hb0 p⟩
  have hx : Continuous fun p : ℝ × ℝ => max p.2 0 := continuous_snd.max continuous_const
  exact ((hpair (continuous_fst.max continuous_const) hx (fun _ => le_max_right _ _)
    (fun _ => le_max_right _ _)).add (hpair continuous_const hx (fun _ => le_rfl)
    (fun _ => le_max_right _ _))).sub (hpair (continuous_fst.neg.max continuous_const) hx
    (fun _ => le_max_right _ _) (fun _ => le_max_right _ _))

/-- The extension is in `F`. -/
theorem InG.inF_extendG (hg : InG g) : InF (extendG g) := by
  refine ⟨hg.continuous_extendG, fun x s t hst => ?_, ?_⟩
  · have hm := hg.strictMonoOn (max x 0) (le_max_right _ _)
    simp only [extendG]
    rcases le_or_gt 0 s with hs | hs
    · have ht : 0 ≤ t := hs.trans hst.le
      rw [max_eq_left hs, max_eq_left ht, max_eq_right (neg_nonpos.mpr hs),
        max_eq_right (neg_nonpos.mpr ht)]
      have := hm (mem_Ici.mpr hs) (mem_Ici.mpr ht) hst
      simp only at this
      linarith
    · rcases le_or_gt t 0 with ht | ht
      · rw [max_eq_right hs.le, max_eq_right ht, max_eq_left (neg_nonneg.mpr hs.le),
          max_eq_left (neg_nonneg.mpr ht)]
        have := hm (mem_Ici.mpr (neg_nonneg.mpr ht)) (mem_Ici.mpr (neg_nonneg.mpr hs.le))
          (by linarith)
        simp only at this
        linarith
      · rw [max_eq_right hs.le, max_eq_left ht.le, max_eq_left (neg_nonneg.mpr hs.le),
          max_eq_right (neg_nonpos.mpr ht.le)]
        have h1 := hm (mem_Ici.mpr le_rfl) (mem_Ici.mpr (neg_nonneg.mpr hs.le)) (by linarith)
        have h2 := hm (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht.le) ht
        simp only at h1 h2
        linarith
  · obtain ⟨t, ht, hpos⟩ := hg.exists_pos 0 le_rfl
    exact ⟨t, 0, by rw [extendG_of_nonneg ht le_rfl]; exact hpos⟩

/-- The extension satisfies the line condition of Theorem 3.1 at `(0, 0)`, along `t = -x`. -/
theorem InG.lineCondition_extendG (hg : InG g) : LineCondition (extendG g) 0 0 := by
  refine ⟨1, 1, one_pos, fun x hx => ?_⟩
  have hx0 : 0 < x := hx.1
  have : extendG g (0 + 1 * x) (0 - x) = g x 0 := by
    simp only [extendG, zero_add, one_mul, zero_sub, max_eq_left hx0.le,
      max_eq_right (neg_nonpos.mpr hx0.le)]
    ring
  rw [this]
  have := hg.strictMonoOn 0 le_rfl (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx0.le) hx0
  simp only at this
  linarith [hg.nonneg_zero]

/-- A solution of the extended IVP from `(0, 0)` on `[0, ∞)` is a global solution of
Problem 1.4, and conversely. -/
theorem InG.isGlobalSolution_iff (hg : InG g) {φ : ℝ → ℝ} :
    IsGlobalSolution g φ ↔ IsSolution (extendG g) 0 0 ⊤ φ := by
  constructor
  · intro h
    refine ⟨EReal.coe_lt_top 0, h.init, fun t ht => ?_⟩
    rw [dom_top] at ht ⊢
    rw [extendG_of_nonneg ht (h.nonneg t ht)]
    exact h.deriv t ht
  · intro h
    have hnn : ∀ t, 0 ≤ t → 0 ≤ φ t := fun t ht =>
      le_solution hg.inF_extendG hg.lineCondition_extendG h (by rw [dom_top]; exact ht)
    refine ⟨h.init, hnn, fun t ht => ?_⟩
    have := h.deriv t (by rw [dom_top]; exact ht)
    rw [dom_top, extendG_of_nonneg ht (hnn t ht)] at this
    exact this

/-- Theorem 3.3 (Well-posedness for Problem 1.4), part 1: there is a global solution, strictly
increasing and unbounded, and it is the only one. -/
theorem InG.exists_unique_global (hg : InG g) :
    ∃ φ, IsGlobalSolution g φ ∧ StrictMonoOn φ (Ici 0) ∧ ¬ BddAbove (φ '' Ici 0) ∧
      ∀ ψ, IsGlobalSolution g ψ → EqOn ψ φ (Ici 0) := by
  have hf := hg.inF_extendG
  have hl := hg.lineCondition_extendG
  obtain ⟨T, φ, hφ⟩ := exists_maximal hf hl
  obtain ⟨hT, hub⟩ := spatio_temporal hf hl hφ
  have hT' : T = ⊤ := hT fun t ht => by
    obtain ⟨x, hx, hneg⟩ := hg.exists_neg t ht
    exact ⟨x, hx, by rw [extendG_of_nonneg ht hx]; exact hneg⟩
  subst hT'
  have hsol : IsGlobalSolution g φ := hg.isGlobalSolution_iff.mpr hφ.toIsSolution
  refine ⟨φ, hsol, ?_, ?_, fun ψ hψ => ?_⟩
  · simpa [dom_top] using strictMonoOn_solution hf hl hφ.toIsSolution
  · have := hub fun x hx => by
      obtain ⟨t, ht, hpos⟩ := hg.exists_pos x hx
      exact ⟨t, ht, by rw [extendG_of_nonneg ht hx]; exact hpos⟩
    simpa [dom_top] using this
  · have hψ' : IsMaximalSolution (extendG g) 0 0 ⊤ ψ :=
      ⟨hg.isGlobalSolution_iff.mp hψ, Or.inl rfl⟩
    simpa [dom_top] using (maximal_uniqueness hf hl hψ' hφ).2

/-- The upper bound of Theorem 3.3, part 2: `φ̄ (t) = inf {x > 0 : g (t, x) < 0}`. For `t ≥ 0` it is
the bound `φ̄` of the extension. -/
theorem upperBound_extendG {t : ℝ} (ht : 0 ≤ t) :
    upperBound (extendG g) 0 t = ⨅ x ∈ {x : ℝ | 0 < x ∧ g t x < 0}, (x : EReal) := by
  have h : {x : ℝ | 0 < x ∧ extendG g t x < 0} = {x : ℝ | 0 < x ∧ g t x < 0} := by
    ext x
    simp only [mem_ofPred_eq]
    exact ⟨fun h => ⟨h.1, by rw [← extendG_of_nonneg (g := g) ht h.1.le]; exact h.2⟩,
      fun h => ⟨h.1, by rw [extendG_of_nonneg ht h.1.le]; exact h.2⟩⟩
  rw [upperBound, h]

/-- Theorem 3.3, part 2: the global solution is bounded above by `φ̄`, which is finite,
strictly increasing and càdlàg on `ℝ₊`, and unbounded. -/
theorem InG.upper_bound (hg : InG g) {φ : ℝ → ℝ} (hφ : IsGlobalSolution g φ) :
    (∀ t, 0 ≤ t → (φ t : EReal) ≤ upperBound (extendG g) 0 t) ∧
    (∀ t, 0 ≤ t → upperBound (extendG g) 0 t < ⊤) ∧
    (∀ s t, 0 ≤ s → s < t → upperBound (extendG g) 0 s < upperBound (extendG g) 0 t) ∧
    (∀ t, ContinuousWithinAt (upperBound (extendG g) 0) (Ici t) t) ∧
    (∀ t, ∃ l, Tendsto (upperBound (extendG g) 0) (𝓝[<] t) (𝓝 l)) ∧
    ∀ M : ℝ, ∃ t, 0 ≤ t ∧ (M : EReal) < upperBound (extendG g) 0 t := by
  have hf := hg.inF_extendG
  have hs := hg.isGlobalSolution_iff.mp hφ
  have hle : ∀ t, 0 ≤ t → (φ t : EReal) ≤ upperBound (extendG g) 0 t := fun t ht =>
    solution_le_upperBound hf hs (by rw [dom_top]; exact ht)
  have hfin : ∀ t, 0 ≤ t → upperBound (extendG g) 0 t < ⊤ := fun t ht => by
    obtain ⟨x, hx, hneg⟩ := hg.exists_neg t ht
    refine upperBound_lt_top_iff.mpr ⟨x, lt_of_le_of_ne hx fun h => ?_, by
      rw [extendG_of_nonneg ht hx]; exact hneg⟩
    subst h
    have := hg.strictMonoOn 0 le_rfl (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht)
    rcases eq_or_lt_of_le ht with h | h
    · subst h; linarith [hg.nonneg_zero]
    · have := this h; simp only at this; linarith [hg.nonneg_zero]
  refine ⟨hle, hfin, fun s t hs hst => upperBound_lt hf ?_ hs hst (hfin t (hs.trans hst.le)),
    fun t => upperBound_continuousWithinAt hf t, fun t => upperBound_tendsto_left hf t, ?_⟩
  · rw [extendG_of_nonneg le_rfl le_rfl]; exact hg.nonneg_zero
  · -- `φ ≤ φ̄`, and `φ` is unbounded
    intro M
    obtain ⟨φ₀, -, -, hunb, huniq⟩ := hg.exists_unique_global
    obtain ⟨_, ⟨t, ht, rfl⟩, hMt⟩ := not_bddAbove_iff.mp hunb M
    rw [← huniq φ hφ ht] at hMt
    exact ⟨t, ht, (EReal.coe_lt_coe_iff.mpr hMt).trans_le (hle t ht)⟩

/-- Theorem 3.3, part 3 (Continuous dependence): if `g_n → g₀` uniformly on compacts of `ℝ₊²`,
the global solutions converge uniformly on compacts. -/
theorem InG.solution_continuous (hg : InG g) {G : ℕ → ℝ → ℝ → ℝ} (hG : ∀ n, InG (G n))
    {φ₀ : ℝ → ℝ} (hφ₀ : IsGlobalSolution g φ₀) {φ : ℕ → ℝ → ℝ}
    (hφ : ∀ n, IsGlobalSolution (G n) (φ n))
    (hconv : ∀ T X η, 0 < η → ∀ᶠ n in atTop, ∀ t ∈ Icc 0 T, ∀ x ∈ Icc 0 X,
      |G n t x - g t x| < η) {T : ℝ} (hT : 0 < T) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ t ∈ Icc 0 T, |φ n t - φ₀ t| < ε := by
  intro ε hε
  have h := solution_map_continuous hg.inF_extendG hg.lineCondition_extendG
    (⟨hg.isGlobalSolution_iff.mp hφ₀, Or.inl rfl⟩ : IsMaximalSolution (extendG g) 0 0 ⊤ φ₀)
    (fun n => (hG n).inF_extendG) (fun n => (hG n).lineCondition_extendG)
    (fun n => (⟨(hG n).isGlobalSolution_iff.mp (hφ n), Or.inl rfl⟩ :
      IsMaximalSolution (extendG (G n)) 0 0 ⊤ (φ n)))
    hT (EReal.coe_lt_top T) (lt_add_one (φ₀ T))
    (fun η hη => (hconv T (φ₀ T + 1) η hη).mono fun n hn t ht x hx => by
      rw [extendG_of_nonneg ht.1 hx.1, extendG_of_nonneg ht.1 hx.1]; exact hn t ht x hx)
    ε hε
  exact h.mono fun n hn => hn.2

end PathwiseVolatility
