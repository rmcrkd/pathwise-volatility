/-
Copyright (c) 2026 Ryan McCrickerd. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCrickerd
-/
import PathwiseVolatility.Peano
import PathwiseVolatility.Uniqueness

/-!
# Maximal existence: Theorems 2.8 and 2.17, Corollary 2.1

The existence of a maximal solution, which the thesis takes from classical theory (Theorem 1.1.3
of Lakshmikantham and Leela). Here it is proved from Peano's theorem and the uniqueness of
Section 2.4: `T_*` is the supremum of the ends of all solutions, which agree wherever they
overlap, and the maximal solution is their common value. If it ended at a finite `T_*` while
bounded, Peano's theorem, with an interval length uniform over the bounded region, would extend
it past `T_*`.
-/

open Set Filter Topology

namespace PathwiseVolatility

variable {f : ℝ → ℝ → ℝ} {τ ξ : ℝ}

/-- Peano's theorem with an interval length uniform over starting points in a bounded region. -/
theorem peano_uniform (hc : Continuous (Function.uncurry f)) (τ T₀ B : ℝ) :
    ∃ a > 0, ∀ s ∈ Icc τ T₀, ∀ x ∈ Icc (-B) B, ∃ χ : ℝ → ℝ, χ s = x ∧
      ∀ t ∈ Icc s (s + a), HasDerivWithinAt χ (f t (χ t)) (Icc s (s + a)) t := by
  have hK : IsCompact (Icc τ (T₀ + 1) ×ˢ Icc (-B - 1) (B + 1)) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  set M := max C 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  refine ⟨1 / (M + 1), by positivity, fun s hs x hx => ?_⟩
  have ha1 : 1 / (M + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  obtain ⟨χ, hχ0, -, hχ⟩ := peano_exists (s := s) (x := x) (a := 1 / (M + 1)) (r := 1) (M := M)
    hc (by positivity) zero_le_one
    (fun t ht y hy => by
      have := hC (t, y) (mem_prod.mpr ⟨⟨hs.1.trans ht.1, by linarith [ht.2, hs.2]⟩,
        ⟨by linarith [hx.1, hy.1], by linarith [hx.2, hy.2]⟩⟩)
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _))
    (by rw [mul_one_div, div_le_one (by positivity)]; linarith)
  exact ⟨χ, hχ0, hχ⟩

/-- Some solution exists. -/
theorem exists_solution (hc : Continuous (Function.uncurry f)) (τ ξ : ℝ) :
    ∃ T : ℝ, τ < T ∧ ∃ φ, IsSolution f τ ξ T φ := by
  obtain ⟨a, ha, h⟩ := peano_uniform hc τ τ (|ξ|)
  obtain ⟨χ, hχ0, hχ⟩ := h τ ⟨le_rfl, le_rfl⟩ ξ ⟨neg_abs_le ξ, le_abs_self ξ⟩
  have hsub : Dom τ (τ + a : ℝ) ⊆ Icc τ (τ + a) := fun u hu =>
    ⟨hu.1, (EReal.coe_lt_coe_iff.mp hu.2).le⟩
  exact ⟨τ + a, by linarith, χ, EReal.coe_lt_coe_iff.mpr (by linarith), hχ0,
    fun t ht => (hχ t (hsub ht)).mono hsub⟩

/-- The value at `t` of any solution defined there, or `ξ` if there is none. -/
noncomputable def maxSol (f : ℝ → ℝ → ℝ) (τ ξ t : ℝ) : ℝ :=
  open Classical in
  if h : ∃ T φ, IsSolution f τ ξ T φ ∧ t ∈ Dom τ T then
    (Classical.choose (Classical.choose_spec h)) t
  else ξ

/-- `maxSol` agrees with every solution, by uniqueness. -/
theorem maxSol_eq (hf : InF f) (hpos : LineCondition f τ ξ) {T : EReal} {ψ : ℝ → ℝ}
    (hψ : IsSolution f τ ξ T ψ) {t : ℝ} (ht : t ∈ Dom τ T) : maxSol f τ ξ t = ψ t := by
  have h : ∃ T φ, IsSolution f τ ξ T φ ∧ t ∈ Dom τ T := ⟨T, ψ, hψ, ht⟩
  rw [maxSol]
  split_ifs
  obtain ⟨hs, hts⟩ := Classical.choose_spec (Classical.choose_spec h)
  exact solutions_eqOn hf hpos hs hψ ⟨hts, ht⟩

/-- The supremum of the ends of all solutions. -/
noncomputable def maxEnd (f : ℝ → ℝ → ℝ) (τ ξ : ℝ) : EReal :=
  sSup {T : EReal | ∃ φ, IsSolution f τ ξ T φ}

theorem le_maxEnd {T : EReal} {φ : ℝ → ℝ} (hφ : IsSolution f τ ξ T φ) : T ≤ maxEnd f τ ξ :=
  le_sSup ⟨φ, hφ⟩

/-- `maxSol` is a solution on `[τ, maxEnd)`. -/
theorem maxSol_isSolution (hf : InF f) (hpos : LineCondition f τ ξ) :
    IsSolution f τ ξ (maxEnd f τ ξ) (maxSol f τ ξ) := by
  obtain ⟨T₀, hτT₀, φ₀, hφ₀⟩ := exists_solution hf.continuous τ ξ
  refine ⟨(EReal.coe_lt_coe_iff.mpr hτT₀).trans_le (le_maxEnd hφ₀), ?_, fun t ht => ?_⟩
  · rw [maxSol_eq hf hpos hφ₀ (mem_dom_self hφ₀.lt), hφ₀.init]
  · obtain ⟨T, ⟨ψ, hψ⟩, htT⟩ := lt_sSup_iff.mp ht.2
    have htψ : t ∈ Dom τ T := ⟨ht.1, htT⟩
    have hmem : Dom τ T ∈ 𝓝[Dom τ (maxEnd f τ ξ)] t :=
      mem_nhdsWithin.mpr ⟨{u | (u : EReal) < T}, isOpen_lt continuous_coe_real_ereal
        continuous_const, htT, fun u hu => ⟨hu.2.1, hu.1⟩⟩
    have hd := (hψ.deriv t htψ).mono_of_mem_nhdsWithin hmem
    rw [maxSol_eq hf hpos hψ htψ]
    exact hd.congr_of_eventuallyEq (by
      filter_upwards [hmem] with u hu using maxSol_eq hf hpos hψ hu) (maxSol_eq hf hpos hψ htψ)

/-- `maxSol` is a maximal solution: if it ended at a finite time while bounded, a solution
from a point just before that time would carry it beyond. -/
theorem maxSol_isMaximal (hf : InF f) (hpos : LineCondition f τ ξ) :
    IsMaximalSolution f τ ξ (maxEnd f τ ξ) (maxSol f τ ξ) := by
  have hsol := maxSol_isSolution hf hpos
  refine ⟨hsol, ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hT, ⟨B, hB⟩⟩ := hcon
  set T₀ := (maxEnd f τ ξ).toReal with hT₀
  have hr : (T₀ : EReal) = maxEnd f τ ξ := EReal.coe_toReal hT (ne_bot_of_gt hsol.lt)
  have hτT₀ : τ < T₀ := by
    have := hsol.lt; rw [← hr] at this; exact EReal.coe_lt_coe_iff.mp this
  have hdom : ∀ u, τ ≤ u → u < T₀ → u ∈ Dom τ (maxEnd f τ ξ) := fun u h1 h2 =>
    ⟨h1, by rw [← hr]; exact EReal.coe_lt_coe_iff.mpr h2⟩
  obtain ⟨a, ha, hpeano⟩ := peano_uniform hf.continuous τ T₀ B
  set s := max τ (T₀ - a / 2) with hs
  have hτs : τ ≤ s := le_max_left _ _
  have hsT₀ : s < T₀ := max_lt hτT₀ (by linarith)
  have hxB : maxSol f τ ξ s ∈ Icc (-B) B := by
    have := hB ⟨s, hdom s hτs hsT₀, rfl⟩
    exact ⟨by linarith [neg_abs_le (maxSol f τ ξ s)], by linarith [le_abs_self (maxSol f τ ξ s)]⟩
  obtain ⟨χ, hχ0, hχ⟩ := hpeano s ⟨hτs, hsT₀.le⟩ _ hxB
  -- glue `maxSol` on `[τ, s]` to `χ` on `[s, s + a]`
  set ψ : ℝ → ℝ := fun u => if u ≤ s then maxSol f τ ξ u else χ u with hψ
  have hψl : ∀ u ∈ Icc τ s, ψ u = maxSol f τ ξ u := fun u hu => by simp [hψ, hu.2]
  have hψr : ∀ u ∈ Icc s (s + a), ψ u = χ u := fun u hu => by
    rcases eq_or_lt_of_le hu.1 with h | h
    · rw [← h]; simp [hψ, hχ0]
    · simp [hψ, not_le.mpr h]
  have hext : IsSolution f τ ξ (s + a : ℝ) ψ := by
    refine ⟨EReal.coe_lt_coe_iff.mpr (by linarith), by simp [hψ, hτs, hsol.init], fun u hu => ?_⟩
    have hua : u < s + a := EReal.coe_lt_coe_iff.mp hu.2
    have h1 : HasDerivWithinAt ψ (f u (ψ u)) (Icc τ s) u := by
      by_cases hus : u ≤ s
      · rw [hψl u ⟨hu.1, hus⟩]
        exact ((hsol.deriv u (hdom u hu.1 (hus.trans_lt hsT₀))).mono fun v hv =>
          hdom v hv.1 (hv.2.trans_lt hsT₀)).congr_of_mem hψl ⟨hu.1, hus⟩
      · exact HasFDerivWithinAt.of_notMem_closure (by
          rw [closure_Icc]; exact fun h => hus h.2)
    have h2 : HasDerivWithinAt ψ (f u (ψ u)) (Icc s (s + a)) u := by
      by_cases hsu : s ≤ u
      · rw [hψr u ⟨hsu, hua.le⟩]
        exact (hχ u ⟨hsu, hua.le⟩).congr_of_mem hψr ⟨hsu, hua.le⟩
      · exact HasFDerivWithinAt.of_notMem_closure (by
          rw [closure_Icc]; exact fun h => hsu h.1)
    exact (h1.union h2).mono fun v hv => by
      rcases le_total v s with h | h
      · exact Or.inl ⟨hv.1, h⟩
      · exact Or.inr ⟨h, (EReal.coe_lt_coe_iff.mp hv.2).le⟩
  have := le_maxEnd hext
  rw [← hr, EReal.coe_le_coe_iff] at this
  linarith [le_max_right τ (T₀ - a / 2)]

/-- Theorem 2.8 (Maximal existence and bijectivity), existence: there is a maximal solution. -/
theorem exists_maximal (hf : InF f) (hpos : LineCondition f τ ξ) :
    ∃ T φ, IsMaximalSolution f τ ξ T φ :=
  ⟨_, _, maxSol_isMaximal hf hpos⟩

/-- Theorem 2.17 (Maximal uniqueness), in full, and Corollary 2.1: there is precisely one
maximal solution, it is strictly increasing, and it has `T_* = ∞` or is unbounded above. -/
theorem maximal_existence_uniqueness (hf : InF f) (hpos : LineCondition f τ ξ) :
    ∃ T φ, IsMaximalSolution f τ ξ T φ ∧ StrictMonoOn φ (Dom τ T) ∧
      (T = ⊤ ∨ ¬ BddAbove (φ '' Dom τ T)) ∧
      ∀ T' φ', IsMaximalSolution f τ ξ T' φ' → T' = T ∧ EqOn φ' φ (Dom τ T) := by
  obtain ⟨T, φ, hφ⟩ := exists_maximal hf hpos
  refine ⟨T, φ, hφ, strictMonoOn_solution hf hpos hφ.toIsSolution,
    maximal_unbounded hf hpos hφ, fun T' φ' hφ' => ?_⟩
  obtain ⟨hT, heq⟩ := maximal_uniqueness hf hpos hφ' hφ
  exact ⟨hT, hT ▸ heq⟩

end PathwiseVolatility
