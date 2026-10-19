/-
Copyright (c) 2026 Ryan McCrickerd. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCrickerd
-/
import PathwiseVolatility.Global
import PathwiseVolatility.Inverse

/-!
# Section 3.2: the problem's solution map

Theorem 3.4 (The solution set), Corollary 3.5 (Solution map surjectivity), Theorem 3.6 (Solution
map bijectivity) and Corollary 3.7.

A path `φ ∈ Φ` comes with its derivative `φ'`, continuous on `ℝ₊`; statements take it as a
separate function with `HasDerivWithinAt φ (φ' t) (Ici 0) t`.
-/

open Set Filter Topology

namespace PathwiseVolatility

variable {g : ℝ → ℝ → ℝ} {φ φ' ϑ : ℝ → ℝ}

/-- The derivative of a function non-decreasing on `ℝ₊` is non-negative there. -/
theorem deriv_nonneg_of_monotoneOn (hm : MonotoneOn φ (Ici 0)) {t d : ℝ} (ht : 0 ≤ t)
    (hd : HasDerivWithinAt φ d (Ici 0) t) : 0 ≤ d := by
  refine nonneg_of_slope hd ?_ fun u hu hne => ?_
  · have h' : Ioi t ⊆ Ici 0 \ {t} := fun u hu => ⟨mem_Ici.mpr (ht.trans hu.le), ne_of_gt hu⟩
    exact closure_mono h' (by rw [closure_Ioi]; exact mem_Ici.mpr le_rfl)
  · rw [slope_def_field]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact div_nonneg_of_nonpos (by linarith [hm hu (mem_Ici.mpr ht) hlt.le]) (by linarith)
    · exact div_nonneg (by linarith [hm (mem_Ici.mpr ht) hu hgt.le]) (by linarith)

/-- A path with derivative `φ'` on `ℝ₊` is continuous there. -/
theorem continuousOn_of_deriv (hd : ∀ t, 0 ≤ t → HasDerivWithinAt φ (φ' t) (Ici 0) t) :
    ContinuousOn φ (Ici 0) :=
  fun t ht => (hd t ht).continuousWithinAt

theorem InΦ.strictMonoOn (hφ : InΦ φ) : StrictMonoOn φ (Ici 0) := by
  obtain ⟨φ', -, hd⟩ := hφ.deriv
  exact strictMonoOn_of_bijOn hφ.bijOn (continuousOn_of_deriv hd) hφ.init

/-- Theorem 3.4 (The solution set), first part: every global solution of Problem 1.4 is in `Φ`. -/
theorem InG.mem_Φ (hg : InG g) {φ : ℝ → ℝ} (hφ : IsGlobalSolution g φ) : InΦ φ := by
  obtain ⟨φ₀, -, hmono, hunb, huniq⟩ := hg.exists_unique_global
  have heq : EqOn φ φ₀ (Ici 0) := huniq φ hφ
  have hm : StrictMonoOn φ (Ici 0) := fun s hs t ht hst => by
    rw [heq hs, heq ht]; exact hmono hs ht hst
  have hcont : ContinuousOn φ (Ici 0) := continuousOn_of_deriv hφ.deriv
  refine ⟨hφ.init, ⟨fun t ht => hφ.nonneg t ht, hm.injOn, fun x hx => ?_⟩,
    ⟨fun t => g t (φ t), ?_, hφ.deriv⟩⟩
  · -- `φ` is continuous and unbounded, so it reaches every level
    have hunb' : ¬ BddAbove (φ '' Ici 0) := by
      rintro ⟨B, hB⟩
      exact hunb ⟨B, by rintro _ ⟨t, ht, rfl⟩; rw [← heq ht]; exact hB ⟨t, ht, rfl⟩⟩
    obtain ⟨_, ⟨T, hT, rfl⟩, hxT⟩ := not_bddAbove_iff.mp hunb' x
    obtain ⟨t, ht, htx⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ T from hT)
      (hcont.mono Icc_subset_Ici_self) ⟨by rw [hφ.init]; exact hx, hxT.le⟩
    exact ⟨t, ht.1, htx⟩
  · exact hg.continuousOn.comp (continuousOn_id.prodMk hcont) fun t ht => ⟨ht, hφ.nonneg t ht⟩

/-- The function of eq. (3.10), `g (t, x) = φ' (φ⁻¹ (x)) + ϑ (t) - ϑ (φ⁻¹ (x))`. -/
noncomputable def gOfPath (φ φ' ϑ : ℝ → ℝ) (t x : ℝ) : ℝ :=
  φ' (invPath φ x) + ϑ t - ϑ (invPath φ x)

/-- Theorem 3.4, second part: each `φ ∈ Φ` solves `x' = g (t, x)`, `x (0) = 0` for the `g` of
eq. (3.10), whatever `ϑ`. -/
theorem solves_gOfPath (hφ : InΦ φ) (hd : ∀ t, 0 ≤ t → HasDerivWithinAt φ (φ' t) (Ici 0) t)
    (ϑ : ℝ → ℝ) : IsGlobalSolution (gOfPath φ φ' ϑ) φ := by
  refine ⟨hφ.init, fun t ht => hφ.bijOn.mapsTo ht, fun t ht => ?_⟩
  have : gOfPath φ φ' ϑ t (φ t) = φ' t := by
    simp only [gOfPath, invPath_apply hφ.bijOn ht]; ring
  rw [this]
  exact hd t ht

/-- Theorem 3.4, third part: if `ϑ` is continuous and strictly increasing with
`sup_{t ≥ 0} ϑ (t) - φ' (t) = ∞`, then the `g` of eq. (3.10) is in `G`, so `φ` is its unique
global solution. -/
theorem gOfPath_mem_G (hφ : InΦ φ) (hd : ∀ t, 0 ≤ t → HasDerivWithinAt φ (φ' t) (Ici 0) t)
    (hφ'c : ContinuousOn φ' (Ici 0)) (hϑc : ContinuousOn ϑ (Ici 0))
    (hϑm : StrictMonoOn ϑ (Ici 0)) (hsup : ∀ M, ∃ t, 0 ≤ t ∧ M < ϑ t - φ' t) :
    InG (gOfPath φ φ' ϑ) := by
  have hm := hφ.strictMonoOn
  have hψc := continuousOn_invPath hφ.bijOn hm hφ.init
  have hφ'nn : ∀ t, 0 ≤ t → 0 ≤ φ' t := fun t ht =>
    deriv_nonneg_of_monotoneOn hm.monotoneOn ht (hd t ht)
  have hψ2 : ContinuousOn (fun p : ℝ × ℝ => invPath φ p.2) (Ici 0 ×ˢ Ici 0) :=
    hψc.comp continuous_snd.continuousOn fun p hp => hp.2
  have hmapsψ : MapsTo (fun p : ℝ × ℝ => invPath φ p.2) (Ici 0 ×ˢ Ici 0) (Ici 0) :=
    fun p hp => invPath_nonneg hφ.bijOn hp.2
  refine ⟨?_, ?_, fun x _ s hs t ht hst => ?_, fun t _ => ?_, fun x hx => ?_⟩
  · show ContinuousOn (fun p : ℝ × ℝ => φ' (invPath φ p.2) + ϑ p.1 - ϑ (invPath φ p.2)) _
    exact ((hφ'c.comp hψ2 hmapsψ).add (hϑc.comp continuous_fst.continuousOn fun p hp => hp.1)).sub
      (hϑc.comp hψ2 hmapsψ)
  · simp only [gOfPath, invPath_zero hφ.bijOn hφ.init]
    linarith [hφ'nn 0 le_rfl]
  · simp only [gOfPath]
    linarith [hϑm hs ht hst]
  · obtain ⟨s, hs, hMs⟩ := hsup (ϑ t)
    refine ⟨φ s, hφ.bijOn.mapsTo hs, ?_⟩
    simp only [gOfPath, invPath_apply hφ.bijOn hs]
    linarith
  · obtain ⟨s, hs, hMs⟩ := hsup (ϑ (invPath φ x) - φ' (invPath φ x))
    refine ⟨s, hs, ?_⟩
    simp only [gOfPath]
    linarith [hφ'nn s hs]

/-- Theorem 3.4 (The solution set): the global solution set of Problem 1.4 is `Φ`. Every global
solution is in `Φ`, and every `φ ∈ Φ` is the unique global solution for the `g ∈ G` of eq. (3.10),
given such a `ϑ`. -/
theorem solution_set :
    (∀ g, InG g → ∀ φ, IsGlobalSolution g φ → InΦ φ) ∧
    (∀ φ φ', InΦ φ → (∀ t, 0 ≤ t → HasDerivWithinAt φ (φ' t) (Ici 0) t) →
      ∀ ϑ, IsGlobalSolution (gOfPath φ φ' ϑ) φ) ∧
    (∀ φ φ' ϑ, InΦ φ → (∀ t, 0 ≤ t → HasDerivWithinAt φ (φ' t) (Ici 0) t) →
      ContinuousOn φ' (Ici 0) → ContinuousOn ϑ (Ici 0) → StrictMonoOn ϑ (Ici 0) →
      (∀ M, ∃ t, 0 ≤ t ∧ M < ϑ t - φ' t) →
      InG (gOfPath φ φ' ϑ) ∧ ∀ ψ, IsGlobalSolution (gOfPath φ φ' ϑ) ψ → EqOn ψ φ (Ici 0)) := by
  refine ⟨fun g hg φ hφ => hg.mem_Φ hφ, fun φ φ' hφ hd ϑ => solves_gOfPath hφ hd ϑ,
    fun φ φ' ϑ hφ hd hφ'c hϑc hϑm hsup => ?_⟩
  have hG := gOfPath_mem_G hφ hd hφ'c hϑc hϑm hsup
  refine ⟨hG, fun ψ hψ => ?_⟩
  obtain ⟨φ₀, -, -, -, huniq⟩ := hG.exists_unique_global
  intro t ht
  rw [huniq ψ hψ ht, huniq φ (solves_gOfPath hφ hd ϑ) ht]

/-! ### Corollary 3.5 -/

/-- The running maximum `t ↦ max_{[0, t]} p`. -/
noncomputable def runMax (p : ℝ → ℝ) (t : ℝ) : ℝ := sSup (p '' Icc 0 t)

variable {p : ℝ → ℝ}

theorem le_runMax (hp : ContinuousOn p (Ici 0)) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    p s ≤ runMax p t :=
  le_csSup (isCompact_Icc.image_of_continuousOn (hp.mono Icc_subset_Ici_self)).bddAbove
    ⟨s, ⟨hs, hst⟩, rfl⟩

theorem runMax_le {t M : ℝ} (ht : 0 ≤ t) (h : ∀ s ∈ Icc 0 t, p s ≤ M) : runMax p t ≤ M :=
  csSup_le ⟨p 0, 0, ⟨le_rfl, ht⟩, rfl⟩ (by rintro _ ⟨s, hs, rfl⟩; exact h s hs)

theorem runMax_mono (hp : ContinuousOn p (Ici 0)) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    runMax p s ≤ runMax p t :=
  runMax_le hs fun _ hu => le_runMax hp hu.1 (hu.2.trans hst)

theorem runMax_zero (hp : ContinuousOn p (Ici 0)) : runMax p 0 = p 0 :=
  le_antisymm (runMax_le le_rfl fun s hs => by rw [le_antisymm hs.2 hs.1]) (le_runMax hp le_rfl le_rfl)

/-- The running maximum of a function continuous on `ℝ₊` is continuous on `ℝ₊`: over a short time
it rises by at most the oscillation of the function. -/
theorem continuousOn_runMax (hp : ContinuousOn p (Ici 0)) : ContinuousOn (runMax p) (Ici 0) := by
  intro t ht
  have ht' : (0 : ℝ) ≤ t := ht
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, huc⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous
      (hp.mono (Icc_subset_Ici_self : Icc (0 : ℝ) (t + 1) ⊆ Ici 0)))
    (ε / 2) (by linarith)
  refine ⟨min δ 1, lt_min hδ one_pos, fun s hs hst => ?_⟩
  have hs' : (0 : ℝ) ≤ s := hs
  rw [Real.dist_eq] at hst ⊢
  have hδ' := min_le_left δ 1
  have h1' := min_le_right δ 1
  -- from `a` to `b ≥ a` close by, the running maximum rises by at most `ε / 2`
  have key : ∀ a b, 0 ≤ a → a ≤ b → b ≤ t + 1 → b - a < min δ 1 →
      runMax p b ≤ runMax p a + ε / 2 := by
    intro a b ha hab hb hba
    refine runMax_le (ha.trans hab) fun u hu => ?_
    rcases le_total u a with hua | hua
    · linarith [le_runMax hp hu.1 hua]
    · have := huc u ⟨hu.1, hu.2.trans hb⟩ a ⟨ha, by linarith⟩
        (by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith [hu.2])
      rw [Real.dist_eq] at this
      linarith [le_runMax hp ha le_rfl, le_abs_self (p u - p a)]
  rcases le_total t s with hts | hst'
  · have h1 := key t s ht' hts (by linarith [abs_lt.mp hst]) (by linarith [abs_lt.mp hst])
    have h2 := runMax_mono hp ht' hts
    rw [abs_lt]; constructor <;> linarith
  · have h1 := key s t hs' hst' (by linarith) (by linarith [abs_lt.mp hst])
    have h2 := runMax_mono hp hs' hst'
    rw [abs_lt]; constructor <;> linarith

/-- Corollary 3.5 (Solution map surjectivity): every `φ ∈ Φ` is the global solution for two
different functions in `G`, so the solution map from `G` to `Φ` is surjective and not injective.
They are the functions of eq. (3.10) with `ϑ (t) = a t + max_{[0, t]} φ' - φ' (0)`, for `a = 1, 2`,
as after Theorem 3.4. -/
theorem solution_map_surjective (hφ : InΦ φ) :
    ∃ g₁ g₂, InG g₁ ∧ InG g₂ ∧ IsGlobalSolution g₁ φ ∧ IsGlobalSolution g₂ φ ∧ g₁ 1 0 ≠ g₂ 1 0 := by
  obtain ⟨φ', hφ'c, hd⟩ := hφ.deriv
  have hRc := continuousOn_runMax hφ'c
  set ϑ : ℝ → ℝ → ℝ := fun a t => a * t + runMax φ' t - φ' 0 with hϑ
  have hϑc : ∀ a, ContinuousOn (ϑ a) (Ici 0) := fun a =>
    ((continuousOn_const.mul continuousOn_id).add hRc).sub continuousOn_const
  have hϑm : ∀ a, 0 < a → StrictMonoOn (ϑ a) (Ici 0) := fun a ha s hs t ht hst => by
    simp only [hϑ]
    nlinarith [runMax_mono hφ'c hs hst.le]
  have hsup : ∀ a, 1 ≤ a → ∀ M, ∃ t, 0 ≤ t ∧ M < ϑ a t - φ' t := fun a ha M => by
    refine ⟨max (M + φ' 0 + 1) 0, le_max_right _ _, ?_⟩
    simp only [hϑ]
    have := le_runMax hφ'c (le_max_right (M + φ' 0 + 1) 0) le_rfl
    nlinarith [le_max_left (M + φ' 0 + 1) 0, le_max_right (M + φ' 0 + 1) 0]
  refine ⟨gOfPath φ φ' (ϑ 1), gOfPath φ φ' (ϑ 2),
    gOfPath_mem_G hφ hd hφ'c (hϑc 1) (hϑm 1 one_pos) (hsup 1 le_rfl),
    gOfPath_mem_G hφ hd hφ'c (hϑc 2) (hϑm 2 two_pos) (hsup 2 one_le_two),
    solves_gOfPath hφ hd _, solves_gOfPath hφ hd _, ?_⟩
  simp only [gOfPath, hϑ, invPath_zero hφ.bijOn hφ.init]
  intro h
  linarith

/-! ### Theorem 3.6 and Corollary 3.7 -/

/-- The paths `w` of Theorem 3.6: continuous on `ℝ₊`, with `w (0) ≤ 0` and `sup_{x ≥ 0} w (x) = ∞`. -/
structure InW (w : ℝ → ℝ) : Prop where
  continuousOn : ContinuousOn w (Ici 0)
  nonpos_zero : w 0 ≤ 0
  unbounded : ∀ M, ∃ x, 0 ≤ x ∧ M < w x

/-- The paths `ϑ` of Theorem 3.6: continuous and strictly increasing on `ℝ₊`, with `ϑ (0) = 0` and
`ϑ (t) → ∞`. -/
structure InΘ (ϑ : ℝ → ℝ) : Prop where
  continuousOn : ContinuousOn ϑ (Ici 0)
  strictMonoOn : StrictMonoOn ϑ (Ici 0)
  zero : ϑ 0 = 0
  unbounded : ∀ M, ∃ t, 0 ≤ t ∧ M < ϑ t

/-- The set `Φ_ϑ` of Theorem 3.6: paths `φ ∈ Φ`, with derivative `φ'`, such that
`sup_{t ≥ 0} ϑ (t) - φ' (t) = ∞`. -/
def InΦϑ (ϑ φ φ' : ℝ → ℝ) : Prop :=
  InΦ φ ∧ (∀ t, 0 ≤ t → HasDerivWithinAt φ (φ' t) (Ici 0) t) ∧ ContinuousOn φ' (Ici 0) ∧
    ∀ M, ∃ t, 0 ≤ t ∧ M < ϑ t - φ' t

variable {w : ℝ → ℝ}

/-- In Theorem 3.6, `g (t, x) = ϑ (t) - w (x)` is in `G`: the subset `G_ϑ ⊂ G`. -/
theorem InW.inG (hϑ : InΘ ϑ) (hw : InW w) : InG (fun t x => ϑ t - w x) := by
  refine ⟨(hϑ.continuousOn.comp continuous_fst.continuousOn fun p hp => hp.1).sub
    (hw.continuousOn.comp continuous_snd.continuousOn fun p hp => hp.2), ?_,
    fun x _ s hs t ht hst => ?_, fun t _ => ?_, fun x _ => ?_⟩
  · simp only [hϑ.zero]; linarith [hw.nonpos_zero]
  · simp only; linarith [hϑ.strictMonoOn hs ht hst]
  · obtain ⟨x, hx, hMx⟩ := hw.unbounded (ϑ t)
    exact ⟨x, hx, by linarith⟩
  · obtain ⟨t, ht, hMt⟩ := hϑ.unbounded (w x)
    exact ⟨t, ht, by linarith⟩

/-- Theorem 3.6 and Corollary 3.7 (Solution map bijectivity), into `Φ_ϑ`: the global solution for
`ϑ (t) - w (x)` is in `Φ_ϑ`, with derivative `ϑ (t) - w (φ (t))`. -/
theorem InW.solution_mem (hϑ : InΘ ϑ) (hw : InW w) {φ : ℝ → ℝ}
    (hφ : IsGlobalSolution (fun t x => ϑ t - w x) φ) :
    InΦϑ ϑ φ (fun t => ϑ t - w (φ t)) := by
  have hG := hw.inG hϑ
  have hΦ := hG.mem_Φ hφ
  have hcont := continuousOn_of_deriv hφ.deriv
  refine ⟨hΦ, hφ.deriv, hϑ.continuousOn.sub (hw.continuousOn.comp hcont fun t ht => hφ.nonneg t ht),
    fun M => ?_⟩
  obtain ⟨x, hx, hMx⟩ := hw.unbounded M
  obtain ⟨t, ht, rfl⟩ := hΦ.bijOn.surjOn (mem_Ici.mpr hx)
  exact ⟨t, ht, by simp only; linarith⟩

/-- Theorem 3.6 and Corollary 3.7, injectivity: two paths in `W` with the same global solution
agree on `ℝ₊`, since `w (φ (t)) = ϑ (t) - φ' (t)` and `φ` is onto `ℝ₊`. -/
theorem InW.injective (hϑ : InΘ ϑ) {w₁ w₂ : ℝ → ℝ} (hw₁ : InW w₁) {φ : ℝ → ℝ}
    (h₁ : IsGlobalSolution (fun t x => ϑ t - w₁ x) φ)
    (h₂ : IsGlobalSolution (fun t x => ϑ t - w₂ x) φ) : EqOn w₁ w₂ (Ici 0) := by
  have hΦ := (hw₁.inG hϑ).mem_Φ h₁
  intro x hx
  obtain ⟨t, ht, rfl⟩ := hΦ.bijOn.surjOn hx
  have := (uniqueDiffOn_Ici 0 t ht).eq_deriv _ (h₁.deriv t ht) (h₂.deriv t ht)
  linarith

/-- Theorem 3.6 and Corollary 3.7, surjectivity: each `φ ∈ Φ_ϑ` is the global solution for
`ϑ (t) - w (x)` with `w (x) = ϑ (φ⁻¹ (x)) - φ' (φ⁻¹ (x))`, which is in `W`. -/
theorem InΦϑ.exists_w (hϑ : InΘ ϑ) {φ φ' : ℝ → ℝ} (h : InΦϑ ϑ φ φ') :
    ∃ w, InW w ∧ IsGlobalSolution (fun t x => ϑ t - w x) φ := by
  obtain ⟨hΦ, hd, hφ'c, hsup⟩ := h
  have hψc := continuousOn_invPath hΦ.bijOn hΦ.strictMonoOn hΦ.init
  have hmaps : MapsTo (invPath φ) (Ici 0) (Ici 0) := fun x hx => invPath_nonneg hΦ.bijOn hx
  have hφ'nn : 0 ≤ φ' 0 := deriv_nonneg_of_monotoneOn hΦ.strictMonoOn.monotoneOn le_rfl (hd 0 le_rfl)
  refine ⟨fun x => ϑ (invPath φ x) - φ' (invPath φ x),
    ⟨(hϑ.continuousOn.comp hψc hmaps).sub (hφ'c.comp hψc hmaps), ?_, fun M => ?_⟩, ?_⟩
  · simp only [invPath_zero hΦ.bijOn hΦ.init, hϑ.zero]; linarith
  · obtain ⟨t, ht, hMt⟩ := hsup M
    exact ⟨φ t, hΦ.bijOn.mapsTo ht, by simp only [invPath_apply hΦ.bijOn ht]; exact hMt⟩
  · refine ⟨hΦ.init, fun t ht => hΦ.bijOn.mapsTo ht, fun t ht => ?_⟩
    have : ϑ t - (ϑ (invPath φ (φ t)) - φ' (invPath φ (φ t))) = φ' t := by
      rw [invPath_apply hΦ.bijOn ht]; ring
    simp only
    rw [this]
    exact hd t ht

end PathwiseVolatility
