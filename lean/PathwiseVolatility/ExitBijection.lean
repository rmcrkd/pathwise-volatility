/-
Copyright (c) 2026 Ryan McCrickerd. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCrickerd
-/
import PathwiseVolatility.ExitConstruct

/-!
# Lemma 3.11, and the paths of `Φ̄` and `N`

Lemma 3.11 (Exit-time bijectivity): `E` maps `Φ̄` to `N` and `N` to `Φ̄`, and `E ∘ E = id` on both,
so `E` is a bijective involution between them. The thesis cites Whitt for this; here it is proved
from the definitions. Also: the bound `φ̄₀` of Theorem 3.3 is in `Φ̄`, and the level sets of
`E (φ̄)` are the intervals `[φ̄ (t₋), φ̄ (t)]`, which the excursionary limits use.
-/

open Set Filter Topology

namespace PathwiseVolatility

variable {φ ψ : ℝ → ℝ}

/-- The left limit `φ̄ (t₋) = sup {φ̄ (s) : s ∈ [0, t)}` of a path in `Φ̄`, with `φ̄ (0₋) = 0` as in
eq. (3.18) (`sSup ∅ = 0`). -/
noncomputable def leftVal (φ : ℝ → ℝ) (t : ℝ) : ℝ := sSup (φ '' Ico 0 t)

theorem leftVal_nonneg (h : ∀ t, 0 ≤ t → 0 ≤ φ t) (t : ℝ) : 0 ≤ leftVal φ t :=
  Real.sSup_nonneg (by rintro _ ⟨s, hs, rfl⟩; exact h s hs.1)

/-! ### Paths in `Φ̄` -/

theorem InΦbar.exists_gt (h : InΦbar φ) (M : ℝ) : ∃ t, 0 < t ∧ M < φ t := by
  obtain ⟨_, ⟨s, hs, rfl⟩, hxs⟩ := not_bddAbove_iff.mp h.unbounded M
  refine ⟨max s 1, by positivity, hxs.trans_le (h.strictMonoOn.monotoneOn hs ?_ (le_max_left _ _))⟩
  exact mem_Ici.mpr (by positivity)

theorem InΦbar.leftVal_le (h : InΦbar φ) {t : ℝ} (ht : 0 ≤ t) : leftVal φ t ≤ φ t :=
  Real.sSup_le (by rintro _ ⟨s, hs, rfl⟩; exact h.strictMonoOn.monotoneOn hs.1 ht hs.2.le)
    (h.nonneg t ht)

theorem InΦbar.bddAbove_Ico (h : InΦbar φ) {t : ℝ} (ht : 0 ≤ t) : BddAbove (φ '' Ico 0 t) :=
  ⟨φ t, by rintro _ ⟨s, hs, rfl⟩; exact h.strictMonoOn.monotoneOn hs.1 ht hs.2.le⟩

theorem InΦbar.lt_leftVal (h : InΦbar φ) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    φ s < leftVal φ t :=
  (h.strictMonoOn hs (mem_Ici.mpr (by linarith)) (by linarith : s < (s + t) / 2)).trans_le
    (le_csSup (h.bddAbove_Ico (hs.trans hst.le)) ⟨(s + t) / 2, ⟨by linarith, by linarith⟩, rfl⟩)

theorem InΦbar.exitT_le_of_le (h : InΦbar φ) {t x : ℝ} (ht : 0 ≤ t) (hx : x ≤ φ t) :
    exitT φ x ≤ t :=
  not_lt.mp fun hlt => absurd ((h.lt_exitT_iff ht).mp hlt) (not_lt.mpr hx)

theorem InΦbar.le_exitT_of_leftVal_le (h : InΦbar φ) {t x : ℝ} (hx : leftVal φ t ≤ x) :
    t ≤ exitT φ x := by
  by_contra hlt
  push Not at hlt
  have h0 := exitT_nonneg φ x
  have := (h.lt_exitT_iff h0).mpr ((h.lt_leftVal h0 hlt).trans_le hx)
  exact lt_irrefl _ this

/-- The level sets of `E (φ̄)` are the intervals `[φ̄ (t₋), φ̄ (t)]`. -/
theorem InΦbar.exitT_eq_iff (h : InΦbar φ) {t x : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) :
    exitT φ x = t ↔ x ∈ Icc (leftVal φ t) (φ t) := by
  constructor
  · rintro rfl
    refine ⟨Real.sSup_le (by rintro _ ⟨s, hs, rfl⟩; exact ((h.lt_exitT_iff hs.1).mp hs.2).le) hx,
      not_lt.mp fun hlt => lt_irrefl _ ((h.lt_exitT_iff ht).mpr hlt)⟩
  · rintro ⟨h1, h2⟩
    exact le_antisymm (h.exitT_le_of_le ht h2) (h.le_exitT_of_leftVal_le h1)

/-- Lemma 3.11, in part: `E` maps `Φ̄` to `N`. -/
theorem InΦbar.inN_exitT (h : InΦbar φ) : InN (exitT φ) := by
  refine ⟨le_antisymm (h.exitT_le_of_le le_rfl (h.nonneg 0 le_rfl)) (exitT_nonneg φ 0), ?_,
    fun x _ y _ hxy => exitT_mono h.exists_gt hxy, fun M => ?_⟩
  · intro x hx
    refine (Metric.continuousAt_iff.mpr fun ε hε => ?_).continuousWithinAt
    set t₀ := exitT φ x with ht₀
    have h0 : 0 ≤ t₀ := exitT_nonneg φ x
    have hmem := (h.exitT_eq_iff h0 hx).mp rfl
    have h2 : x < φ (t₀ + ε / 2) :=
      hmem.2.trans_lt (h.strictMonoOn (mem_Ici.mpr h0) (mem_Ici.mpr (by linarith)) (by linarith))
    have hup : ∀ y, y < φ (t₀ + ε / 2) → exitT φ y ≤ t₀ + ε / 2 := fun y hy =>
      h.exitT_le_of_le (by linarith) hy.le
    rcases le_or_gt t₀ (ε / 2) with hsmall | hbig
    · refine ⟨φ (t₀ + ε / 2) - x, by linarith, fun y hy => ?_⟩
      rw [Real.dist_eq] at hy ⊢
      have := hup y (by linarith [le_abs_self (y - x)])
      rw [abs_lt]
      constructor <;> linarith [exitT_nonneg φ y]
    · have h1 : φ (t₀ - ε / 2) < x := (h.lt_exitT_iff (by linarith)).mp (by linarith)
      refine ⟨min (φ (t₀ + ε / 2) - x) (x - φ (t₀ - ε / 2)), lt_min (by linarith) (by linarith),
        fun y hy => ?_⟩
      rw [Real.dist_eq] at hy ⊢
      have hy1 := hy.trans_le (min_le_left _ _)
      have hy2 := hy.trans_le (min_le_right _ _)
      have := hup y (by linarith [le_abs_self (y - x)])
      have hlow : t₀ - ε / 2 < exitT φ y :=
        (h.lt_exitT_iff (by linarith)).mpr (by linarith [neg_abs_le (y - x)])
      rw [abs_lt]
      constructor <;> linarith
  · refine ⟨φ (|M| + 1), h.nonneg _ (by positivity), ?_⟩
    exact (show M < |M| + 1 by linarith [le_abs_self M]).trans_le
      (h.le_exitT_of_leftVal_le (h.leftVal_le (by positivity)))

/-- `Φ̄` depends only on the values on `ℝ₊`. -/
theorem InΦbar.congr (h : InΦbar φ) (heq : ∀ t, 0 ≤ t → φ t = ψ t) : InΦbar ψ := by
  refine ⟨fun t ht => heq t ht ▸ h.nonneg t ht, fun s hs t ht hst => ?_, fun t ht => ?_,
    fun t ht => ?_, ?_⟩
  · rw [← heq s hs, ← heq t ht]; exact h.strictMonoOn hs ht hst
  · exact (h.rightCont t ht).congr (fun y hy => (heq y (ht.trans hy)).symm) (heq t ht).symm
  · obtain ⟨l, hl⟩ := h.leftLim t ht
    refine ⟨l, hl.congr' ?_⟩
    filter_upwards [Ioo_mem_nhdsLT ht] with s hs
    exact heq s hs.1.le
  · have : φ '' Ici 0 = ψ '' Ici 0 := image_congr fun t ht => heq t ht
    rw [← this]; exact h.unbounded

/-! ### Paths in `N` -/

theorem InN.nonneg (h : InN ψ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ ψ t :=
  h.zero ▸ h.monotoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht

theorem InN.exists_gt (h : InN ψ) (M : ℝ) : ∃ t, 0 < t ∧ M < ψ t := by
  obtain ⟨t, ht, hMt⟩ := h.unbounded (max M 0)
  refine ⟨t, lt_of_le_of_ne ht fun h0 => ?_, (le_max_left M 0).trans_lt hMt⟩
  rw [← h0, h.zero] at hMt
  linarith [le_max_right M 0]

theorem exitT_le_of_lt {t x : ℝ} (ht : 0 < t) (hx : x < ψ t) : exitT ψ x ≤ t :=
  csInf_le ⟨0, fun _ hs => hs.1.le⟩ ⟨ht, hx⟩

theorem InN.lt_of_exitT_lt (h : InN ψ) {s x : ℝ} (hs : exitT ψ x < s) : x < ψ s := by
  obtain ⟨u, ⟨hu0, hxu⟩, hus⟩ := exists_lt_of_csInf_lt (h.exists_gt x) hs
  exact hxu.trans_le (h.monotoneOn (mem_Ici.mpr hu0.le) (mem_Ici.mpr (hu0.le.trans hus.le)) hus.le)

theorem InN.le_of_lt_exitT (h : InN ψ) {s x : ℝ} (hs : 0 ≤ s) (hst : s < exitT ψ x) : ψ s ≤ x := by
  by_contra hlt
  push Not at hlt
  refine absurd hst (not_lt.mpr (le_of_forall_gt_imp_ge_of_dense fun u hu => ?_))
  exact exitT_le_of_lt (hs.trans_lt hu)
    (hlt.trans_le (h.monotoneOn (mem_Ici.mpr hs) (mem_Ici.mpr (hs.trans hu.le)) hu.le))

theorem InN.apply_exitT (h : InN ψ) {x : ℝ} (hx : 0 ≤ x) : ψ (exitT ψ x) = x := by
  set a := exitT ψ x with ha
  have ha0 : 0 ≤ a := exitT_nonneg ψ x
  refine le_antisymm ?_ ?_
  · rcases eq_or_lt_of_le ha0 with h0 | h0
    · rw [← h0, h.zero]; exact hx
    · have hc : ContinuousWithinAt ψ (Iio a) a :=
        ((h.continuousOn a ha0).continuousAt (Ici_mem_nhds h0)).continuousWithinAt
      refine le_of_tendsto hc ?_
      filter_upwards [Ioo_mem_nhdsLT h0] with s hs
      exact h.le_of_lt_exitT hs.1.le hs.2
  · have hc : ContinuousWithinAt ψ (Ioi a) a :=
      (h.continuousOn a ha0).mono fun s hs => mem_Ici.mpr (ha0.trans (le_of_lt hs))
    refine ge_of_tendsto hc ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (h.lt_of_exitT_lt hs).le

/-- Lemma 3.11, in part: `E` maps `N` to `Φ̄`. -/
theorem InN.inΦbar_exitT (h : InN ψ) : InΦbar (exitT ψ) := by
  have hmono : Monotone (exitT ψ) := fun _ _ hxy => exitT_mono h.exists_gt hxy
  refine ⟨fun x _ => exitT_nonneg ψ x, fun x hx y hy hxy => ?_, fun x hx => ?_,
    fun t _ => ⟨_, hmono.tendsto_nhdsLT t⟩, ?_⟩
  · refine lt_of_le_of_ne (hmono hxy.le) fun heq => ?_
    have := congrArg ψ heq
    rw [h.apply_exitT hx, h.apply_exitT hy] at this
    exact hxy.ne this
  · refine Metric.continuousWithinAt_iff.mpr fun ε hε => ?_
    set a := exitT ψ x
    have hlt := h.lt_of_exitT_lt (show a < a + ε / 2 by linarith)
    refine ⟨ψ (a + ε / 2) - x, by linarith, fun y hy hyx => ?_⟩
    rw [Real.dist_eq] at hyx ⊢
    have hxy : x ≤ y := hy
    rw [abs_of_nonneg (by linarith)] at hyx
    have h1 := exitT_le_of_lt (by linarith [exitT_nonneg ψ x])
      (show y < ψ (a + ε / 2) by linarith)
    have h2 := hmono hxy
    rw [abs_lt]
    constructor <;> linarith
  · rintro ⟨B, hB⟩
    set T := max B 0 + 1
    have hT : B < T := by linarith [le_max_left B 0]
    have hx : 0 ≤ ψ T + 1 := by linarith [h.nonneg (show 0 ≤ T by positivity)]
    have : T ≤ exitT ψ (ψ T + 1) := not_lt.mp fun hlt => by
      have := h.lt_of_exitT_lt hlt; linarith
    linarith [hB ⟨ψ T + 1, hx, rfl⟩]

/-- Lemma 3.11, in part: `E ∘ E = id` on `N`. -/
theorem InN.exitT_exitT (h : InN ψ) {t : ℝ} (ht : 0 ≤ t) : exitT (exitT ψ) t = ψ t := by
  have hbdd : BddBelow {x | 0 < x ∧ t < exitT ψ x} := ⟨0, fun _ hx => hx.1.le⟩
  -- points `ψ (t + δ) + ε` with `ψ (t + δ)` close to `ψ (t)` are in the set
  have hnear : ∀ ε, 0 < ε → ∃ x, (0 < x ∧ t < exitT ψ x) ∧ x < ψ t + ε := by
    intro ε hε
    obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.mp
      ((h.continuousOn t ht).mono (Ici_subset_Ici.mpr ht)) (ε / 2) (by positivity)
    have hd := hball (mem_Ici.mpr (by linarith : t ≤ t + δ / 2))
      (by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith)
    rw [Real.dist_eq] at hd
    refine ⟨ψ (t + δ / 2) + ε / 2, ⟨by linarith [h.nonneg (show 0 ≤ t + δ / 2 by linarith)], ?_⟩,
      by linarith [le_abs_self (ψ (t + δ / 2) - ψ t)]⟩
    by_contra hle
    push Not at hle
    have := h.lt_of_exitT_lt (show exitT ψ (ψ (t + δ / 2) + ε / 2) < t + δ / 2 by linarith)
    linarith
  obtain ⟨x₁, hx₁, -⟩ := hnear 1 one_pos
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_)
    (le_csInf ⟨x₁, hx₁⟩ fun x hx => h.le_of_lt_exitT ht hx.2)
  obtain ⟨x, hx, hxε⟩ := hnear ε hε
  exact (csInf_le hbdd hx).trans hxε.le

/-! ### The bound of Theorem 3.3 -/

variable {g : ℝ → ℝ → ℝ}

theorem InG.zeroG_zero (hg : InG g) : zeroG g 0 = 0 :=
  le_antisymm (not_lt.mp fun hpos => by
    have := (hg.lt_zeroG_iff le_rfl le_rfl).mp hpos; linarith [hg.nonneg_zero]) (zeroG_nonneg g 0)

/-- `M (ϕ) ∈ N`, as noted before Corollary 3.15. -/
theorem InG.inN_supF (hg : InG g) : InN (supF (zeroG g)) := by
  refine ⟨?_, hg.continuousOn_supF, fun x hx y _ hxy => hg.supF_mono hx hxy, fun M => ?_⟩
  · simp [supF, hg.zeroG_zero]
  · obtain ⟨x, hx, hneg⟩ := hg.exists_neg (max M 0 + 1) (by positivity)
    have := (hg.lt_zeroG_iff (by positivity) hx).mpr hneg
    exact ⟨x, hx, by linarith [le_max_left M 0, hg.zeroG_le_supF (x := x) ⟨hx, le_rfl⟩]⟩

theorem InG.barG_eq_exitT_supF (hg : InG g) {t : ℝ} (ht : 0 ≤ t) :
    barG g t = exitT (supF (zeroG g)) t := by
  rw [← hg.exitT_zeroG ht]
  obtain ⟨x, hx, hneg⟩ := hg.nonempty_neg ht
  exact sInf_lt_supF hg.continuousOn_zeroG hg.zeroG_zero.le ht
    ⟨x, hx, (hg.lt_zeroG_iff ht hx.le).mpr hneg⟩

/-- The bound `φ̄` of Theorem 3.3 is in `Φ̄`. -/
theorem InG.inΦbar_barG (hg : InG g) : InΦbar (barG g) :=
  hg.inN_supF.inΦbar_exitT.congr fun _ ht => (hg.barG_eq_exitT_supF ht).symm

/-- The example in Theorem 3.18: `w = ϑ ∘ E (φ̄)` is in `W` and satisfies `M (w) = ϑ ∘ E (φ̄)`. -/
theorem InΦbar.construct_example {ϑ : ℝ → ℝ} (h : InΦbar φ) (hϑ : InΘ ϑ) :
    InW (fun x => ϑ (exitT φ x)) ∧
      ∀ x, 0 ≤ x → supF (fun x => ϑ (exitT φ x)) x = ϑ (exitT φ x) := by
  have hN := h.inN_exitT
  have hϑ0 : ∀ t, 0 ≤ t → 0 ≤ ϑ t := fun t ht => by
    have := hϑ.strictMonoOn.monotoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht
    rwa [hϑ.zero] at this
  have hmono : ∀ s x, 0 ≤ s → s ≤ x → ϑ (exitT φ s) ≤ ϑ (exitT φ x) := fun s x hs hsx =>
    hϑ.strictMonoOn.monotoneOn (mem_Ici.mpr (exitT_nonneg φ s)) (mem_Ici.mpr (exitT_nonneg φ x))
      (hN.monotoneOn (mem_Ici.mpr hs) (mem_Ici.mpr (hs.trans hsx)) hsx)
  refine ⟨⟨hϑ.continuousOn.comp hN.continuousOn fun x _ => mem_Ici.mpr (exitT_nonneg φ x),
    by simp only [hN.zero, hϑ.zero, le_refl], fun M => ?_⟩, fun x hx => ?_⟩
  · obtain ⟨t, ht, hMt⟩ := hϑ.unbounded M
    obtain ⟨x, hx, htx⟩ := hN.unbounded t
    exact ⟨x, hx, hMt.trans_le (hϑ.strictMonoOn.monotoneOn (mem_Ici.mpr ht)
      (mem_Ici.mpr (exitT_nonneg φ x)) htx.le)⟩
  · refine IsGreatest.csSup_eq ⟨⟨x, ⟨hx, le_rfl⟩, max_eq_right (hϑ0 _ (exitT_nonneg φ x))⟩, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact max_le (hϑ0 _ (exitT_nonneg φ x)) (hmono s x hs.1 hs.2)

end PathwiseVolatility
