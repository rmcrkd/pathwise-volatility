/-
Copyright (c) 2026 Ryan McCrickerd. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCrickerd
-/
import PathwiseVolatility.ExitLimits

/-!
# Theorem 3.18: construction of exit-time limits

Every `φ̄ ∈ Φ̄` is the limit, on `(Φ̄, d_Φ̄)`, of solutions of `x' = (n + 1) g_n (t, x)` with
`g_n → g₀ = ϑ (t) - w (x)`, for any `ϑ ∈ Θ` and `w ∈ W` with `M (w) = ϑ ∘ E (φ̄)`. Three identities
give `φ̄₀ = φ̄`: `E ∘ M = E` (a continuous `w` first exceeds a level when its running maximum does),
the strict increase of `ϑ`, and `E ∘ E = id` on `Φ̄`, part of Lemma 3.11.
-/

open Set Filter Topology

namespace PathwiseVolatility

variable {φb ϑ w : ℝ → ℝ}

/-- For `φ̄ ∈ Φ̄` and `t ≥ 0`, `E (φ̄) (x) > t` exactly when `x > φ̄ (t)`. -/
theorem InΦbar.lt_exitT_iff (h : InΦbar φb) {t x : ℝ} (ht : 0 ≤ t) :
    t < exitT φb x ↔ φb t < x := by
  have hmono := h.strictMonoOn.monotoneOn
  have hne : {s | 0 < s ∧ x < φb s}.Nonempty := by
    obtain ⟨_, ⟨s, hs, rfl⟩, hxs⟩ := not_bddAbove_iff.mp h.unbounded x
    refine ⟨max s 1, by positivity, hxs.trans_le (hmono hs ?_ (le_max_left _ _))⟩
    exact mem_Ici.mpr (by positivity)
  have hbdd : BddBelow {s | 0 < s ∧ x < φb s} := ⟨0, fun _ hs => hs.1.le⟩
  constructor
  · intro htx
    by_contra hle
    push Not at hle
    refine absurd htx (not_lt.mpr (le_of_forall_gt_imp_ge_of_dense fun c htc => ?_))
    exact csInf_le hbdd ⟨ht.trans_lt htc, hle.trans_lt (h.strictMonoOn (mem_Ici.mpr ht)
      (mem_Ici.mpr (ht.trans htc.le)) htc)⟩
  · intro hxt
    obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.mp (h.rightCont t ht) (x - φb t)
      (by linarith)
    refine lt_of_lt_of_le (show t < t + δ / 2 by linarith) (le_csInf hne fun s hs => ?_)
    by_contra hlt
    push Not at hlt
    rcases le_total s t with hst | hts
    · have := hmono (mem_Ici.mpr hs.1.le) (mem_Ici.mpr ht) hst
      linarith [hs.2]
    · have := hball (mem_Ici.mpr hts) (by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith)
      rw [Real.dist_eq] at this
      linarith [le_abs_self (φb s - φb t), hs.2]

/-- Lemma 3.11, in part: `E ∘ E = id` on `Φ̄`. -/
theorem InΦbar.exitT_exitT (h : InΦbar φb) {t : ℝ} (ht : 0 ≤ t) : exitT (exitT φb) t = φb t := by
  have hset : {x | 0 < x ∧ t < exitT φb x} = Ioi (φb t) := by
    ext x
    simp only [mem_ofPred_eq, mem_Ioi]
    rw [h.lt_exitT_iff ht]
    exact ⟨fun hx => hx.2, fun hx => ⟨lt_of_le_of_lt (h.nonneg t ht) hx, hx⟩⟩
  rw [exitT, hset, csInf_Ioi]

/-- `E ∘ M = E`: for `w` continuous on `ℝ₊` with `w (0) ≤ 0`, and a level `c ≥ 0`, the first time
`w` exceeds `c` is the first time its running maximum does. -/
theorem sInf_lt_supF {c : ℝ} (hw : ContinuousOn w (Ici 0)) (hw0 : w 0 ≤ 0) (hc : 0 ≤ c)
    (hne : ∃ x, 0 < x ∧ c < w x) :
    sInf {x | 0 < x ∧ c < w x} = sInf {x | 0 < x ∧ c < supF w x} := by
  have hbddA : ∀ x, BddAbove ((fun s => max 0 (w s)) '' Icc 0 x) := fun x =>
    (isCompact_Icc.image_of_continuousOn
      (ContinuousOn.sup continuousOn_const (hw.mono Icc_subset_Ici_self))).bddAbove
  have hsub : {x | 0 < x ∧ c < w x} ⊆ {x | 0 < x ∧ c < supF w x} := fun x hx =>
    ⟨hx.1, hx.2.trans_le ((le_max_right 0 (w x)).trans
      (le_csSup (hbddA x) ⟨x, ⟨hx.1.le, le_rfl⟩, rfl⟩))⟩
  obtain ⟨x₀, hx₀⟩ := hne
  refine le_antisymm (le_csInf ⟨x₀, hsub hx₀⟩ fun x hx => ?_)
    (csInf_le_csInf ⟨0, fun _ hs => hs.1.le⟩ ⟨x₀, hx₀⟩ hsub)
  obtain ⟨_, ⟨y, hy, rfl⟩, hcy⟩ := exists_lt_of_lt_csSup
    ((nonempty_Icc.mpr hx.1.le).image fun s => max 0 (w s)) hx.2
  have hcy' : c < max 0 (w y) := hcy
  have hwy : c < w y := by
    rcases le_total (w y) 0 with h0 | h0
    · rw [max_eq_left h0] at hcy'; linarith
    · rwa [max_eq_right h0] at hcy'
  have hy0 : 0 < y := lt_of_le_of_ne hy.1 fun h0 => by rw [← h0] at hwy; linarith
  exact (csInf_le ⟨0, fun _ hs => hs.1.le⟩ (show y ∈ {x | 0 < x ∧ c < w x} from ⟨hy0, hwy⟩)).trans
    hy.2

/-- Theorem 3.18: with `M (w) = ϑ ∘ E (φ̄)`, the bound of `g₀ (t, x) = ϑ (t) - w (x)` is `φ̄`. -/
theorem barG_construct (hφ : InΦbar φb) (hϑ : InΘ ϑ) (hw : InW w)
    (hM : ∀ x, 0 ≤ x → supF w x = ϑ (exitT φb x)) {t : ℝ} (ht : 0 ≤ t) :
    barG (fun t x => ϑ t - w x) t = φb t := by
  have hϑt : 0 ≤ ϑ t := by
    have := hϑ.strictMonoOn.monotoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht
    rwa [hϑ.zero] at this
  have h1 : {x | 0 < x ∧ ϑ t - w x < 0} = {x | 0 < x ∧ ϑ t < w x} := by
    ext x; simp only [mem_ofPred_eq, sub_neg]
  have hne : ∃ x, 0 < x ∧ ϑ t < w x := by
    obtain ⟨x, hx, hwx⟩ := hw.unbounded (ϑ t)
    exact ⟨x, lt_of_le_of_ne hx fun h0 => by rw [← h0] at hwx; linarith [hw.nonpos_zero], hwx⟩
  have h2 : {x | 0 < x ∧ ϑ t < supF w x} = {x | 0 < x ∧ t < exitT φb x} := by
    ext x
    simp only [mem_ofPred_eq]
    refine and_congr_right fun hx => ?_
    rw [hM x hx.le]
    exact hϑ.strictMonoOn.lt_iff_lt (mem_Ici.mpr ht) (mem_Ici.mpr (exitT_nonneg φb x))
  rw [barG, h1, sInf_lt_supF hw.continuousOn hw.nonpos_zero hϑt hne, h2]
  exact hφ.exitT_exitT ht

variable {G : ℕ → ℝ → ℝ → ℝ}

/-- Theorem 3.18 (Construction of exit-time limits): every `φ̄ ∈ Φ̄` is the limit on `(Φ̄, d_Φ̄)` of
the global solutions of `x' = (n + 1) g_n (t, x)`, `x (0) = 0`, whenever `g_n → ϑ (t) - w (x)`
uniformly on compacts, for any `ϑ ∈ Θ` and `w ∈ W` with `M (w) = ϑ ∘ E (φ̄)`. -/
theorem construct_limit (hφ : InΦbar φb) (hϑ : InΘ ϑ) (hw : InW w)
    (hM : ∀ x, 0 ≤ x → supF w x = ϑ (exitT φb x)) (hG : ∀ n, InG (G n))
    (hconv : ∀ T X η, 0 < η → ∀ᶠ n in atTop, ∀ t ∈ Icc 0 T, ∀ x ∈ Icc 0 X,
      |G n t x - (ϑ t - w x)| < η)
    {φ : ℕ → ℝ → ℝ} (hsol : ∀ n : ℕ, IsGlobalSolution (fun t x => ((n : ℝ) + 1) * G n t x) (φ n)) :
    Tendsto (fun n => exitMetric (φ n) φb) atTop (𝓝 0) := by
  have hlim := (exit_limit (g₀ := fun t x => ϑ t - w x) (hw.inG hϑ) hG hconv hsol).2
  have hE : exitT (barG fun t x => ϑ t - w x) = exitT φb := by
    funext x
    unfold exitT
    congr 1
    ext s
    simp only [mem_ofPred_eq]
    refine and_congr_right fun hs => ?_
    rw [barG_construct hφ hϑ hw hM hs.le]
  simpa only [exitMetric, hE] using hlim

end PathwiseVolatility
