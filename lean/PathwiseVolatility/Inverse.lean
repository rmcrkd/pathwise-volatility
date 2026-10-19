/-
Copyright (c) 2026 Ryan McCrickerd. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCrickerd
-/
import PathwiseVolatility.Basic

/-!
# Inverses of paths in `Φ`

The inverse `φ⁻¹` of a continuous bijection `φ` of `ℝ₊` with `φ (0) = 0`, which Chapter 3 uses
throughout: it is a bijection of `ℝ₊`, strictly increasing and continuous.
-/

open Set Filter Topology

namespace PathwiseVolatility

/-- The inverse `φ⁻¹` of a bijection `φ` of `ℝ₊`. -/
noncomputable def invPath (φ : ℝ → ℝ) : ℝ → ℝ := Function.invFunOn φ (Ici 0)

variable {φ : ℝ → ℝ}

theorem invPath_apply (h : BijOn φ (Ici 0) (Ici 0)) {t : ℝ} (ht : 0 ≤ t) :
    invPath φ (φ t) = t :=
  h.injOn.leftInvOn_invFunOn (mem_Ici.mpr ht)

theorem apply_invPath (h : BijOn φ (Ici 0) (Ici 0)) {x : ℝ} (hx : 0 ≤ x) :
    φ (invPath φ x) = x :=
  h.surjOn.rightInvOn_invFunOn (mem_Ici.mpr hx)

theorem invPath_nonneg (h : BijOn φ (Ici 0) (Ici 0)) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ invPath φ x :=
  h.surjOn.mapsTo_invFunOn (mem_Ici.mpr hx)

theorem bijOn_invPath (h : BijOn φ (Ici 0) (Ici 0)) : BijOn (invPath φ) (Ici 0) (Ici 0) := by
  refine ⟨fun x hx => invPath_nonneg h hx, fun x hx y hy hxy => ?_, fun t ht => ?_⟩
  · rw [← apply_invPath h hx, ← apply_invPath h hy, hxy]
  · exact ⟨φ t, h.mapsTo ht, invPath_apply h ht⟩

/-- A continuous bijection of `ℝ₊` with `φ (0) = 0` is strictly increasing. -/
theorem strictMonoOn_of_bijOn (h : BijOn φ (Ici 0) (Ici 0)) (hc : ContinuousOn φ (Ici 0))
    (h0 : φ 0 = 0) : StrictMonoOn φ (Ici 0) := by
  intro s hs t ht hst
  have hs' : (0 : ℝ) ≤ s := hs
  have ht' : (0 : ℝ) ≤ t := ht
  have hsub : Icc 0 t ⊆ Ici 0 := Icc_subset_Ici_self
  rcases (hc.mono hsub).strictMonoOn_of_injOn_Icc' ht' (h.injOn.mono hsub) with hm | ha
  · exact hm ⟨hs', hst.le⟩ ⟨ht', le_rfl⟩ hst
  · -- decreasing on `[0, t]` would take `φ (t)` below `φ (0) = 0`
    have := ha ⟨le_rfl, ht'⟩ ⟨ht', le_rfl⟩ (hs'.trans_lt hst)
    rw [h0] at this
    exact absurd (h.mapsTo ht) (not_le.mpr this)

theorem strictMonoOn_invPath (h : BijOn φ (Ici 0) (Ici 0)) (hm : StrictMonoOn φ (Ici 0)) :
    StrictMonoOn (invPath φ) (Ici 0) := by
  intro x hx y hy hxy
  by_contra hle
  push Not at hle
  have := (hm.le_iff_le (invPath_nonneg h hy) (invPath_nonneg h hx)).mpr hle
  rw [apply_invPath h hy, apply_invPath h hx] at this
  linarith

theorem invPath_zero (h : BijOn φ (Ici 0) (Ici 0)) (h0 : φ 0 = 0) : invPath φ 0 = 0 := by
  have := invPath_apply h (le_refl 0)
  rwa [h0] at this

/-- The inverse is continuous on `ℝ₊`, as a monotone map of `ℝ₊` onto `ℝ₊`. -/
theorem continuousOn_invPath (h : BijOn φ (Ici 0) (Ici 0)) (hm : StrictMonoOn φ (Ici 0))
    (h0 : φ 0 = 0) : ContinuousOn (invPath φ) (Ici 0) := by
  intro x hx
  have hmono := (strictMonoOn_invPath h hm).monotoneOn
  have himg : invPath φ '' Ici 0 = Ici 0 := (bijOn_invPath h).image_eq
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ x from hx) with hx0 | hx0
  · rw [← hx0]
    refine continuousWithinAt_right_of_monotoneOn_of_image_mem_nhdsWithin hmono
      self_mem_nhdsWithin ?_
    rw [himg, invPath_zero h h0]
    exact self_mem_nhdsWithin
  · have hpos : 0 < invPath φ x := by
      have := strictMonoOn_invPath h hm (mem_Ici.mpr le_rfl) hx hx0
      rwa [invPath_zero h h0] at this
    exact (continuousAt_of_monotoneOn_of_image_mem_nhds hmono (Ici_mem_nhds hx0)
      (by rw [himg]; exact Ici_mem_nhds hpos)).continuousWithinAt

end PathwiseVolatility
