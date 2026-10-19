/-
Copyright (c) 2026 Ryan McCrickerd. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCrickerd
-/
import PathwiseVolatility.InverseSolution

/-!
# Solutions: their regularity, their image, and their inverse at the initial time

Problem 1.2 asks for solutions in `C¹`; Theorem 2.8 says a solution is a bijection of `[τ, T)` onto
`[ξ, X_*)`, where `X_* = sup φ`; and Lemma 2.16's relation `φ' (t) φ̂' (φ (t)) = 1` holds at the
initial time too, between one-sided derivatives.
-/

open Set Filter Topology

namespace PathwiseVolatility

variable {f : ℝ → ℝ → ℝ} {τ ξ : ℝ} {T : EReal} {φ : ℝ → ℝ}

/-- Problem 1.2: a solution is `C¹`, its derivative `t ↦ f (t, φ (t))` being continuous on
`[τ, T)`. -/
theorem IsSolution.continuousOn_deriv (hf : InF f) (hφ : IsSolution f τ ξ T φ) :
    ContinuousOn (fun t => f t (φ t)) (Dom τ T) :=
  hf.continuous.comp_continuousOn (continuousOn_id.prodMk hφ.continuousOn)

section

variable (hf : InF f) (hpos : LineCondition f τ ξ) (hφ : IsSolution f τ ξ T φ)
include hf hpos hφ

/-- Theorem 2.8, the bijection: a solution maps `[τ, T)` onto `[ξ, X_*)`, where `X_* = sup φ`.
Its image is the set of `x ≥ ξ` lying below some value of `φ`. -/
theorem image_dom : φ '' Dom τ T = {x | ξ ≤ x ∧ ∃ t ∈ Dom τ T, x < φ t} := by
  have hm := strictMonoOn_solution hf hpos hφ
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨t, ht, hst⟩ := exists_dom_gt hs
    exact ⟨le_solution hf hpos hφ hs, t, ht, hm hs ht hst⟩
  · rintro ⟨hξx, t, ht, hxt⟩
    refine Icc_subset_image hφ (mem_dom_self hφ.lt) ht ⟨?_, hxt.le⟩
    rw [hφ.init]
    exact hξx

/-- Lemma 2.16 at the initial time: if `φ' (τ) = f (τ, ξ) > 0`, the inverse has the right
derivative `1 / φ' (τ)` at `ξ`, within the image `[ξ, X_*)`. -/
theorem hasDerivWithinAt_solInv_init (hτ : 0 < f τ ξ) :
    HasDerivWithinAt (solInv φ τ T) (f τ ξ)⁻¹ (φ '' Dom τ T) ξ := by
  have h0 := mem_dom_self hφ.lt
  have hξ : ξ ∈ φ '' Dom τ T := ⟨τ, h0, hφ.init⟩
  have hinv : solInv φ τ T ξ = τ := by
    rw [← hφ.init]; exact solInv_apply hf hpos hφ h0
  have hd : HasDerivWithinAt φ (f τ ξ) (Dom τ T) (solInv φ τ T ξ) := by
    rw [hinv]
    have := hφ.deriv τ h0
    rwa [hφ.init] at this
  have hg : Tendsto (solInv φ τ T) (𝓝[φ '' Dom τ T] ξ) (𝓝[Dom τ T] (solInv φ τ T ξ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨((continuousOn_solInv hf hpos hφ) ξ hξ).tendsto,
      eventually_nhdsWithin_of_forall fun x hx => solInv_mem hx⟩
  exact (show HasFDerivWithinAt φ (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 _ hτ.ne') :
      ℝ →L[ℝ] ℝ) (Dom τ T) (solInv φ τ T ξ) from hd).of_local_left_inverse hg hξ
    (eventually_nhdsWithin_of_forall fun x hx => apply_solInv hx)

/-- Lemma 2.16 at the initial time, conversely: if the inverse has a right derivative `d` at `ξ`
within the image, then `φ' (τ) d = 1`, so `φ' (τ) = f (τ, ξ) > 0`. -/
theorem mul_eq_one_of_hasDerivWithinAt_solInv_init {d : ℝ}
    (hd : HasDerivWithinAt (solInv φ τ T) d (φ '' Dom τ T) ξ) : f τ ξ * d = 1 ∧ 0 < f τ ξ := by
  have h0 := mem_dom_self hφ.lt
  have hφd : HasDerivWithinAt φ (f τ ξ) (Dom τ T) τ := by
    have := hφ.deriv τ h0
    rwa [hφ.init] at this
  have hd' : HasDerivWithinAt (solInv φ τ T) d (φ '' Dom τ T) (φ τ) := by rwa [hφ.init]
  have hcomp := hd'.comp τ hφd fun t ht => ⟨t, ht, rfl⟩
  have hid : HasDerivWithinAt (solInv φ τ T ∘ φ) 1 (Dom τ T) τ :=
    (hasDerivWithinAt_id τ (Dom τ T)).congr (fun t ht => solInv_apply hf hpos hφ ht)
      (solInv_apply hf hpos hφ h0)
  obtain ⟨t', ht', hτt'⟩ := exists_dom_gt h0
  have hint : (interior (Dom τ T)).Nonempty :=
    ⟨(τ + t') / 2, mem_interior_iff_mem_nhds.mpr (mem_of_superset
      (Ioo_mem_nhds (by linarith) (by linarith)) fun u hu =>
        ⟨hu.1.le, (EReal.coe_lt_coe_iff.mpr hu.2).trans ht'.2⟩)⟩
  have hone : d * f τ ξ = 1 :=
    (uniqueDiffOn_convex convex_dom hint τ h0).eq_deriv _ hcomp hid
  have hne : f τ ξ ≠ 0 := fun h => by rw [h, mul_zero] at hone; exact zero_ne_one hone
  exact ⟨by rw [mul_comm]; exact hone, lt_of_le_of_ne (hpos.nonneg hf) (Ne.symm hne)⟩

end

end PathwiseVolatility
