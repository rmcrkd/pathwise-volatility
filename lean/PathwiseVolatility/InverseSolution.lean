/-
Copyright (c) 2026 Ryan McCrickerd. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCrickerd
-/
import PathwiseVolatility.Bounds

/-!
# Lemma 2.16: solutions' inverse properties

A solution `φ` on `[τ, T)` is strictly increasing (Theorem 2.8), so it has an inverse `φ̂` on its
image `φ ([τ, T))`, which is the thesis's `[ξ, X_*)`. The inverse is strictly increasing and
continuous; where `φ' (t) > 0` it is differentiable at `φ (t)` with `φ̂' = 1 / φ'`, and conversely.
By Lebesgue's theorem it is differentiable almost everywhere on any `[a, b]` in the image, with
`φ̂ (b) - φ̂ (a) ≥ ∫ φ̂'`; if `φ̂` is differentiable off finitely many points of `[a, b]`, it is
absolutely continuous there, with equality, and `φ' > 0` almost everywhere on `[φ̂ (a), φ̂ (b)]`.
-/

open Set Filter Topology MeasureTheory

namespace PathwiseVolatility

variable {f : ℝ → ℝ → ℝ} {τ ξ : ℝ} {T : EReal} {φ : ℝ → ℝ}

/-- The inverse `φ̂` of a solution `φ` on `[τ, T)`, on the image `φ ([τ, T))`. -/
noncomputable def solInv (φ : ℝ → ℝ) (τ : ℝ) (T : EReal) : ℝ → ℝ :=
  Function.invFunOn φ (Dom τ T)

section

variable (hf : InF f) (hpos : LineCondition f τ ξ) (hφ : IsSolution f τ ξ T φ)
include hf hpos hφ

theorem solInv_apply {t : ℝ} (ht : t ∈ Dom τ T) : solInv φ τ T (φ t) = t :=
  (strictMonoOn_solution hf hpos hφ).injOn.leftInvOn_invFunOn ht

omit hf hpos hφ in
theorem apply_solInv {x : ℝ} (hx : x ∈ φ '' Dom τ T) : φ (solInv φ τ T x) = x :=
  Function.invFunOn_eq hx

omit hf hpos hφ in
theorem solInv_mem {x : ℝ} (hx : x ∈ φ '' Dom τ T) : solInv φ τ T x ∈ Dom τ T :=
  Function.invFunOn_mem hx

/-- Lemma 2.16: `φ̂` is strictly increasing on the image. -/
theorem strictMonoOn_solInv : StrictMonoOn (solInv φ τ T) (φ '' Dom τ T) := by
  intro x hx y hy hxy
  by_contra hle
  push Not at hle
  have := (strictMonoOn_solution hf hpos hφ).monotoneOn (solInv_mem hy) (solInv_mem hx) hle
  rw [apply_solInv hy, apply_solInv hx] at this
  linarith

theorem solInv_image : solInv φ τ T '' (φ '' Dom τ T) = Dom τ T := by
  ext t
  refine ⟨fun ⟨x, hx, hxt⟩ => hxt ▸ solInv_mem hx, fun ht => ⟨φ t, ⟨t, ht, rfl⟩, ?_⟩⟩
  exact solInv_apply hf hpos hφ ht

omit hf hpos hφ in
/-- Every time in `[τ, T)` has a later one. -/
theorem exists_dom_gt {t : ℝ} (ht : t ∈ Dom τ T) : ∃ t' ∈ Dom τ T, t < t' := by
  obtain ⟨r, htr, hrT⟩ := EReal.lt_iff_exists_real_btwn.mp ht.2
  have htr' : t < r := EReal.coe_lt_coe_iff.mp htr
  refine ⟨(t + r) / 2, ⟨by linarith [ht.1], ?_⟩, by linarith⟩
  exact (EReal.coe_lt_coe_iff.mpr (by linarith)).trans hrT

omit hf hpos in
theorem ordConnected_image : OrdConnected (φ '' Dom τ T) :=
  (convex_dom.isPreconnected.image φ hφ.continuousOn).ordConnected

omit hf hpos in
/-- The image of a neighbourhood: `φ ([τ, T))` contains `[φ (t), φ (t')]` for `t < t'` in `[τ, T)`. -/
theorem Icc_subset_image {t t' : ℝ} (ht : t ∈ Dom τ T) (ht' : t' ∈ Dom τ T) :
    Icc (φ t) (φ t') ⊆ φ '' Dom τ T :=
  (ordConnected_image hφ).out ⟨t, ht, rfl⟩ ⟨t', ht', rfl⟩

/-- Lemma 2.16: at an interior point `φ (t)`, `t > τ`, the image is a neighbourhood and `φ̂` is
continuous. -/
theorem image_mem_nhds {t : ℝ} (ht : t ∈ Dom τ T) (hτt : τ < t) : φ '' Dom τ T ∈ 𝓝 (φ t) := by
  obtain ⟨t', ht', htt'⟩ := exists_dom_gt ht
  have hm := strictMonoOn_solution hf hpos hφ
  have h1 : φ τ < φ t := hm (mem_dom_self hφ.lt) ht hτt
  have h2 : φ t < φ t' := hm ht ht' htt'
  exact mem_of_superset (Icc_mem_nhds h1 h2) (Icc_subset_image hφ (mem_dom_self hφ.lt) ht')

/-- Lemma 2.16: `φ̂` is continuous on the image. It is monotone, and maps the image onto the
interval `[τ, T)`. -/
theorem continuousOn_solInv : ContinuousOn (solInv φ τ T) (φ '' Dom τ T) := by
  rintro _ ⟨t, ht, rfl⟩
  have hm := strictMonoOn_solution hf hpos hφ
  have hmono := (strictMonoOn_solInv hf hpos hφ).monotoneOn
  have himg := solInv_image hf hpos hφ
  obtain ⟨t', ht', htt'⟩ := exists_dom_gt ht
  have hD : ∀ a ∈ Dom τ T, ∀ b ∈ Dom τ T, Icc a b ⊆ Dom τ T := fun a ha b hb u hu =>
    ⟨ha.1.trans hu.1, (EReal.coe_le_coe_iff.mpr hu.2).trans_lt hb.2⟩
  have hright : ContinuousWithinAt (solInv φ τ T) (Ici (φ t)) (φ t) := by
    refine continuousWithinAt_right_of_monotoneOn_of_image_mem_nhdsWithin hmono
      (mem_of_superset (Icc_mem_nhdsGE (hm ht ht' htt')) (Icc_subset_image hφ ht ht')) ?_
    rw [himg, solInv_apply hf hpos hφ ht]
    exact mem_of_superset (Icc_mem_nhdsGE htt') (hD t ht t' ht')
  rcases eq_or_lt_of_le ht.1 with hτt | hτt
  · -- at the start, the image lies to the right of `φ (τ)`
    refine hright.mono fun x ⟨s, hs, hsx⟩ => ?_
    rw [← hsx, ← hτt]
    exact hm.monotoneOn (mem_dom_self hφ.lt) hs hs.1
  · have hleft : ContinuousWithinAt (solInv φ τ T) (Iic (φ t)) (φ t) := by
      refine continuousWithinAt_left_of_monotoneOn_of_image_mem_nhdsWithin hmono
        (mem_of_superset (Icc_mem_nhdsLE (hm (mem_dom_self hφ.lt) ht hτt))
          (Icc_subset_image hφ (mem_dom_self hφ.lt) ht)) ?_
      rw [himg, solInv_apply hf hpos hφ ht]
      exact mem_of_superset (Icc_mem_nhdsLE hτt) (hD τ (mem_dom_self hφ.lt) t ht)
    exact (continuousAt_iff_continuous_left_right.mpr ⟨hleft, hright⟩).continuousWithinAt

omit hf hpos in
theorem hasDerivAt_of_interior {t : ℝ} (ht : t ∈ Dom τ T) (hτt : τ < t) :
    HasDerivAt φ (f t (φ t)) t := by
  obtain ⟨t', ht', htt'⟩ := exists_dom_gt ht
  refine (hφ.deriv t ht).hasDerivAt (mem_of_superset (Ioo_mem_nhds hτt htt') fun u hu => ?_)
  exact ⟨hu.1.le, (EReal.coe_lt_coe_iff.mpr hu.2).trans ht'.2⟩

/-- Lemma 2.16: where `φ' (t) > 0`, `t > τ`, the inverse is differentiable at `φ (t)`, with
`φ̂' (φ (t)) = 1 / φ' (t)`. -/
theorem hasDerivAt_solInv {t : ℝ} (ht : t ∈ Dom τ T) (hτt : τ < t) (hft : 0 < f t (φ t)) :
    HasDerivAt (solInv φ τ T) (f t (φ t))⁻¹ (φ t) := by
  have hnhds := image_mem_nhds hf hpos hφ ht hτt
  have hcont : ContinuousAt (solInv φ τ T) (φ t) :=
    (continuousOn_solInv hf hpos hφ).continuousAt hnhds
  have hd : HasDerivAt φ (f t (φ t)) (solInv φ τ T (φ t)) := by
    rw [solInv_apply hf hpos hφ ht]; exact hasDerivAt_of_interior hφ ht hτt
  refine HasDerivAt.of_local_left_inverse hcont hd hft.ne' ?_
  filter_upwards [hnhds] with y hy using apply_solInv hy

/-- Lemma 2.16, conversely: if the inverse is differentiable at `φ (t)`, `t > τ`, then
`φ' (t) > 0` and `φ' (t) φ̂' (φ (t)) = 1`. -/
theorem pos_of_hasDerivAt_solInv {t d : ℝ} (ht : t ∈ Dom τ T) (hτt : τ < t)
    (hd : HasDerivAt (solInv φ τ T) d (φ t)) : 0 < f t (φ t) ∧ f t (φ t) * d = 1 := by
  have hnhds := image_mem_nhds hf hpos hφ ht hτt
  have hφd : HasDerivAt φ (f t (φ t)) (solInv φ τ T (φ t)) := by
    rw [solInv_apply hf hpos hφ ht]; exact hasDerivAt_of_interior hφ ht hτt
  have hcomp := hφd.comp (φ t) hd
  have hid : HasDerivAt (φ ∘ solInv φ τ T) 1 (φ t) :=
    (hasDerivAt_id (φ t)).congr_of_eventuallyEq (by
      filter_upwards [hnhds] with y hy using apply_solInv hy)
  have h1 := hcomp.unique hid
  refine ⟨lt_of_le_of_ne (nonneg_along hf hpos hφ ht) fun h => ?_, h1⟩
  rw [← h, zero_mul] at h1
  exact zero_ne_one h1

/-- Lemma 2.16, Lebesgue's theorem: on `[a, b]` in the image, `φ̂` is differentiable almost
everywhere, and `φ̂ (b) - φ̂ (a) ≥ ∫_a^b φ̂'`. -/
theorem solInv_lebesgue {a b : ℝ} (ha : a ∈ φ '' Dom τ T) (hb : b ∈ φ '' Dom τ T) (hab : a ≤ b) :
    (∀ᵐ x, x ∈ Ioo a b → DifferentiableAt ℝ (solInv φ τ T) x) ∧
      ∫ x in a..b, deriv (solInv φ τ T) x ≤ solInv φ τ T b - solInv φ τ T a := by
  have hsub : Icc a b ⊆ φ '' Dom τ T := (ordConnected_image hφ).out ha hb
  have hmono : MonotoneOn (solInv φ τ T) (Icc a b) :=
    (strictMonoOn_solInv hf hpos hφ).monotoneOn.mono hsub
  refine ⟨?_, ?_⟩
  · filter_upwards [hmono.ae_differentiableWithinAt_of_mem] with x hx hxab
    exact (hx (Ioo_subset_Icc_self hxab)).differentiableAt (Icc_mem_nhds hxab.1 hxab.2)
  · have hmono' : MonotoneOn (solInv φ τ T) (uIcc a b) := by rw [uIcc_of_le hab]; exact hmono
    have h := hmono'.intervalIntegral_deriv_mem_uIcc
    have hle : solInv φ τ T a ≤ solInv φ τ T b := hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
    rw [uIcc_of_le (sub_nonneg.mpr hle)] at h
    exact h.2

/-- Lemma 2.16: if `φ̂` is differentiable on `[a, b]` off finitely many points, it is absolutely
continuous there with `φ̂ (b) - φ̂ (a) = ∫_a^b φ̂'`, and `φ' > 0` almost everywhere on
`[φ̂ (a), φ̂ (b)]`. -/
theorem solInv_absolutelyContinuous {a b : ℝ} (ha : a ∈ φ '' Dom τ T) (hb : b ∈ φ '' Dom τ T)
    (hab : a ≤ b) {s : Set ℝ} (hs : s.Finite)
    (hdiff : ∀ x ∈ Ioo a b \ s, DifferentiableAt ℝ (solInv φ τ T) x) :
    ∫ x in a..b, deriv (solInv φ τ T) x = solInv φ τ T b - solInv φ τ T a ∧
      AbsolutelyContinuousOnInterval (solInv φ τ T) a b ∧
      ∀ᵐ t, t ∈ Icc (solInv φ τ T a) (solInv φ τ T b) → 0 < f t (φ t) := by
  set ψ := solInv φ τ T with hψ
  have hsub : Icc a b ⊆ φ '' Dom τ T := (ordConnected_image hφ).out ha hb
  have hmonoI := (strictMonoOn_solInv hf hpos hφ).monotoneOn
  have hcont := continuousOn_solInv hf hpos hφ
  -- the fundamental theorem of calculus on `[a, x]`, for `x ∈ [a, b]`
  have hFTC : ∀ x ∈ Icc a b, ∫ u in a..x, deriv ψ u = ψ x - ψ a := by
    intro x hx
    have hsubx : Icc a x ⊆ φ '' Dom τ T := (Icc_subset_Icc_right hx.2).trans hsub
    refine integral_eq_of_hasDerivAt_off_countable_of_le ψ (deriv ψ) hx.1 hs.countable
      (hcont.mono hsubx) (fun u hu => (hdiff u ⟨⟨hu.1.1, hu.1.2.trans_le hx.2⟩, hu.2⟩).hasDerivAt)
      ?_
    exact (show MonotoneOn ψ (uIcc a x) by rw [uIcc_of_le hx.1]; exact hmonoI.mono hsubx)
      |>.intervalIntegrable_deriv
  refine ⟨hFTC b ⟨hab, le_rfl⟩, ?_, ?_⟩
  · -- `ψ = ψ (a) + ∫_a^x ψ'`, the sum of a constant and an indefinite integral
    have hint : IntervalIntegrable (deriv ψ) volume a b :=
      (show MonotoneOn ψ (uIcc a b) by rw [uIcc_of_le hab]; exact hmonoI.mono hsub)
        |>.intervalIntegrable_deriv
    have hac := ((LipschitzWith.const (ψ a)).lipschitzOnWith (s := uIcc a b)
      |>.absolutelyContinuousOnInterval).add
      (hint.absolutelyContinuousOnInterval_intervalIntegral (left_mem_uIcc (a := a) (b := b)))
    refine hac.congr fun x hx => ?_
    rw [uIcc_of_le hab] at hx
    simp only [Pi.add_apply]
    rw [hFTC x hx]
    ring
  · -- off the finitely many times `ψ (s)` and the endpoints, `ψ` is differentiable at `φ (t)`
    have hE : (ψ '' s ∪ {ψ a, ψ b}).Countable :=
      ((hs.image ψ).union ((finite_singleton _).insert _)).countable
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hE.measure_zero volume)] with t hE ht
    simp only [mem_union, mem_image, mem_insert_iff, mem_singleton_iff, not_or] at hE
    obtain ⟨hts, hta, htb⟩ := hE
    have hta' : ψ a < t := lt_of_le_of_ne ht.1 (Ne.symm hta)
    have htb' : t < ψ b := lt_of_le_of_ne ht.2 htb
    have htD : t ∈ Dom τ T := ⟨(solInv_mem ha).1.trans hta'.le,
      (EReal.coe_le_coe_iff.mpr htb'.le).trans_lt (solInv_mem hb).2⟩
    have hm := strictMonoOn_solution hf hpos hφ
    have hx1 : a < φ t := by
      have := hm (solInv_mem ha) htD hta'
      rwa [apply_solInv ha] at this
    have hx2 : φ t < b := by
      have := hm htD (solInv_mem hb) htb'
      rwa [apply_solInv hb] at this
    have hxs : φ t ∉ s := fun h => hts ⟨φ t, h, solInv_apply hf hpos hφ htD⟩
    have hτt : τ < t := lt_of_le_of_lt (solInv_mem ha).1 hta'
    exact (pos_of_hasDerivAt_solInv hf hpos hφ htD hτt
      (hdiff (φ t) ⟨⟨hx1, hx2⟩, hxs⟩).hasDerivAt).1

end

end PathwiseVolatility
