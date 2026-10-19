/-
Copyright (c) 2026 Ryan McCrickerd. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCrickerd
-/
import PathwiseVolatility.Bounds

/-!
# Section 2.2: driving functions' zeros

Lemma 2.3 (Path of zeros): `ϕ (x) = sup {t : f (t, x) < 0}` is continuous into `[-∞, ∞]`, with
`f (ϕ (x), x) = 0` where it is finite. Lemma 2.4 (Càdlàg zeros): the bound
`φ̄ (t) = inf {x > ξ : f (t, x) < 0}` is the exit time `E (ϕ)`, is non-decreasing and càdlàg, and
where it is finite it is a zero of `f (t, ·)` and strictly increasing. The properties of `φ̄` are
proved from its definition directly, not through `ϕ`.
-/

open Set Filter Topology

namespace PathwiseVolatility

variable {f : ℝ → ℝ → ℝ} {τ ξ : ℝ}

/-- If `f (t, x) < 0` at a level `x > ξ`, then also at some level in `(ξ, x)`. -/
theorem exists_below_of_neg (hf : InF f) {t x : ℝ} (hξx : ξ < x) (hfx : f t x < 0) :
    ∃ y, ξ < y ∧ y < x ∧ f t y < 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp
    (isOpen_lt (hf.continuous_level t) continuous_const) x hfx
  have hm : 0 < min ε (x - ξ) := lt_min hε (by linarith)
  refine ⟨x - min ε (x - ξ) / 2, by linarith [min_le_right ε (x - ξ)], by linarith, hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [min_le_left ε (x - ξ)]

theorem upperBound_le {t x : ℝ} (hξx : ξ < x) (hfx : f t x < 0) : upperBound f ξ t ≤ x :=
  iInf₂_le (f := fun (x : ℝ) (_ : ξ < x ∧ f t x < 0) => (x : EReal)) x ⟨hξx, hfx⟩

/-- Lemma 2.4, monotonicity: `φ̄` is non-decreasing. -/
theorem upperBound_mono (hf : InF f) {s t : ℝ} (hst : s ≤ t) :
    upperBound f ξ s ≤ upperBound f ξ t := by
  refine le_iInf₂ fun x hx => upperBound_le hx.1 ?_
  exact lt_of_le_of_lt (hf.mono x hst) hx.2

/-- Where `φ̄ (t) = x` is finite, `f (t, x) ≤ 0`: otherwise `f (t, ·) > 0` near `x`, and `φ̄ (t)`
would be above `x`. -/
theorem f_upperBound_nonpos (hf : InF f) {t x : ℝ} (hx : upperBound f ξ t = x) : f t x ≤ 0 := by
  have hbelow : ∀ y, ξ < y → f t y < 0 → x ≤ y := le_upperBound_iff.mp hx.symm.le
  by_contra hgt
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp
    (isOpen_lt continuous_const (hf.continuous_level t)) x (not_le.mp hgt)
  have : ((x + ε : ℝ) : EReal) ≤ upperBound f ξ t := by
    rw [le_upperBound_iff]
    intro y hy hfy
    have hxy := hbelow y hy hfy
    by_contra hlt
    have hyb : y ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
    exact absurd (hball hyb) (not_lt.mpr hfy.le)
  rw [hx, EReal.coe_le_coe_iff] at this
  linarith

/-- Lemma 2.4: at a time `t ≥ τ` where `φ̄ (t) = x` is finite, `f (t, x) = 0`. -/
theorem f_upperBound_eq_zero (hf : InF f) (hnn : 0 ≤ f τ ξ) {t x : ℝ} (ht : τ ≤ t)
    (hx : upperBound f ξ t = x) : f t x = 0 := by
  have hbelow : ∀ y, ξ < y → f t y < 0 → x ≤ y := le_upperBound_iff.mp hx.symm.le
  have hξx : ξ ≤ x := by
    have h' : (ξ : EReal) ≤ upperBound f ξ t := le_upperBound_iff.mpr fun y hy _ => hy.le
    rw [hx] at h'
    exact EReal.coe_le_coe_iff.mp h'
  refine le_antisymm (f_upperBound_nonpos hf hx) (not_lt.mp fun hneg => ?_)
  rcases eq_or_lt_of_le hξx with h | h
  · rw [← h] at hneg
    linarith [hf.mono ξ ht]
  · obtain ⟨y, hy, hyx, hfy⟩ := exists_below_of_neg hf h hneg
    linarith [hbelow y hy hfy]

/-- Where `f (t, ξ) > 0` and `φ̄ (t) = x` is finite, `x > ξ`. -/
theorem lt_of_upperBound_eq (hf : InF f) {t x : ℝ} (hξ : 0 < f t ξ)
    (hx : upperBound f ξ t = x) : ξ < x := by
  have h' : (ξ : EReal) ≤ upperBound f ξ t := le_upperBound_iff.mpr fun y hy _ => hy.le
  rw [hx] at h'
  refine lt_of_le_of_ne (EReal.coe_le_coe_iff.mp h') fun h => ?_
  have := f_upperBound_nonpos hf hx
  rw [← h] at this
  linarith

/-- Lemma 2.4, strict increase: for `τ ≤ s < t`, `φ̄ (s) < φ̄ (t)` wherever `φ̄ (t) < ∞`. -/
theorem upperBound_lt (hf : InF f) (hnn : 0 ≤ f τ ξ) {s t : ℝ} (hs : τ ≤ s) (hst : s < t)
    (hfin : upperBound f ξ t < ⊤) : upperBound f ξ s < upperBound f ξ t := by
  have hbot : upperBound f ξ t ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot ξ) (le_upperBound_iff.mpr fun y hy _ => hy.le)
  have hx := EReal.coe_toReal hfin.ne hbot
  have hzero := f_upperBound_eq_zero hf hnn (hs.trans hst.le) hx.symm
  have hξx : ξ < (upperBound f ξ t).toReal := lt_of_upperBound_eq hf
    (lt_of_le_of_lt hnn (by have := hf.strictMono ξ (hs.trans_lt hst); simpa using this)) hx.symm
  have hneg : f s (upperBound f ξ t).toReal < 0 := by
    have := hf.strictMono (upperBound f ξ t).toReal hst
    simp only at this
    linarith
  obtain ⟨y, hy, hyx, hfy⟩ := exists_below_of_neg hf hξx hneg
  rw [← hx]
  exact lt_of_le_of_lt (upperBound_le hy hfy) (EReal.coe_lt_coe_iff.mpr hyx)

/-! ### Lemma 2.3: the path of zeros -/

/-- The path of zeros of Lemma 2.3, `ϕ (x) = sup {t : f (t, x) < 0}` in `[-∞, ∞]`, with
`sup ∅ = -∞`. -/
noncomputable def zeroPath (f : ℝ → ℝ → ℝ) (x : ℝ) : EReal :=
  ⨆ t ∈ {t : ℝ | f t x < 0}, (t : EReal)

theorem le_zeroPath {x t : ℝ} (h : f t x < 0) : (t : EReal) ≤ zeroPath f x :=
  le_iSup₂ (f := fun (t : ℝ) (_ : f t x < 0) => (t : EReal)) t h

theorem lt_zeroPath_iff {x : ℝ} {a : EReal} :
    a < zeroPath f x ↔ ∃ t : ℝ, a < t ∧ f t x < 0 := by
  rw [zeroPath, lt_biSup_iff]
  constructor <;> rintro ⟨t, h1, h2⟩ <;> exact ⟨t, h2, h1⟩

theorem zeroPath_le_of_nonneg (hf : InF f) {x t : ℝ} (h : 0 ≤ f t x) : zeroPath f x ≤ t := by
  refine iSup₂_le fun s (hs : f s x < 0) => EReal.coe_le_coe_iff.mpr ?_
  by_contra hlt
  have := hf.strictMono x (not_le.mp hlt)
  simp only at this
  linarith

theorem zeroPath_lt_iff (hf : InF f) {x : ℝ} {a : EReal} :
    zeroPath f x < a ↔ ∃ t : ℝ, (t : EReal) < a ∧ 0 < f t x := by
  constructor
  · intro h
    obtain ⟨r, h1, h2⟩ := EReal.lt_iff_exists_real_btwn.mp h
    obtain ⟨r', h3, h4⟩ := EReal.lt_iff_exists_real_btwn.mp h1
    have hr' : 0 ≤ f r' x := not_lt.mp fun hneg => absurd (le_zeroPath hneg) (not_le.mpr h3)
    have := hf.strictMono x (EReal.coe_lt_coe_iff.mp h4)
    simp only at this
    exact ⟨r, h2, by linarith⟩
  · rintro ⟨t, hta, hpos⟩
    exact (zeroPath_le_of_nonneg hf hpos.le).trans_lt hta

/-- Lemma 2.3 (Path of zeros): `ϕ` is continuous into `[-∞, ∞]`. -/
theorem continuous_zeroPath (hf : InF f) : Continuous (zeroPath f) := by
  rw [OrderTopology.continuous_iff]
  intro a
  constructor
  · refine isOpen_iff_mem_nhds.mpr fun x hx => ?_
    obtain ⟨t, hat, htx⟩ := lt_zeroPath_iff.mp (show a < zeroPath f x from hx)
    filter_upwards [(hf.continuous_level t).continuousAt.eventually (gt_mem_nhds htx)] with y hy
    exact lt_zeroPath_iff.mpr ⟨t, hat, hy⟩
  · refine isOpen_iff_mem_nhds.mpr fun x hx => ?_
    obtain ⟨t, hta, htx⟩ := (zeroPath_lt_iff hf).mp (show zeroPath f x < a from hx)
    filter_upwards [(hf.continuous_level t).continuousAt.eventually (lt_mem_nhds htx)] with y hy
    exact (zeroPath_lt_iff hf).mpr ⟨t, hta, hy⟩

/-- Lemma 2.3 (Path of zeros): `f (ϕ (x), x) = 0` wherever `ϕ (x)` is finite. -/
theorem f_zeroPath_eq_zero (hf : InF f) {x r : ℝ} (hr : zeroPath f x = r) : f r x = 0 := by
  apply le_antisymm
  · by_contra hpos
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp
      (isOpen_lt continuous_const (hf.continuous_time x)) r (not_le.mp hpos)
    have hmem : r - δ / 2 ∈ Metric.ball r δ := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
    have := zeroPath_le_of_nonneg hf (le_of_lt (hball hmem))
    rw [hr, EReal.coe_le_coe_iff] at this
    linarith
  · by_contra hneg
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp
      (isOpen_lt (hf.continuous_time x) continuous_const) r (not_le.mp hneg)
    have hmem : r + δ / 2 ∈ Metric.ball r δ := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
    have := le_zeroPath (f := f) (hball hmem)
    rw [hr, EReal.coe_le_coe_iff] at this
    linarith

/-! ### Lemma 2.4: the exit time and càdlàg paths -/

/-- The exit time of eq. (2.8), `E (g) (t) = inf {x > ξ : g (x) > t}`, with `inf ∅ = ∞`. -/
noncomputable def exitTime (g : ℝ → EReal) (ξ t : ℝ) : EReal :=
  ⨅ x ∈ {x : ℝ | ξ < x ∧ (t : EReal) < g x}, (x : EReal)

/-- `ϕ (x) > t` exactly when `f (t, x) < 0`. -/
theorem lt_zeroPath_iff_neg (hf : InF f) {t x : ℝ} : (t : EReal) < zeroPath f x ↔ f t x < 0 := by
  rw [lt_zeroPath_iff]
  constructor
  · rintro ⟨s, hts, hs⟩
    have := hf.strictMono x (EReal.coe_lt_coe_iff.mp hts)
    simp only at this
    linarith
  · intro h
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp
      (isOpen_lt (hf.continuous_time x) continuous_const) t h
    refine ⟨t + δ / 2, EReal.coe_lt_coe_iff.mpr (by linarith), hball ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith

/-- Lemma 2.4 (Càdlàg zeros): `φ̄ = E (ϕ)`. -/
theorem upperBound_eq_exitTime (hf : InF f) (t : ℝ) :
    upperBound f ξ t = exitTime (zeroPath f) ξ t := by
  have h : {x : ℝ | ξ < x ∧ f t x < 0} = {x : ℝ | ξ < x ∧ (t : EReal) < zeroPath f x} := by
    ext x
    simp only [mem_ofPred_eq, lt_zeroPath_iff_neg hf]
  rw [upperBound, exitTime, h]

/-- Lemma 2.4: `φ̄` takes values in `[ξ, ∞]`. -/
theorem le_upperBound (t : ℝ) : (ξ : EReal) ≤ upperBound f ξ t :=
  le_upperBound_iff.mpr fun _ hy _ => hy.le

/-- Lemma 2.4 (Càdlàg zeros): `φ̄` is right-continuous. -/
theorem upperBound_continuousWithinAt (hf : InF f) (t : ℝ) :
    ContinuousWithinAt (upperBound f ξ) (Ici t) t := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · exact eventually_nhdsWithin_of_forall fun s hs => ha.trans_le (upperBound_mono hf hs)
  · obtain ⟨x, hx⟩ := iInf_lt_iff.mp (show upperBound f ξ t < a from ha)
    obtain ⟨⟨hξx, hfx⟩, hxa⟩ := iInf_lt_iff.mp hx
    filter_upwards [nhdsWithin_le_nhds
      ((hf.continuous_time x).continuousAt.eventually (gt_mem_nhds hfx))] with s hs
    exact (upperBound_le hξx hs).trans_lt hxa

/-- Lemma 2.4 (Càdlàg zeros): `φ̄` has a left limit at every time. -/
theorem upperBound_tendsto_left (hf : InF f) (t : ℝ) :
    ∃ l, Tendsto (upperBound f ξ) (𝓝[<] t) (𝓝 l) :=
  ⟨_, Monotone.tendsto_nhdsLT (fun _ _ h => upperBound_mono hf h) t⟩

end PathwiseVolatility
