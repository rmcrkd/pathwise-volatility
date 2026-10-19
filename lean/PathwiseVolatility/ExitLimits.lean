/-
Copyright (c) 2026 Ryan McCrickerd. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCrickerd
-/
import PathwiseVolatility.ExitTime
import PathwiseVolatility.InverseSolution

/-!
# Section 3.4: uniform exit-time solution limits

For `g ∈ G`, the bound `φ̄ (t) = inf {x > 0 : g (t, x) < 0}` and the path of zeros
`ϕ (x) = sup {t ≥ 0 : g (t, x) < 0}` of eq. (3.28), with `sup ∅ = 0`, and Corollary 3.15 (Exit-time
lower bound): `E (ϕ) = φ̄`, `E (φ̄) = M (ϕ)` and `M (ϕ) = E (φ̄) ≤ E (φ) = φ⁻¹`.
-/

open Set Filter Topology

namespace PathwiseVolatility

/-- The bound of eq. (3.28), `φ̄ (t) = inf {x > 0 : g (t, x) < 0}`. -/
noncomputable def barG (g : ℝ → ℝ → ℝ) (t : ℝ) : ℝ := sInf {x | 0 < x ∧ g t x < 0}

/-- The path of zeros of eq. (3.28), `ϕ (x) = sup {t ≥ 0 : g (t, x) < 0}`, with `sup ∅ = 0`. -/
noncomputable def zeroG (g : ℝ → ℝ → ℝ) (x : ℝ) : ℝ := sSup {t | 0 ≤ t ∧ g t x < 0}

variable {g : ℝ → ℝ → ℝ}

theorem InG.continuousOn_time (hg : InG g) {x : ℝ} (hx : 0 ≤ x) :
    ContinuousOn (fun t => g t x) (Ici 0) :=
  hg.continuousOn.comp (continuousOn_id.prodMk continuousOn_const) fun _ ht => ⟨ht, hx⟩

theorem InG.continuousOn_level (hg : InG g) {t : ℝ} (ht : 0 ≤ t) :
    ContinuousOn (fun x => g t x) (Ici 0) :=
  hg.continuousOn.comp (continuousOn_const.prodMk continuousOn_id) fun _ hx => ⟨ht, hx⟩

theorem InG.lt_of_lt (hg : InG g) {s t x : ℝ} (hs : 0 ≤ s) (hx : 0 ≤ x) (hst : s < t) :
    g s x < g t x := by
  have := hg.strictMonoOn x hx (mem_Ici.mpr hs) (mem_Ici.mpr (hs.trans hst.le)) hst
  simpa using this

theorem InG.bddAbove_neg (hg : InG g) {x : ℝ} (hx : 0 ≤ x) : BddAbove {t | 0 ≤ t ∧ g t x < 0} := by
  obtain ⟨t₁, ht₁, hpos⟩ := hg.exists_pos x hx
  refine ⟨t₁, fun t ht => ?_⟩
  by_contra hlt
  push Not at hlt
  linarith [hg.lt_of_lt ht₁ hx hlt, ht.2]

theorem zeroG_nonneg (g : ℝ → ℝ → ℝ) (x : ℝ) : 0 ≤ zeroG g x :=
  Real.sSup_nonneg fun _ ht => ht.1

/-- For `t, x ≥ 0`, `t < ϕ (x)` exactly when `g (t, x) < 0`. -/
theorem InG.lt_zeroG_iff (hg : InG g) {t x : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) :
    t < zeroG g x ↔ g t x < 0 := by
  constructor
  · intro h
    have hne : {s | 0 ≤ s ∧ g s x < 0}.Nonempty := by
      by_contra hemp
      rw [not_nonempty_iff_eq_empty] at hemp
      rw [zeroG, hemp, Real.sSup_empty] at h
      linarith
    obtain ⟨s, hs, hts⟩ := exists_lt_of_lt_csSup hne h
    linarith [hg.lt_of_lt ht hx hts, hs.2]
  · intro h
    obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.mp
      ((hg.continuousOn_time hx) t (mem_Ici.mpr ht)) (-(g t x)) (by linarith)
    have hmem : t + δ / 2 ∈ {s | 0 ≤ s ∧ g s x < 0} := by
      refine ⟨by linarith, ?_⟩
      have := hball (mem_Ici.mpr (by linarith : (0 : ℝ) ≤ t + δ / 2))
        (by rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (by linarith)]; linarith)
      rw [Real.dist_eq] at this
      linarith [le_abs_self (g (t + δ / 2) x - g t x)]
    exact lt_of_lt_of_le (by linarith) (le_csSup (hg.bddAbove_neg hx) hmem)

/-- If `g (s, x) > 0`, then `ϕ (x) ≤ s`. -/
theorem InG.zeroG_le_of_pos (hg : InG g) {s x : ℝ} (hs : 0 ≤ s) (hx : 0 ≤ x) (hpos : 0 < g s x) :
    zeroG g x ≤ s :=
  Real.sSup_le (fun t ht => by
    by_contra hlt
    push Not at hlt
    linarith [hg.lt_of_lt hs hx hlt, ht.2]) hs

/-- At `ϕ (x)`, `g ≥ 0`. -/
theorem InG.nonneg_at_zeroG (hg : InG g) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ g (zeroG g x) x :=
  not_lt.mp fun h => lt_irrefl _ ((hg.lt_zeroG_iff (zeroG_nonneg g x) hx).mpr h)

/-- Where `ϕ (x) > 0`, `g (ϕ (x), x) ≤ 0`, so `g (ϕ (x), x) = 0`. -/
theorem InG.nonpos_at_zeroG (hg : InG g) {x : ℝ} (hx : 0 ≤ x) (hpos : 0 < zeroG g x) :
    g (zeroG g x) x ≤ 0 := by
  by_contra hgt
  push Not at hgt
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.mp
    ((hg.continuousOn_time hx) _ (mem_Ici.mpr (zeroG_nonneg g x))) (g (zeroG g x) x) hgt
  set s := zeroG g x - min δ (zeroG g x) / 2 with hs
  have hm : 0 < min δ (zeroG g x) := lt_min hδ hpos
  have hs0 : 0 ≤ s := by linarith [min_le_right δ (zeroG g x)]
  have h1 := hball (mem_Ici.mpr hs0) (by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [min_le_left δ (zeroG g x)])
  rw [Real.dist_eq] at h1
  have := hg.zeroG_le_of_pos hs0 hx (by linarith [neg_abs_le (g s x - g (zeroG g x) x)])
  linarith

/-- The path of zeros is continuous on `ℝ₊`. -/
theorem InG.continuousOn_zeroG (hg : InG g) : ContinuousOn (zeroG g) (Ici 0) := by
  intro x hx
  have hx' : (0 : ℝ) ≤ x := hx
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · rcases lt_or_ge a 0 with ha0 | ha0
    · exact eventually_nhdsWithin_of_forall fun y _ => lt_of_lt_of_le ha0 (zeroG_nonneg g y)
    · have hneg := (hg.lt_zeroG_iff ha0 hx').mp ha
      filter_upwards [((hg.continuousOn_level ha0) x hx).eventually (gt_mem_nhds hneg),
        self_mem_nhdsWithin] with y hy hy0
      exact (hg.lt_zeroG_iff ha0 hy0).mpr hy
  · set s := (zeroG g x + a) / 2 with hs
    set s' := (zeroG g x + s) / 2 with hs'
    have hz := zeroG_nonneg g x
    have h1 : 0 ≤ g s' x := not_lt.mp fun h => by
      have := (hg.lt_zeroG_iff (by linarith) hx').mpr h; linarith
    have hpos : 0 < g s x := lt_of_le_of_lt h1 (hg.lt_of_lt (by linarith) hx' (by linarith))
    filter_upwards [((hg.continuousOn_level (by linarith : (0 : ℝ) ≤ s)) x hx).eventually
      (lt_mem_nhds hpos), self_mem_nhdsWithin] with y hy hy0
    exact lt_of_le_of_lt (hg.zeroG_le_of_pos (by linarith) hy0 hy) (by linarith)

/-- `g (t, ·)` is negative somewhere above `0`, at every `t ≥ 0`; the bound's set is not empty. -/
theorem InG.nonempty_neg (hg : InG g) {t : ℝ} (ht : 0 ≤ t) : {x | 0 < x ∧ g t x < 0}.Nonempty := by
  obtain ⟨x, hx, hneg⟩ := hg.exists_neg t ht
  refine ⟨x, lt_of_le_of_ne hx fun h => ?_, hneg⟩
  rw [← h] at hneg
  rcases eq_or_lt_of_le ht with h0 | h0
  · rw [← h0] at hneg; linarith [hg.nonneg_zero]
  · linarith [hg.lt_of_lt le_rfl le_rfl h0, hg.nonneg_zero]

/-- Corollary 3.15: `E (ϕ) = φ̄` on `ℝ₊`. -/
theorem InG.exitT_zeroG (hg : InG g) {t : ℝ} (ht : 0 ≤ t) : exitT (zeroG g) t = barG g t := by
  have h : {x | 0 < x ∧ t < zeroG g x} = {x | 0 < x ∧ g t x < 0} := by
    ext x
    exact ⟨fun h => ⟨h.1, (hg.lt_zeroG_iff ht h.1.le).mp h.2⟩,
      fun h => ⟨h.1, (hg.lt_zeroG_iff ht h.1.le).mpr h.2⟩⟩
  rw [exitT, barG, h]

/-- The supremum `M (ϕ) (x)` bounds `ϕ` on `[0, x]`, and is the least such bound. -/
theorem InG.zeroG_le_supF (hg : InG g) {x y : ℝ} (hy : y ∈ Icc 0 x) : zeroG g y ≤ supF (zeroG g) x :=
  (le_max_right _ _).trans (le_csSup ((isCompact_Icc.image_of_continuousOn
    (ContinuousOn.sup continuousOn_const (hg.continuousOn_zeroG.mono Icc_subset_Ici_self))).bddAbove)
    ⟨y, hy, rfl⟩)

theorem supF_nonneg (φ : ℝ → ℝ) (x : ℝ) : 0 ≤ supF φ x :=
  Real.sSup_nonneg fun _ ⟨_, _, h⟩ => h ▸ le_max_left _ _

/-- If `φ̄ (t) > x` at `t > 0`, then `M (ϕ) (x) ≤ t`. -/
theorem InG.supF_le_of_lt_barG (hg : InG g) {x t : ℝ} (hx : 0 ≤ x) (ht : 0 < t)
    (hxt : x < barG g t) : supF (zeroG g) x ≤ t := by
  refine csSup_le ⟨_, 0, ⟨le_rfl, hx⟩, rfl⟩ ?_
  rintro _ ⟨y, hy, rfl⟩
  refine max_le ht.le (not_lt.mp fun hlt => ?_)
  have hneg := (hg.lt_zeroG_iff ht.le hy.1).mp hlt
  rcases eq_or_lt_of_le hy.1 with h0 | h0
  · rw [← h0] at hneg; linarith [hg.lt_of_lt le_rfl le_rfl ht, hg.nonneg_zero]
  · have hle : barG g t ≤ y := csInf_le ⟨0, fun _ hy => hy.1.le⟩ ⟨h0, hneg⟩
    linarith [hy.2]

/-- If `M (ϕ) (x) < t`, then `φ̄ (t) > x`: by continuity, `ϕ < t` a little beyond `x` too. -/
theorem InG.lt_barG_of_supF_lt (hg : InG g) {x t : ℝ} (hx : 0 ≤ x)
    (hMt : supF (zeroG g) x < t) : x < barG g t := by
  have ht0 : 0 ≤ t := (supF_nonneg _ x).trans hMt.le
  have hzx : zeroG g x < t := lt_of_le_of_lt (hg.zeroG_le_supF ⟨hx, le_rfl⟩) hMt
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.mp (hg.continuousOn_zeroG x hx)
    (t - zeroG g x) (by linarith)
  refine lt_of_lt_of_le (show x < x + δ / 2 by linarith)
    (le_csInf (hg.nonempty_neg ht0) fun y hy => not_lt.mp fun hyx => ?_)
  have hzy : zeroG g y < t := by
    rcases le_total y x with hyx' | hyx'
    · exact lt_of_le_of_lt (hg.zeroG_le_supF ⟨hy.1.le, hyx'⟩) hMt
    · have := hball (mem_Ici.mpr hy.1.le)
        (by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith)
      rw [Real.dist_eq] at this
      linarith [le_abs_self (zeroG g y - zeroG g x)]
  exact absurd ((hg.lt_zeroG_iff ht0 hy.1.le).mpr hy.2) (not_lt.mpr hzy.le)

/-- Corollary 3.15: `E (φ̄) = M (ϕ)` on `ℝ₊`. For `t > 0`, `φ̄ (t) > x` exactly when `ϕ ≤ t` on
`[0, x]` and a little beyond. -/
theorem InG.exitT_barG (hg : InG g) {x : ℝ} (hx : 0 ≤ x) : exitT (barG g) x = supF (zeroG g) x := by
  set M := supF (zeroG g) x with hM
  have hM0 : 0 ≤ M := supF_nonneg _ x
  have hmem : ∀ ε > 0, M + ε ∈ {t | 0 < t ∧ x < barG g t} := fun ε hε =>
    ⟨by linarith, hg.lt_barG_of_supF_lt hx (by linarith)⟩
  refine le_antisymm (le_of_forall_pos_lt_add fun ε hε => ?_)
    (le_csInf ⟨_, hmem 1 one_pos⟩ fun t ht => hg.supF_le_of_lt_barG hx ht.1 ht.2)
  exact lt_of_le_of_lt (csInf_le ⟨0, fun _ ht => ht.1.le⟩ (hmem (ε / 2) (by linarith)))
    (by linarith)

/-- A global solution lies below `φ̄`. -/
theorem InG.le_barG (hg : InG g) {φ : ℝ → ℝ} (hφ : IsGlobalSolution g φ) {t : ℝ} (ht : 0 ≤ t) :
    φ t ≤ barG g t := by
  have h := solution_le_upperBound hg.inF_extendG (hg.isGlobalSolution_iff.mp hφ)
    (by rw [dom_top]; exact ht)
  refine le_csInf (hg.nonempty_neg ht) fun y hy => le_upperBound_iff.mp h y hy.1 ?_
  rw [extendG_of_nonneg ht hy.1.le]; exact hy.2

/-- Corollary 3.15 (Exit-time lower bound): `M (ϕ) = E (φ̄) ≤ E (φ) = φ⁻¹` on `ℝ₊`. -/
theorem InG.exitT_barG_le (hg : InG g) {φ : ℝ → ℝ} (hφ : IsGlobalSolution g φ) {x : ℝ}
    (hx : 0 ≤ x) : supF (zeroG g) x = exitT (barG g) x ∧ exitT (barG g) x ≤ exitT φ x ∧
      exitT φ x = invPath φ x := by
  have hΦ := hg.mem_Φ hφ
  refine ⟨(hg.exitT_barG hx).symm, exitT_le_of_le (fun M => ?_) (fun t ht => hg.le_barG hφ ht.le) x,
    exitT_eq_invPath hΦ hx⟩
  obtain ⟨t, ht, hφt⟩ := hΦ.bijOn.surjOn (mem_Ici.mpr (by positivity : (0 : ℝ) ≤ max M 0 + 1))
  refine ⟨t, lt_of_le_of_ne ht fun h => ?_, by rw [hφt]; linarith [le_max_left M 0]⟩
  rw [← h, hΦ.init] at hφt
  linarith [le_max_right M 0]

/-! ### Lemma 3.16 and Theorem 3.17 -/

/-- A positive multiple of a function in `G` is in `G`. -/
theorem InG.const_mul (hg : InG g) {c : ℝ} (hc : 0 < c) : InG fun t x => c * g t x := by
  refine ⟨?_, mul_nonneg hc.le hg.nonneg_zero, fun x hx s hs t ht hst => ?_, fun t ht => ?_,
    fun x hx => ?_⟩
  · show ContinuousOn (fun p : ℝ × ℝ => c * Function.uncurry g p) _
    exact ContinuousOn.mul continuousOn_const hg.continuousOn
  · exact mul_lt_mul_of_pos_left (hg.strictMonoOn x hx hs ht hst) hc
  · obtain ⟨x, hx, hneg⟩ := hg.exists_neg t ht
    exact ⟨x, hx, mul_neg_of_pos_of_neg hc hneg⟩
  · obtain ⟨t, ht, hpos⟩ := hg.exists_pos x hx
    exact ⟨t, ht, mul_pos hc hpos⟩

/-- The bound `φ̄` of `c g` is that of `g`, for `c > 0`. -/
theorem barG_const_mul {c : ℝ} (hc : 0 < c) : barG (fun t x => c * g t x) = barG g := by
  funext t
  have h : {x | 0 < x ∧ c * g t x < 0} = {x | 0 < x ∧ g t x < 0} := by
    ext x
    exact ⟨fun h => ⟨h.1, by nlinarith [h.2]⟩, fun h => ⟨h.1, mul_neg_of_pos_of_neg hc h.2⟩⟩
  rw [barG, barG, h]

/-- `M` is `1`-Lipschitz for the uniform distance on `[0, x]`. -/
theorem supF_le_add {a b : ℝ → ℝ} {x η : ℝ} (hx : 0 ≤ x) (hη : 0 ≤ η) (hb : ContinuousOn b (Ici 0))
    (hab : ∀ y ∈ Icc 0 x, a y ≤ b y + η) : supF a x ≤ supF b x + η := by
  refine csSup_le ⟨_, 0, ⟨le_rfl, hx⟩, rfl⟩ ?_
  rintro _ ⟨y, hy, rfl⟩
  have hle : max 0 (b y) ≤ supF b x :=
    le_csSup (isCompact_Icc.image_of_continuousOn
      (ContinuousOn.sup continuousOn_const (hb.mono Icc_subset_Ici_self))).bddAbove ⟨y, hy, rfl⟩
  have := hab y hy
  show max 0 (a y) ≤ supF b x + η
  calc max 0 (a y) ≤ max 0 (b y) + η :=
        max_le (by linarith [le_max_left 0 (b y)]) (by linarith [le_max_right 0 (b y)])
    _ ≤ supF b x + η := by linarith

variable {g₀ : ℝ → ℝ → ℝ} {G : ℕ → ℝ → ℝ → ℝ}

/-- Lemma 3.16 (Convergence of bounds): if `g_n → g₀` uniformly on compacts of `ℝ₊²`, the exit
times `E (φ̄_n)` converge to `E (φ̄₀)` uniformly on compacts. The paths of zeros `ϕ_n` converge
uniformly, and `E (φ̄_n) = M (ϕ_n)` with `M` `1`-Lipschitz. -/
theorem bounds_converge (hg₀ : InG g₀) (hG : ∀ n, InG (G n))
    (hconv : ∀ T X η, 0 < η → ∀ᶠ n in atTop, ∀ t ∈ Icc 0 T, ∀ x ∈ Icc 0 X, |G n t x - g₀ t x| < η)
    (X η : ℝ) (hη : 0 < η) :
    ∀ᶠ n in atTop, ∀ x ∈ Icc 0 X, |exitT (barG g₀) x - exitT (barG (G n)) x| ≤ η := by
  rcases lt_or_ge X 0 with hX | hX
  · exact Eventually.of_forall fun n x hx => absurd (hx.1.trans hx.2) (not_le.mpr hX)
  -- the paths of zeros converge uniformly on `[0, X]`
  have hz : ∀ᶠ n in atTop, ∀ y ∈ Icc 0 X, |zeroG (G n) y - zeroG g₀ y| ≤ η := by
    obtain ⟨T', hT'⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hg₀.continuousOn_zeroG.mono (Icc_subset_Ici_self : Icc 0 X ⊆ Ici 0))
    have hT0 : 0 ≤ T' := (norm_nonneg _).trans (hT' 0 ⟨le_rfl, hX⟩)
    have hBne : (Icc 0 (T' + η) ×ˢ Icc 0 X).Nonempty :=
      (nonempty_Icc.mpr (by linarith)).prod (nonempty_Icc.mpr hX)
    have hBsub : Icc 0 (T' + η) ×ˢ Icc 0 X ⊆ Ici 0 ×ˢ Ici 0 := fun p hp => ⟨hp.1.1, hp.2.1⟩
    have hcont : ContinuousOn (fun p : ℝ × ℝ => g₀ (p.1 + η) p.2 - g₀ p.1 p.2)
        (Icc 0 (T' + η) ×ˢ Icc 0 X) := by
      refine ContinuousOn.sub ?_ (hg₀.continuousOn.mono hBsub)
      exact hg₀.continuousOn.comp ((continuous_fst.add continuous_const).prodMk
        continuous_snd).continuousOn fun p hp => ⟨show (0 : ℝ) ≤ p.1 + η by linarith [hp.1.1], hp.2.1⟩
    obtain ⟨p₀, hp₀, hmin⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMinOn hBne hcont
    set m := g₀ (p₀.1 + η) p₀.2 - g₀ p₀.1 p₀.2 with hm
    have hmpos : 0 < m := by
      have := hg₀.lt_of_lt hp₀.1.1 hp₀.2.1 (show p₀.1 < p₀.1 + η by linarith); linarith
    have hgap : ∀ t ∈ Icc 0 (T' + η), ∀ y ∈ Icc 0 X, m ≤ g₀ (t + η) y - g₀ t y :=
      fun t ht y hy => hmin (mk_mem_prod ht hy)
    filter_upwards [hconv (T' + 2 * η) X (m / 2) (by positivity)] with n hn y hy
    set z := zeroG g₀ y with hz
    have hz0 : 0 ≤ z := zeroG_nonneg _ _
    have hzT : z ≤ T' := by
      have := hT' y hy; rwa [Real.norm_eq_abs, abs_of_nonneg hz0] at this
    rw [abs_le]
    constructor
    · rcases le_or_gt z η with hzη | hzη
      · linarith [zeroG_nonneg (G n) y]
      · have hs0 : 0 ≤ z - η := by linarith
        have h1 := hgap (z - η) ⟨hs0, by linarith⟩ y hy
        rw [sub_add_cancel] at h1
        have h2 := hg₀.nonpos_at_zeroG hy.1 (by linarith)
        have h3 := hn (z - η) ⟨hs0, by linarith⟩ y hy
        have hneg : G n (z - η) y < 0 := by
          linarith [le_abs_self (G n (z - η) y - g₀ (z - η) y)]
        have := ((hG n).lt_zeroG_iff hs0 hy.1).mpr hneg
        linarith
    · have h1 := hgap z ⟨hz0, by linarith⟩ y hy
      have h2 := hg₀.nonneg_at_zeroG hy.1
      have h3 := hn (z + η) ⟨by linarith, by linarith⟩ y hy
      have hpos : 0 < G n (z + η) y := by
        linarith [neg_abs_le (G n (z + η) y - g₀ (z + η) y)]
      have := (hG n).zeroG_le_of_pos (by linarith) hy.1 hpos
      linarith
  -- so do their running maxima
  filter_upwards [hz] with n hn x hx
  rw [hg₀.exitT_barG hx.1, (hG n).exitT_barG hx.1]
  have h1 := supF_le_add (a := zeroG g₀) (b := zeroG (G n)) hx.1 hη.le (hG n).continuousOn_zeroG
    fun y hy => by linarith [abs_le.mp (hn y ⟨hy.1, hy.2.trans hx.2⟩)]
  have h2 := supF_le_add (a := zeroG (G n)) (b := zeroG g₀) hx.1 hη.le hg₀.continuousOn_zeroG
    fun y hy => by linarith [abs_le.mp (hn y ⟨hy.1, hy.2.trans hx.2⟩)]
  rw [abs_le]
  constructor <;> linarith

/-- `E (φ̄₀) = M (ϕ₀)` is continuous and non-decreasing on `ℝ₊`. -/
theorem InG.continuousOn_supF (hg : InG g) : ContinuousOn (supF (zeroG g)) (Ici 0) :=
  continuousOn_runMax (p := fun s => max 0 (zeroG g s))
    (ContinuousOn.sup continuousOn_const hg.continuousOn_zeroG)

theorem InG.supF_mono (hg : InG g) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    supF (zeroG g) x ≤ supF (zeroG g) y :=
  runMax_mono (p := fun s => max 0 (zeroG g s))
    (ContinuousOn.sup continuousOn_const hg.continuousOn_zeroG) hx hxy

/-- For a global solution, the inverse of Lemma 2.16 is `φ⁻¹`. -/
theorem solInv_zero_top {φ : ℝ → ℝ} : solInv φ 0 ⊤ = invPath φ := by
  unfold solInv invPath
  rw [dom_top]

/-- Theorem 3.17 (Uniform exit-time limits): if `g_n → g₀` uniformly on compacts of `ℝ₊²`, the
global solutions `φ_n` of `x' = (n + 1) g_n (t, x)`, `x (0) = 0` converge to `φ̄₀` on
`(Φ̄, d_Φ̄)`: their inverses converge to `E (φ̄₀)` uniformly on compacts. -/
theorem exit_limit (hg₀ : InG g₀) (hG : ∀ n, InG (G n))
    (hconv : ∀ T X η, 0 < η → ∀ᶠ n in atTop, ∀ t ∈ Icc 0 T, ∀ x ∈ Icc 0 X, |G n t x - g₀ t x| < η)
    {φ : ℕ → ℝ → ℝ} (hφ : ∀ n : ℕ, IsGlobalSolution (fun t x => ((n : ℝ) + 1) * G n t x) (φ n)) :
    (∀ X η, 0 < η → ∀ᶠ n in atTop, ∀ x ∈ Icc 0 X,
      |exitT (barG g₀) x - invPath (φ n) x| ≤ η) ∧
    Tendsto (fun n => exitMetric (φ n) (barG g₀)) atTop (𝓝 0) := by
  have hG' : ∀ n : ℕ, InG fun t x => ((n : ℝ) + 1) * G n t x :=
    fun n => (hG n).const_mul (by positivity)
  have hΦ : ∀ n, InΦ (φ n) := fun n => (hG' n).mem_Φ (hφ n)
  have main : ∀ X, 1 ≤ X → ∀ η, 0 < η → ∀ᶠ n in atTop, ∀ x ∈ Icc 0 X,
      |exitT (barG g₀) x - invPath (φ n) x| ≤ η := by
    intro X hX η hη
    have hXpos : 0 < X := by linarith
    have hMc := hg₀.continuousOn_supF
    set κ := η / (2 * X) with hκ
    have hκpos : 0 < κ := by positivity
    set μ : ℝ → ℝ := fun x => supF (zeroG g₀) x + η / 2 + κ * x with hμ
    have hμc : ContinuousOn μ (Ici 0) :=
      (hMc.add continuousOn_const).add (continuousOn_const.mul continuousOn_id)
    -- on the line `x ↦ (μ (x), x)`, `g₀ > 0`, so `g₀ ≥ m₀ > 0` on `[0, X]`
    have hline : ∀ x ∈ Icc 0 X, 0 < g₀ (μ x) x := by
      intro x hx
      have hz := hg₀.zeroG_le_supF (x := x) ⟨hx.1, le_rfl⟩
      have hzμ : zeroG g₀ x < μ x := by
        have : 0 ≤ κ * x := mul_nonneg hκpos.le hx.1
        simp only [hμ]; linarith
      set t' := (zeroG g₀ x + μ x) / 2 with ht'
      have hz0 := zeroG_nonneg g₀ x
      have h1 : 0 ≤ g₀ t' x := not_lt.mp fun h => by
        have := (hg₀.lt_zeroG_iff (by linarith) hx.1).mpr h; linarith
      linarith [hg₀.lt_of_lt (by linarith) hx.1 (show t' < μ x by linarith)]
    have hlinec : ContinuousOn (fun x => g₀ (μ x) x) (Icc 0 X) :=
      hg₀.continuousOn.comp ((hμc.mono Icc_subset_Ici_self).prodMk continuousOn_id) fun x hx =>
        ⟨show (0 : ℝ) ≤ μ x by
          simp only [hμ]; linarith [supF_nonneg (zeroG g₀) x, mul_nonneg hκpos.le hx.1], hx.1⟩
    obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn
      (nonempty_Icc.mpr (by linarith : (0 : ℝ) ≤ X)) hlinec
    set m₀ := g₀ (μ x₀) x₀ with hm₀
    have hm₀pos : 0 < m₀ := hline x₀ hx₀
    have hμmono : ∀ x ∈ Icc 0 X, μ x ≤ μ X := fun x hx => by
      simp only [hμ]
      linarith [hg₀.supF_mono hx.1 hx.2, mul_le_mul_of_nonneg_left hx.2 hκpos.le]
    have hμnn : ∀ x, 0 ≤ x → 0 ≤ μ x := fun x hx => by
      simp only [hμ]; linarith [supF_nonneg (zeroG g₀) x, mul_nonneg hκpos.le hx]
    obtain ⟨N, hN⟩ := exists_nat_gt (2 / (κ * m₀))
    filter_upwards [hconv (μ X) X (m₀ / 2) (by positivity),
      bounds_converge hg₀ hG hconv X η hη, eventually_ge_atTop N] with n hn hb hnN x hx
    -- the lower bound, from Corollary 3.15 and Lemma 3.16
    obtain ⟨-, hlow, hinv⟩ := (hG' n).exitT_barG_le (hφ n) hx.1
    rw [barG_const_mul (by positivity)] at hlow
    have hb' := abs_le.mp (hb x hx)
    -- the upper bound: `φ_n⁻¹ < μ` on `[0, X]`, by comparison at a first meeting point
    set ψ := invPath (φ n) with hψ
    have hψc : ContinuousOn ψ (Ici 0) :=
      continuousOn_invPath (hΦ n).bijOn (hΦ n).strictMonoOn (hΦ n).init
    have hup : ψ x < μ x := by
      by_contra hge
      push Not at hge
      have hD0 : 0 < μ 0 - ψ 0 := by
        rw [hψ, invPath_zero (hΦ n).bijOn (hΦ n).init]
        simp only [hμ, mul_zero, add_zero, sub_zero]
        linarith [supF_nonneg (zeroG g₀) 0]
      obtain ⟨x', hx', hDx', hbefore⟩ := exists_first_nonpos (g := fun y => μ y - ψ y) hx.1
        ((hμc.mono Icc_subset_Ici_self).sub (hψc.mono Icc_subset_Ici_self)) hD0
        (show μ x - ψ x ≤ 0 by linarith)
      have hx'X : x' ∈ Icc 0 X := ⟨hx'.1.le, hx'.2.trans hx.2⟩
      have hmeet : ψ x' = μ x' := by have : μ x' - ψ x' = 0 := hDx'; linarith
      set t' := ψ x' with ht'
      have ht'0 : 0 < t' := by
        rw [hmeet]
        have h1 := supF_nonneg (zeroG g₀) x'
        have h2 := mul_nonneg hκpos.le hx'.1.le
        simp only [hμ]
        linarith
      have hφt' : φ n t' = x' := apply_invPath (hΦ n).bijOn hx'.1.le
      -- on the line, `(n + 1) g_n > 1 / κ`
      have hGn : 1 / κ < ((n : ℝ) + 1) * G n t' x' := by
        have h1 := hn t' ⟨ht'0.le, by rw [hmeet]; exact hμmono x' hx'X⟩ x' hx'X
        have h2 : m₀ ≤ g₀ t' x' := by rw [hmeet]; exact hmin hx'X
        have h3 : m₀ / 2 < G n t' x' := by linarith [neg_abs_le (G n t' x' - g₀ t' x')]
        have hn1 : (N : ℝ) ≤ n := by exact_mod_cast hnN
        have h4 : 2 / (κ * m₀) < (n : ℝ) + 1 := by linarith
        have h5 : 1 / κ = 2 / (κ * m₀) * (m₀ / 2) := by
          rw [div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]; ring
        rw [h5]
        exact mul_lt_mul h4 h3.le (by positivity) (by positivity)
      -- the inverse's derivative at `x'` is below `κ`
      have hderiv : HasDerivAt ψ (((n : ℝ) + 1) * G n t' x')⁻¹ x' := by
        have h := hasDerivAt_solInv (hG' n).inF_extendG (hG' n).lineCondition_extendG
          ((hG' n).isGlobalSolution_iff.mp (hφ n)) (t := t')
          (by rw [dom_top]; exact ht'0.le) ht'0
          (by rw [extendG_of_nonneg ht'0.le ((hφ n).nonneg t' ht'0.le), hφt']
              exact lt_trans (by positivity) hGn)
        rw [solInv_zero_top, extendG_of_nonneg ht'0.le ((hφ n).nonneg t' ht'0.le), hφt'] at h
        exact h
      have hdκ : (((n : ℝ) + 1) * G n t' x')⁻¹ < κ := by
        rw [inv_lt_comm₀ (lt_trans (by positivity) hGn) hκpos, ← one_div]; exact hGn
      have hev : Tendsto (slope ψ x') (𝓝[<] x') (𝓝 (((n : ℝ) + 1) * G n t' x')⁻¹) :=
        (hasDerivAt_iff_tendsto_slope.mp hderiv).mono_left
          (nhdsWithin_mono x' fun y hy => ne_of_lt (mem_Iio.mp hy))
      obtain ⟨u, hu1, hu2⟩ := ((hev.eventually (gt_mem_nhds hdκ)).and
        (Ioo_mem_nhdsLT hx'.1)).exists
      have hDu : 0 < μ u - ψ u := hbefore u ⟨hu2.1.le, hu2.2⟩
      rw [slope_def_field] at hu1
      have hux : 0 < x' - u := by linarith [hu2.2]
      have h1 : ψ x' - ψ u < κ * (x' - u) := by
        have : (ψ u - ψ x') / (u - x') = (ψ x' - ψ u) / (x' - u) := by
          rw [← neg_sub (ψ x'), ← neg_sub x', neg_div_neg_eq]
        rw [this, div_lt_iff₀ hux] at hu1; linarith
      have h2 : κ * (x' - u) ≤ μ x' - μ u := by
        simp only [hμ]
        linarith [hg₀.supF_mono hu2.1.le hu2.2.le]
      linarith
    have hlow' : exitT (barG (G n)) x ≤ ψ x := hlow.trans_eq hinv
    have hκX : κ * (2 * X) = η := div_mul_cancel₀ η (by positivity)
    have hκx : κ * x ≤ κ * X := mul_le_mul_of_nonneg_left hx.2 hκpos.le
    have hμx : μ x = supF (zeroG g₀) x + η / 2 + κ * x := rfl
    have hE := hg₀.exitT_barG hx.1
    rw [abs_le]
    constructor
    · linarith
    · linarith [hb'.2]
  have hfull : ∀ X η, 0 < η → ∀ᶠ n in atTop, ∀ x ∈ Icc 0 X,
      |exitT (barG g₀) x - invPath (φ n) x| ≤ η := fun X η hη =>
    (main (max X 1) (le_max_right _ _) η hη).mono fun n hn x hx =>
      hn x ⟨hx.1, hx.2.trans (le_max_left _ _)⟩
  refine ⟨hfull, tendsto_exitMetric fun X η hη => (hfull X η hη).mono fun n hn x hx => ?_⟩
  rw [exitT_eq_invPath (hΦ n) hx.1]
  exact hn x hx

end PathwiseVolatility
