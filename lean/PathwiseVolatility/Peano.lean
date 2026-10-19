/-
Copyright (c) 2026 Ryan McCrickerd. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCrickerd
-/
import PathwiseVolatility.Basic

/-!
# Peano's existence theorem, forward in time, for scalar ODEs

The classical existence theorem the thesis cites (Peano; Theorem 1.1.2 of Lakshmikantham and
Leela): for `f` continuous, if `|f| ≤ M` on the box `[s, s + a] × [x - r, x + r]` and
`M a ≤ r`, then `x' = f (t, x)`, `x (s) = x` has a solution on `[s, s + a]`.

The Mathlib version used here does not have this theorem. The proof here approximates `f` uniformly by fields
which are Lipschitz in space, by averaging over small spatial intervals, solves each
approximation with Mathlib's Picard–Lindelöf theorem, takes a uniformly convergent subsequence
by the Arzelà–Ascoli theorem, and passes to the limit in the integral equation.
-/

open Set Filter Topology MeasureTheory
open scoped NNReal

namespace PathwiseVolatility

namespace Peano

/-- `max lo (min y hi)`, which clamps `y` to `[lo, hi]`, is `1`-Lipschitz. -/
theorem abs_clamp_sub_le (lo hi y y' : ℝ) :
    |max lo (min y hi) - max lo (min y' hi)| ≤ |y - y'| := by
  have h1 := le_abs_self (y - y')
  have h2 := neg_abs_le (y - y')
  rw [abs_le]
  constructor <;> simp only [max_def, min_def] <;> split_ifs <;> linarith

theorem clamp_mem {lo hi : ℝ} (h : lo ≤ hi) (y : ℝ) : max lo (min y hi) ∈ Icc lo hi :=
  ⟨le_max_left _ _, max_le h (min_le_right _ _)⟩

theorem clamp_of_mem {lo hi y : ℝ} (hy : y ∈ Icc lo hi) : max lo (min y hi) = y := by
  rw [min_eq_left hy.2, max_eq_right hy.1]

variable {f : ℝ → ℝ → ℝ} {s x a r M : ℝ}

/-- `f` with time clamped to `[s, s + a]` and space to `[x - r, x + r]`: it agrees with `f` on
the box, and is bounded and uniformly continuous in space on all of `ℝ²`. -/
def clampF (f : ℝ → ℝ → ℝ) (s x a r : ℝ) (t y : ℝ) : ℝ :=
  f (max s (min t (s + a))) (max (x - r) (min y (x + r)))

theorem continuous_clampF (hf : Continuous (Function.uncurry f)) :
    Continuous (Function.uncurry (clampF f s x a r)) :=
  hf.comp ((continuous_const.max (continuous_fst.min continuous_const)).prodMk
    (continuous_const.max (continuous_snd.min continuous_const)))

theorem clampF_eq {t y : ℝ} (ht : t ∈ Icc s (s + a)) (hy : y ∈ Icc (x - r) (x + r)) :
    clampF f s x a r t y = f t y := by
  rw [clampF, clamp_of_mem ht, clamp_of_mem hy]

theorem abs_clampF_le (ha : 0 ≤ a) (hr : 0 ≤ r)
    (hM : ∀ t ∈ Icc s (s + a), ∀ y ∈ Icc (x - r) (x + r), |f t y| ≤ M) (t y : ℝ) :
    |clampF f s x a r t y| ≤ M :=
  hM _ (clamp_mem (by linarith) t) _ (clamp_mem (by linarith) y)

/-- The clamped field is uniformly continuous in space, uniformly in time. -/
theorem clampF_modulus (hf : Continuous (Function.uncurry f)) (ha : 0 ≤ a) (hr : 0 ≤ r) {ε : ℝ}
    (hε : 0 < ε) : ∃ δ > 0, ∀ t y y', |y - y'| < δ →
      |clampF f s x a r t y - clampF f s x a r t y'| < ε := by
  have hK : IsCompact (Icc s (s + a) ×ˢ Icc (x - r) (x + r)) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hf.continuousOn) ε hε
  refine ⟨δ, hδ, fun t y y' hyy' => ?_⟩
  have hsa : s ≤ s + a := by linarith
  have hxr : x - r ≤ x + r := by linarith
  have hp : (max s (min t (s + a)), max (x - r) (min y (x + r))) ∈
      Icc s (s + a) ×ˢ Icc (x - r) (x + r) := ⟨clamp_mem hsa t, clamp_mem hxr y⟩
  have hq : (max s (min t (s + a)), max (x - r) (min y' (x + r))) ∈
      Icc s (s + a) ×ˢ Icc (x - r) (x + r) := ⟨clamp_mem hsa t, clamp_mem hxr y'⟩
  have := h _ hp _ hq (by
    rw [Prod.dist_eq, dist_self, Real.dist_eq]
    exact max_lt hδ ((abs_clamp_sub_le _ _ y y').trans_lt hyy'))
  rwa [Real.dist_eq] at this

/-! ### Averaging in space -/

/-- A primitive in space, `G (t, y) = ∫₀^y F (t, z) dz`. -/
noncomputable def prim (F : ℝ → ℝ → ℝ) (t y : ℝ) : ℝ := ∫ z in (0 : ℝ)..y, F t z

/-- The average of `F (t, ·)` over `[y, y + 1 / (n + 1)]`. -/
noncomputable def avgF (F : ℝ → ℝ → ℝ) (n : ℕ) (t y : ℝ) : ℝ :=
  (n + 1 : ℝ) * (prim F t (y + 1 / (n + 1)) - prim F t y)

variable {F : ℝ → ℝ → ℝ}

theorem continuous_level' (hF : Continuous (Function.uncurry F)) (t : ℝ) : Continuous (F t) :=
  hF.comp (continuous_const.prodMk continuous_id)

theorem prim_sub (hF : Continuous (Function.uncurry F)) (t y y' : ℝ) :
    prim F t y - prim F t y' = ∫ z in y'..y, F t z :=
  intervalIntegral.integral_interval_sub_left ((continuous_level' hF t).intervalIntegrable _ _)
    ((continuous_level' hF t).intervalIntegrable _ _)

theorem abs_prim_sub_le (hF : Continuous (Function.uncurry F)) (hFM : ∀ t y, |F t y| ≤ M)
    (t y y' : ℝ) : |prim F t y - prim F t y'| ≤ M * |y - y'| := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := y') (b := y) (C := M)
    (f := F t) fun z _ => by rw [Real.norm_eq_abs]; exact hFM t z
  rw [prim_sub hF]
  rwa [Real.norm_eq_abs] at h

theorem continuous_prim (hF : Continuous (Function.uncurry F)) :
    Continuous (Function.uncurry (prim F)) := by
  have h : Continuous (fun p : (ℝ × ℝ) × ℝ => F p.1.1 p.2) :=
    hF.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun (p : ℝ × ℝ) (z : ℝ) => F p.1 z) h continuous_snd

theorem continuous_avgF (hF : Continuous (Function.uncurry F)) (n : ℕ) :
    Continuous (Function.uncurry (avgF F n)) := by
  have h := continuous_prim hF
  exact continuous_const.mul
    ((h.comp (continuous_fst.prodMk (continuous_snd.add continuous_const))).sub h)

theorem avgF_sub_eq (hF : Continuous (Function.uncurry F)) (n : ℕ) (t y : ℝ) :
    avgF F n t y - F t y = (n + 1 : ℝ) * ∫ z in y..y + 1 / (n + 1), (F t z - F t y) := by
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  rw [avgF, prim_sub hF, intervalIntegral.integral_sub
    ((continuous_level' hF t).intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul, mul_sub]
  field_simp
  ring

/-- `|avgF| ≤ M`. -/
theorem abs_avgF_le (hF : Continuous (Function.uncurry F)) (hFM : ∀ t y, |F t y| ≤ M) (n : ℕ)
    (t y : ℝ) : |avgF F n t y| ≤ M := by
  have h := abs_prim_sub_le hF hFM t (y + 1 / (n + 1)) y
  have hn : (0 : ℝ) < n + 1 := by positivity
  rw [show y + 1 / (n + 1) - y = 1 / (n + 1) by ring,
    abs_of_pos (show (0 : ℝ) < 1 / (n + 1) by positivity)] at h
  rw [avgF, abs_mul, abs_of_pos hn]
  calc (n + 1 : ℝ) * |prim F t (y + 1 / (n + 1)) - prim F t y|
      ≤ (n + 1) * (M * (1 / (n + 1))) := mul_le_mul_of_nonneg_left h hn.le
    _ = M := by field_simp

/-- `avgF F n t` is Lipschitz with constant `2 M (n + 1)`. -/
theorem abs_avgF_sub_le (hF : Continuous (Function.uncurry F)) (hFM : ∀ t y, |F t y| ≤ M)
    (n : ℕ) (t y y' : ℝ) :
    |avgF F n t y - avgF F n t y'| ≤ 2 * M * (n + 1) * |y - y'| := by
  have h1 := abs_prim_sub_le hF hFM t (y + 1 / (n + 1)) (y' + 1 / (n + 1))
  have h2 := abs_prim_sub_le hF hFM t y y'
  rw [show y + 1 / (n + 1) - (y' + 1 / (n + 1)) = y - y' by ring] at h1
  have hn : (0 : ℝ) < n + 1 := by positivity
  have : avgF F n t y - avgF F n t y' = (n + 1) * ((prim F t (y + 1 / (n + 1)) -
      prim F t (y' + 1 / (n + 1))) - (prim F t y - prim F t y')) := by
    rw [avgF, avgF]; ring
  rw [this, abs_mul, abs_of_pos hn]
  calc (n + 1 : ℝ) * |prim F t (y + 1 / (n + 1)) - prim F t (y' + 1 / (n + 1)) -
        (prim F t y - prim F t y')|
      ≤ (n + 1) * (M * |y - y'| + M * |y - y'|) :=
        mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add h1 h2)) hn.le
    _ = 2 * M * (n + 1) * |y - y'| := by ring

/-- `avgF F n` approximates `F` uniformly once `1 / (n + 1)` is below the modulus of `F`. -/
theorem abs_avgF_sub_self_le (hF : Continuous (Function.uncurry F)) {ε δ : ℝ}
    (hmod : ∀ t y y', |y - y'| < δ → |F t y - F t y'| < ε) {n : ℕ} (hn : 1 / (n + 1 : ℝ) < δ)
    (t y : ℝ) : |avgF F n t y - F t y| ≤ ε := by
  have hpos : (0 : ℝ) < n + 1 := by positivity
  rw [avgF_sub_eq hF, abs_mul, abs_of_pos hpos]
  have hint : ‖∫ z in y..y + 1 / (n + 1), (F t z - F t y)‖ ≤ ε * |y + 1 / (n + 1) - y| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun z hz => ?_
    rw [uIoc_of_le (by linarith [show (0 : ℝ) < 1 / (n + 1) by positivity])] at hz
    rw [Real.norm_eq_abs]
    refine (hmod t z y ?_).le
    rw [abs_lt]; constructor <;> linarith [hz.1, hz.2]
  rw [Real.norm_eq_abs, show y + 1 / (n + 1) - y = 1 / (n + 1) by ring,
    abs_of_pos (show (0 : ℝ) < 1 / (n + 1) by positivity)] at hint
  calc (n + 1 : ℝ) * |∫ z in y..y + 1 / (n + 1), (F t z - F t y)|
      ≤ (n + 1) * (ε * (1 / (n + 1))) := mul_le_mul_of_nonneg_left hint hpos.le
    _ = ε := by field_simp

end Peano

open Peano

attribute [local irreducible] clampF prim avgF

/-- **Peano's existence theorem**, forward in time: if `f` is continuous, `|f| ≤ M` on
`[s, s + a] × [x - r, x + r]` and `M a ≤ r`, then `x' = f (t, x)`, `x (s) = x` has a solution on
`[s, s + a]`, which stays in `[x - r, x + r]`. -/
theorem peano_exists {f : ℝ → ℝ → ℝ} (hf : Continuous (Function.uncurry f)) {s x a r M : ℝ}
    (ha : 0 ≤ a) (hr : 0 ≤ r)
    (hM : ∀ t ∈ Icc s (s + a), ∀ y ∈ Icc (x - r) (x + r), |f t y| ≤ M) (haM : M * a ≤ r) :
    ∃ χ : ℝ → ℝ, χ s = x ∧ (∀ t ∈ Icc s (s + a), χ t ∈ Icc (x - r) (x + r)) ∧
      ∀ t ∈ Icc s (s + a), HasDerivWithinAt χ (f t (χ t)) (Icc s (s + a)) t := by
  obtain ⟨F, hFdef⟩ : ∃ F, F = clampF f s x a r := ⟨_, rfl⟩
  have hF : Continuous (Function.uncurry F) := by rw [hFdef]; exact continuous_clampF hf
  have hFM : ∀ t y, |F t y| ≤ M := by rw [hFdef]; exact abs_clampF_le ha hr hM
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hFM s x)
  have hsa : s ≤ s + a := by linarith
  -- 1. the approximations, by Picard–Lindelöf
  have hPL : ∀ n : ℕ, ∃ α : ℝ → ℝ, α s = x ∧
      ∀ t ∈ Icc s (s + a), HasDerivWithinAt α (avgF F n t (α t)) (Icc s (s + a)) t := by
    intro n
    have hK : 0 ≤ 2 * M * (n + 1) := by positivity
    have hP : IsPicardLindelof (avgF F n) (⟨s, le_rfl, hsa⟩ : Icc s (s + a)) x
        ⟨r, hr⟩ 0 ⟨M, hM0⟩ ⟨2 * M * (n + 1), hK⟩ :=
      { lipschitzOnWith := fun t _ => (LipschitzWith.of_dist_le_mul fun y y' => by
            rw [Real.dist_eq, Real.dist_eq]; exact abs_avgF_sub_le hF hFM n t y y').lipschitzOnWith
        continuousOn := fun y _ =>
          ((continuous_avgF hF n).comp (continuous_id.prodMk continuous_const)).continuousOn
        norm_le := fun t _ y _ => by rw [Real.norm_eq_abs]; exact abs_avgF_le hF hFM n t y
        mul_max_le := by
          simp only [NNReal.coe_zero, sub_zero, sub_self, add_sub_cancel_left]
          rw [max_eq_left ha]
          exact haM }
    obtain ⟨α, hα0, hα⟩ := hP.exists_eq_forall_mem_Icc_hasDerivWithinAt
      (Metric.mem_closedBall_self (le_refl 0))
    exact ⟨α, hα0, hα⟩
  choose α hα0 hα using hPL
  -- 2. each approximation is `M`-Lipschitz on `[s, s + a]`, stays in the box and solves its
  -- integral equation
  have hlip : ∀ n, LipschitzOnWith ⟨M, hM0⟩ (α n) (Icc s (s + a)) := fun n =>
    (convex_Icc s (s + a)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le (hα n) fun t _ =>
      NNReal.coe_le_coe.mp (by rw [coe_nnnorm, Real.norm_eq_abs]; exact abs_avgF_le hF hFM n t _)
  have hcont : ∀ n, ContinuousOn (α n) (Icc s (s + a)) := fun n => (hlip n).continuousOn
  have hbox : ∀ n, ∀ t ∈ Icc s (s + a), α n t ∈ Icc (x - r) (x + r) := by
    intro n t ht
    have h := (hlip n).dist_le_mul t ht s ⟨le_rfl, hsa⟩
    rw [Real.dist_eq, Real.dist_eq, hα0] at h
    change |α n t - x| ≤ M * |t - s| at h
    rw [abs_of_nonneg (show (0 : ℝ) ≤ t - s by linarith [ht.1])] at h
    have : M * (t - s) ≤ r := le_trans (mul_le_mul_of_nonneg_left (by linarith [ht.2]) hM0) haM
    constructor <;> linarith [neg_abs_le (α n t - x), le_abs_self (α n t - x)]
  have hint : ∀ n, ∀ t ∈ Icc s (s + a), α n t = x + ∫ u in s..t, avgF F n u (α n u) := by
    intro n t ht
    have hsub : Icc s t ⊆ Icc s (s + a) := Icc_subset_Icc_right ht.2
    have hc' : Continuous fun p : ℝ × ℝ => avgF F n p.1 p.2 := continuous_avgF hF n
    have hcomp : ContinuousOn (fun u => avgF F n u (α n u)) (Icc s t) :=
      hc'.comp_continuousOn (continuousOn_id.prodMk ((hcont n).mono hsub))
    have hderiv : ∀ u ∈ Ioo s t, HasDerivWithinAt (α n) (avgF F n u (α n u)) (Ioi u) u := by
      intro u hu
      have hnhds : Icc s (s + a) ∈ 𝓝 u :=
        Icc_mem_nhds (by linarith [hu.1]) (by linarith [hu.2, ht.2])
      exact ((hα n u (hsub (Ioo_subset_Icc_self hu))).hasDerivAt hnhds).hasDerivWithinAt
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1
      ((hcont n).mono hsub) hderiv (hcomp.intervalIntegrable_of_Icc ht.1)
    rw [hFTC, hα0]
    ring
  -- 3. a uniformly convergent subsequence, by Arzelà–Ascoli
  have hcI : ∀ n, Continuous ((Icc s (s + a)).domRestrict (α n)) := fun n =>
    continuousOn_iff_continuous_domRestrict.mp (hcont n)
  obtain ⟨g, hg⟩ : ∃ g : ℕ → BoundedContinuousFunction (Icc s (s + a)) ℝ,
      ∀ n t, g n t = α n t :=
    ⟨fun n => BoundedContinuousFunction.mkOfCompact ⟨(Icc s (s + a)).domRestrict (α n), hcI n⟩,
      fun _ _ => rfl⟩
  have hcompact : IsCompact (closure (range g)) := by
    refine BoundedContinuousFunction.arzela_ascoli (Icc (x - r) (x + r)) isCompact_Icc
      (range g) ?_ ?_
    · rintro _ t ⟨n, rfl⟩
      rw [hg]
      exact hbox n t t.2
    · refine (LipschitzWith.uniformEquicontinuous _ ⟨M, hM0⟩ ?_).equicontinuous
      rintro ⟨_, n, rfl⟩
      have : ⇑(g n) = (Icc s (s + a)).domRestrict (α n) := funext fun t => hg n t
      show LipschitzWith ⟨M, hM0⟩ ⇑(g n)
      rw [this]
      exact (hlip n).to_restrict
  obtain ⟨gl, -, φ, hφ, hlim⟩ := hcompact.tendsto_subseq fun n => subset_closure ⟨n, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ → ℝ, β = fun t => gl (projIcc s (s + a) hsa t) := ⟨_, rfl⟩
  have hβc : Continuous β := by rw [hβ]; exact gl.continuous.comp continuous_projIcc
  have hconv : ∀ k, ∀ t ∈ Icc s (s + a), |α (φ k) t - β t| ≤ dist (g (φ k)) gl := by
    intro k t ht
    have h := BoundedContinuousFunction.dist_coe_le_dist (f := g (φ k)) (g := gl) ⟨t, ht⟩
    have h1 : g (φ k) ⟨t, ht⟩ = α (φ k) t := hg _ _
    have h2 : β t = gl ⟨t, ht⟩ := by simp only [hβ, projIcc_of_mem hsa ht]
    rwa [Real.dist_eq, h1, ← h2] at h
  have hd : Tendsto (fun k => dist (g (φ k)) gl) atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp hlim
  have hpt : ∀ t ∈ Icc s (s + a), Tendsto (fun k => α (φ k) t) atTop (𝓝 (β t)) := fun t ht =>
    tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero (fun _ => dist_nonneg)
      (fun k => by rw [Real.dist_eq]; exact hconv k t ht) hd)
  have hβs : β s = x := tendsto_nhds_unique (hpt s ⟨le_rfl, hsa⟩)
    (by simp only [hα0]; exact tendsto_const_nhds)
  have hβbox : ∀ t ∈ Icc s (s + a), β t ∈ Icc (x - r) (x + r) := fun t ht =>
    isClosed_Icc.mem_of_tendsto (hpt t ht) (Eventually.of_forall fun k => hbox _ t ht)
  -- 4. the limit solves the integral equation of the clamped field
  have hΦ : Continuous fun u => F u (β u) := hF.comp (continuous_id.prodMk hβc)
  have hβint : ∀ t ∈ Icc s (s + a), β t = x + ∫ u in s..t, F u (β u) := by
    intro t ht
    have hI1 : Tendsto (fun k => ∫ u in s..t, avgF F (φ k) u (α (φ k) u)) atTop
        (𝓝 (β t - x)) := by
      refine ((hpt t ht).sub_const x).congr fun k => ?_
      rw [hint (φ k) t ht]
      ring
    have hI2 : Tendsto (fun k => ∫ u in s..t, avgF F (φ k) u (α (φ k) u)) atTop
        (𝓝 (∫ u in s..t, F u (β u))) := by
      refine Metric.tendsto_atTop.mpr fun ε hε => ?_
      set η := ε / (2 * (a + 1)) with hη
      have hηpos : 0 < η := by positivity
      have h2η : 2 * η * (a + 1) = ε := by rw [hη]; field_simp
      obtain ⟨δ, hδ, hmod⟩ := clampF_modulus (s := s) (x := x) (a := a) (r := r) hf ha hr hηpos
      rw [← hFdef] at hmod
      obtain ⟨N₁, hN₁⟩ := exists_nat_one_div_lt hδ
      obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp hd δ hδ
      refine ⟨max N₁ N₂, fun k hk => ?_⟩
      have hφk : N₁ ≤ φ k := (le_max_left _ _).trans (hk.trans (hφ.id_le k))
      have hn : 1 / ((φ k : ℕ) + 1 : ℝ) < δ := lt_of_le_of_lt
        (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hφk 1))
        hN₁
      have hdk : dist (g (φ k)) gl < δ := by
        have := hN₂ k ((le_max_right _ _).trans hk)
        rwa [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] at this
      have hsub : Icc s t ⊆ Icc s (s + a) := Icc_subset_Icc_right ht.2
      have hA : IntervalIntegrable (fun u => avgF F (φ k) u (α (φ k) u)) volume s t :=
        ContinuousOn.intervalIntegrable_of_Icc ht.1 ((continuous_avgF hF (φ k)).comp_continuousOn
          (continuousOn_id.prodMk ((hcont (φ k)).mono hsub)))
      rw [Real.dist_eq, ← intervalIntegral.integral_sub hA (hΦ.intervalIntegrable s t)]
      have hbound : ‖∫ u in s..t, (avgF F (φ k) u (α (φ k) u) - F u (β u))‖ ≤
          2 * η * |t - s| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => ?_
        rw [uIoc_of_le ht.1] at hu
        have hu' : u ∈ Icc s (s + a) := hsub ⟨hu.1.le, hu.2⟩
        rw [Real.norm_eq_abs]
        calc |avgF F (φ k) u (α (φ k) u) - F u (β u)|
            ≤ |avgF F (φ k) u (α (φ k) u) - F u (α (φ k) u)| +
                |F u (α (φ k) u) - F u (β u)| := abs_sub_le _ _ _
          _ ≤ η + η := add_le_add (abs_avgF_sub_self_le hF hmod hn u _)
                (hmod u _ _ ((hconv k u hu').trans_lt hdk)).le
          _ = 2 * η := by ring
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.1] : 0 ≤ t - s)] at hbound
      have : 2 * η * (t - s) ≤ 2 * η * a :=
        mul_le_mul_of_nonneg_left (by linarith [ht.2]) (by positivity)
      linarith
    linarith [tendsto_nhds_unique hI1 hI2]
  -- 5. so it solves the ODE of `f`, which agrees with the clamped field along it
  refine ⟨β, hβs, hβbox, fun t ht => ?_⟩
  have hd' : HasDerivWithinAt (fun u => x + ∫ v in s..u, F v (β v)) (F t (β t))
      (Icc s (s + a)) t :=
    ((hΦ.integral_hasStrictDerivAt s t).hasDerivAt.hasDerivWithinAt).const_add x
  rw [← clampF_eq (f := f) ht (hβbox t ht), ← hFdef]
  exact hd'.congr_of_mem hβint ht

end PathwiseVolatility
