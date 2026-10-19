/-
Copyright (c) 2026 Ryan McCrickerd. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCrickerd
-/
import PathwiseVolatility.SolutionSet

/-!
# Section 3.3: the uniform exit-time space

Definitions 3.9 (the exit-time functional `E`), 3.10 (the set `N`) and 3.12 (the exit-time metric
`d_Φ̄`), the supremum functional `M` of eq. (3.27), and the seminorm `‖·‖_{ℝ₊}` of eq. (1.12).
Convergence on `(Φ̄, d_Φ̄)` follows from uniform convergence of exit times on each `[0, X]`
(`tendsto_exitMetric`), which is how Theorems 3.17 and 3.18 are proved; and on `Φ`, `E` is the
inverse map (`exitT_eq_invPath`).
-/

open Set Filter Topology

namespace PathwiseVolatility

/-- Definition 3.9 (The exit-time functional), eq. (3.16): `E (φ) (x) = inf {t > 0 : φ (t) > x}`.
The thesis applies `E` to paths with `sup φ = ∞`, for which the set is never empty. -/
noncomputable def exitT (φ : ℝ → ℝ) (x : ℝ) : ℝ := sInf {t | 0 < t ∧ x < φ t}

/-- The supremum functional of eq. (3.27), `M (φ) (t) = sup {0 ∨ φ (s) : s ∈ [0, t]}`. -/
noncomputable def supF (φ : ℝ → ℝ) (t : ℝ) : ℝ := sSup ((fun s => max 0 (φ s)) '' Icc 0 t)

/-- Definition 3.10, the set `N`: the non-decreasing, unbounded paths in `C₀ (ℝ₊, ℝ₊)`. -/
structure InN (φ : ℝ → ℝ) : Prop where
  zero : φ 0 = 0
  continuousOn : ContinuousOn φ (Ici 0)
  monotoneOn : MonotoneOn φ (Ici 0)
  unbounded : ∀ M, ∃ t, 0 ≤ t ∧ M < φ t

/-- `‖w‖_{[0, X]} = sup_{[0, X]} |w|`. -/
noncomputable def supOn (w : ℝ → ℝ) (X : ℝ) : ℝ := sSup ((fun x => |w x|) '' Icc 0 X)

/-- The seminorm of eq. (1.12), `‖w‖_{ℝ₊} = Σ_{n ≥ 1} 2^{-n} (1 ∧ ‖w‖_{[0, n]})`, which
characterises uniform convergence on compacts. -/
noncomputable def uniNorm (w : ℝ → ℝ) : ℝ :=
  ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) * min 1 (supOn w (n + 1))

/-- Definition 3.12 (Exit-time metric), eq. (3.17): `d_Φ̄ (φ₁, φ₂) = ‖E (φ₂) - E (φ₁)‖_{ℝ₊}`. -/
noncomputable def exitMetric (φ₁ φ₂ : ℝ → ℝ) : ℝ := uniNorm fun x => exitT φ₂ x - exitT φ₁ x

/-! ### The seminorm -/

theorem supOn_nonneg (w : ℝ → ℝ) (X : ℝ) : 0 ≤ supOn w X :=
  Real.sSup_nonneg fun _ ⟨_, _, h⟩ => h ▸ abs_nonneg _

theorem supOn_le {w : ℝ → ℝ} {X η : ℝ} (hX : 0 ≤ X) (h : ∀ x ∈ Icc 0 X, |w x| ≤ η) :
    supOn w X ≤ η :=
  csSup_le ⟨_, 0, ⟨le_rfl, hX⟩, rfl⟩ (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)

theorem summable_uniNorm_terms (w : ℝ → ℝ) :
    Summable fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1) * min 1 (supOn w (n + 1)) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (by positivity)
    (le_min zero_le_one (supOn_nonneg _ _))) (fun n => ?_)
    ((summable_geometric_two).mul_left (1 / 2))
  calc (1 / 2 : ℝ) ^ (n + 1) * min 1 (supOn w (n + 1)) ≤ (1 / 2 : ℝ) ^ (n + 1) * 1 :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
    _ = 1 / 2 * (1 / 2) ^ n := by ring

/-- The bound after eq. (3.17): if `|w| ≤ η` on `[0, N]`, then `‖w‖_{ℝ₊} ≤ η + 2^{-N}`. -/
theorem uniNorm_le {w : ℝ → ℝ} {η : ℝ} (hη : 0 ≤ η) (N : ℕ)
    (h : ∀ x ∈ Icc 0 (N : ℝ), |w x| ≤ η) : uniNorm w ≤ η + (1 / 2) ^ N := by
  set a : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ (n + 1) * min 1 (supOn w (n + 1)) with ha
  have hs := summable_uniNorm_terms w
  rw [uniNorm, ← hs.sum_add_tsum_nat_add N]
  have h1 : ∑ i ∈ Finset.range N, a i ≤ η := by
    calc ∑ i ∈ Finset.range N, a i ≤ ∑ i ∈ Finset.range N, (1 / 2 : ℝ) ^ (i + 1) * η := by
          refine Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine (min_le_right _ _).trans (supOn_le (by positivity) fun x hx => h x ⟨hx.1, ?_⟩)
          have : (i : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.mp hi
          linarith [hx.2]
      _ = η * ∑ i ∈ Finset.range N, (1 / 2 : ℝ) ^ (i + 1) := by rw [Finset.mul_sum]; ring_nf
      _ ≤ η * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ hη
          have := sum_geometric_two_le N
          calc ∑ i ∈ Finset.range N, (1 / 2 : ℝ) ^ (i + 1)
              = 1 / 2 * ∑ i ∈ Finset.range N, (1 / 2 : ℝ) ^ i := by
                rw [Finset.mul_sum]; ring_nf
            _ ≤ 1 / 2 * 2 := by linarith
            _ = 1 := by norm_num
      _ = η := mul_one η
  have h2 : ∑' n, a (n + N) ≤ (1 / 2) ^ N := by
    have hb : Summable fun n : ℕ => (1 / 2 : ℝ) ^ (n + N + 1) :=
      ((summable_geometric_two).mul_left ((1 / 2) ^ (N + 1))).congr fun n => by ring
    calc ∑' n, a (n + N) ≤ ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + N + 1) := by
          refine Summable.tsum_le_tsum (fun n => ?_) ((summable_nat_add_iff N).mpr hs) hb
          calc a (n + N) ≤ (1 / 2 : ℝ) ^ (n + N + 1) * 1 :=
                mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
            _ = _ := mul_one _
      _ = (1 / 2) ^ (N + 1) * ∑' n : ℕ, (1 / 2 : ℝ) ^ n := by
          rw [← tsum_mul_left]; congr 1; ext n; ring
      _ = (1 / 2) ^ N := by rw [tsum_geometric_two]; ring
  linarith

/-- Uniform convergence on each `[0, X]` gives convergence in `‖·‖_{ℝ₊}`. -/
theorem tendsto_uniNorm {w : ℕ → ℝ → ℝ}
    (h : ∀ X η, 0 < η → ∀ᶠ n in atTop, ∀ x ∈ Icc 0 X, |w n x| ≤ η) :
    Tendsto (fun n => uniNorm (w n)) atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (half_pos hε) (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨K, hK⟩ := (h N (ε / 4) (by positivity)).exists_forall_of_atTop
  refine ⟨K, fun n hn => ?_⟩
  have h0 : 0 ≤ uniNorm (w n) :=
    tsum_nonneg fun k => mul_nonneg (by positivity) (le_min zero_le_one (supOn_nonneg _ _))
  have := uniNorm_le (by positivity) N (hK n hn)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  linarith

/-- Convergence on `(Φ̄, d_Φ̄)` follows from uniform convergence of the exit times on each
`[0, X]`. -/
theorem tendsto_exitMetric {φ : ℕ → ℝ → ℝ} {φ₀ : ℝ → ℝ}
    (h : ∀ X η, 0 < η → ∀ᶠ n in atTop, ∀ x ∈ Icc 0 X, |exitT φ₀ x - exitT (φ n) x| ≤ η) :
    Tendsto (fun n => exitMetric (φ n) φ₀) atTop (𝓝 0) :=
  tendsto_uniNorm h

/-! ### The exit-time functional -/

variable {φ ψ : ℝ → ℝ}

/-- On `Φ`, `E` is the inverse map: `E (φ) = φ⁻¹` on `ℝ₊`. -/
theorem exitT_eq_invPath (hφ : InΦ φ) {x : ℝ} (hx : 0 ≤ x) : exitT φ x = invPath φ x := by
  have hm := hφ.strictMonoOn
  have hset : {t | 0 < t ∧ x < φ t} = Ioi (invPath φ x) := by
    ext t
    simp only [mem_ofPred_eq, mem_Ioi]
    constructor
    · rintro ⟨ht, hxt⟩
      by_contra hle
      push Not at hle
      have := hm.monotoneOn (mem_Ici.mpr ht.le) (invPath_nonneg hφ.bijOn hx) hle
      rw [apply_invPath hφ.bijOn hx] at this
      linarith
    · intro ht
      have hψ := invPath_nonneg hφ.bijOn hx
      have ht0 : 0 < t := lt_of_le_of_lt hψ ht
      refine ⟨ht0, ?_⟩
      have := hm hψ (mem_Ici.mpr ht0.le) ht
      rwa [apply_invPath hφ.bijOn hx] at this
  rw [exitT, hset, csInf_Ioi]

/-- `E` is non-decreasing, for paths unbounded above on `(0, ∞)`. -/
theorem exitT_mono (hφ : ∀ M, ∃ t, 0 < t ∧ M < φ t) {x y : ℝ} (hxy : x ≤ y) :
    exitT φ x ≤ exitT φ y := by
  obtain ⟨t, ht, hyt⟩ := hφ y
  exact csInf_le_csInf ⟨0, fun _ hs => hs.1.le⟩ ⟨t, ht, hyt⟩ fun s hs => ⟨hs.1, hxy.trans_lt hs.2⟩

/-- `E` reverses order: if `φ ≤ ψ` on `(0, ∞)`, then `E (ψ) ≤ E (φ)`. -/
theorem exitT_le_of_le (hφ : ∀ M, ∃ t, 0 < t ∧ M < φ t) (hle : ∀ t, 0 < t → φ t ≤ ψ t) (x : ℝ) :
    exitT ψ x ≤ exitT φ x := by
  obtain ⟨t, ht, hxt⟩ := hφ x
  exact csInf_le_csInf ⟨0, fun _ hs => hs.1.le⟩ ⟨t, ht, hxt⟩ fun s hs =>
    ⟨hs.1, hs.2.trans_le (hle s hs.1)⟩

theorem exitT_nonneg (φ : ℝ → ℝ) (x : ℝ) : 0 ≤ exitT φ x :=
  Real.sInf_nonneg fun _ hs => hs.1.le

end PathwiseVolatility
