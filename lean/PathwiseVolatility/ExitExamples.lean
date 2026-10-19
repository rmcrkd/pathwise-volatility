/-
Copyright (c) 2026 Ryan McCrickerd. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCrickerd
-/
import PathwiseVolatility.Excursion

/-!
# Examples 3.19 and 3.27: pathwise CIR to IG, and Heston to NIG

Example 3.19: with `g_n (t, x) = σ w (x) + κ (θ t - x) + v / n`, the integrated CIR paths `φ_n`
solving `x' = n g_n (t, x)`, `x (0) = 0` converge on `(Φ̄, d_Φ̄)` to the IG path
`φ̄₀ (t) = inf {x > 0 : κ x - σ w (x) > κ θ t}`. As in Theorem 3.17, the sequence is indexed from
`0` here, so `g_{n + 1}` and `x' = (n + 1) g_{n + 1}` appear.

Example 3.27: the Heston price paths `exp (w_ρ (φ_n (t)) - φ_n (t) / 2)` then converge on
`(E, d_E)` to the filled composition of `x ↦ exp (w_ρ (x) - x / 2)` with `φ̄₀`.
-/

open Set Filter Topology

namespace PathwiseVolatility

variable {σ κ θ v : ℝ} {w : ℝ → ℝ}

/-- The functions of Example 3.19, `g (t, x) = σ w (x) + κ (θ t - x) + c`: `c = v / n` gives `g_n`,
and `c = 0` gives `g₀`. -/
def cirG (σ κ θ c : ℝ) (w : ℝ → ℝ) (t x : ℝ) : ℝ := σ * w x + κ * (θ * t - x) + c

theorem cirG_eq (σ κ θ c : ℝ) (w : ℝ → ℝ) (t x : ℝ) :
    cirG σ κ θ c w t x = κ * θ * t + c - (κ * x - σ * w x) := by
  unfold cirG; ring

/-- `g_n ∈ G` for `c ≥ 0`, when `κ x - σ w (x)` is unbounded above. -/
theorem inG_cirG (hκ : 0 < κ) (hθ : 0 < θ) {c : ℝ} (hc : 0 ≤ c) (hw : ContinuousOn w (Ici 0))
    (hw0 : w 0 = 0) (hunb : ∀ M, ∃ x, 0 ≤ x ∧ M < κ * x - σ * w x) :
    InG (cirG σ κ θ c w) := by
  have hκθ := mul_pos hκ hθ
  refine ⟨?_, ?_, fun x _ s _ t _ hst => ?_, fun t _ => ?_, fun x _ => ?_⟩
  · have hw' : ContinuousOn (fun p : ℝ × ℝ => w p.2) (Ici 0 ×ˢ Ici 0) :=
      hw.comp continuous_snd.continuousOn fun p hp => hp.2
    show ContinuousOn (fun p : ℝ × ℝ => σ * w p.2 + κ * (θ * p.1 - p.2) + c) _
    exact ((continuousOn_const.mul hw').add (continuousOn_const.mul
      ((continuousOn_const.mul continuous_fst.continuousOn).sub
        continuous_snd.continuousOn))).add continuousOn_const
  · simp [cirG, hw0, hc]
  · show cirG σ κ θ c w s x < cirG σ κ θ c w t x
    rw [cirG_eq, cirG_eq]
    linarith [mul_lt_mul_of_pos_left hst hκθ]
  · obtain ⟨x, hx, hM⟩ := hunb (κ * θ * t + c)
    exact ⟨x, hx, by rw [cirG_eq]; linarith⟩
  · have h0 : κ * θ ≠ 0 := hκθ.ne'
    obtain ⟨A, hA⟩ : ∃ A, κ * θ * A = κ * x - σ * w x - c :=
      ⟨(κ * x - σ * w x - c) / (κ * θ), by field_simp⟩
    have hlt : A < max 0 A + 1 := by linarith [le_max_right 0 A]
    refine ⟨max 0 A + 1, by positivity, ?_⟩
    rw [cirG_eq]
    linarith [mul_lt_mul_of_pos_left hlt hκθ]

/-- Example 3.19, conversely: `g ∈ G` needs `κ x - σ w (x)` to be unbounded above. -/
theorem unbounded_of_inG_cirG (hκ : 0 < κ) (hθ : 0 < θ) {c : ℝ} (hg : InG (cirG σ κ θ c w)) :
    ∀ M, ∃ x, 0 ≤ x ∧ M < κ * x - σ * w x := by
  intro M
  have hκθ : κ * θ ≠ 0 := (mul_pos hκ hθ).ne'
  obtain ⟨x, hx, hneg⟩ := hg.exists_neg ((|M| + |c|) / (κ * θ))
    (div_nonneg (by positivity) (mul_pos hκ hθ).le)
  rw [cirG_eq] at hneg
  have e : κ * θ * ((|M| + |c|) / (κ * θ)) = |M| + |c| := by field_simp
  exact ⟨x, hx, by linarith [le_abs_self M, neg_abs_le c]⟩

/-- Example 3.19: `g ∈ G` exactly when `κ x - σ w (x)` is unbounded above. -/
theorem inG_cirG_iff (hκ : 0 < κ) (hθ : 0 < θ) {c : ℝ} (hc : 0 ≤ c) (hw : ContinuousOn w (Ici 0))
    (hw0 : w 0 = 0) : InG (cirG σ κ θ c w) ↔ ∀ M, ∃ x, 0 ≤ x ∧ M < κ * x - σ * w x :=
  ⟨unbounded_of_inG_cirG hκ hθ, inG_cirG hκ hθ hc hw hw0⟩

/-- Example 3.19: the condition is equivalent to `φ̄₀` being finite, the set
`{x > 0 : κ x - σ w (x) > κ θ t}` being nonempty for each `t ≥ 0`. -/
theorem unbounded_iff_bound_finite (hκ : 0 < κ) (hθ : 0 < θ) (hw0 : w 0 = 0) :
    (∀ M, ∃ x, 0 ≤ x ∧ M < κ * x - σ * w x) ↔
      ∀ t, 0 ≤ t → {x | 0 < x ∧ κ * θ * t < κ * x - σ * w x}.Nonempty := by
  constructor
  · intro h t ht
    obtain ⟨x, hx, hM⟩ := h (κ * θ * t)
    refine ⟨x, lt_of_le_of_ne hx fun h0 => ?_, hM⟩
    rw [← h0, hw0] at hM
    nlinarith [mul_nonneg (mul_pos hκ hθ).le ht]
  · intro h M
    have hκθ : κ * θ ≠ 0 := (mul_pos hκ hθ).ne'
    obtain ⟨x, hx, hlt⟩ := h (|M| / (κ * θ)) (div_nonneg (abs_nonneg M) (mul_pos hκ hθ).le)
    have e : κ * θ * (|M| / (κ * θ)) = |M| := by field_simp
    exact ⟨x, hx.le, by linarith [le_abs_self M]⟩

/-- `g_{n + 1} → g₀` uniformly on `ℝ₊²`: `g_{n + 1} - g₀ = v / (n + 1)`. -/
theorem cirG_conv (hv : 0 < v) :
    ∀ T X η, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ Icc (0 : ℝ) X,
      |cirG σ κ θ (v / ((n : ℝ) + 1)) w t x - cirG σ κ θ 0 w t x| < η := by
  intro T X η hη
  obtain ⟨N, hN⟩ := exists_nat_gt (v / η)
  filter_upwards [eventually_ge_atTop N] with n hn t _ x _
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  rw [cirG_eq, cirG_eq, show ∀ a b c : ℝ, a + b - c - (a + 0 - c) = b from fun _ _ _ => by ring,
    abs_of_pos (div_pos hv (by positivity)), div_lt_iff₀ (by positivity)]
  have := (div_lt_iff₀ hη).mp (show v / η < (n : ℝ) + 1 by linarith)
  linarith

/-- Example 3.19 (Pathwise integrated CIR to IG): `g_n, g₀ ∈ G`, `g_n → g₀` uniformly, `φ̄₀` is
`t ↦ inf {x > 0 : κ x - σ w (x) > κ θ t}`, and the solutions `φ_n` converge to it on `(Φ̄, d_Φ̄)`.
The thesis also assumes `σ > 0`, which is not needed. -/
theorem cir_to_ig (hκ : 0 < κ) (hθ : 0 < θ) (hv : 0 < v) (hw : ContinuousOn w (Ici 0))
    (hw0 : w 0 = 0) (hunb : ∀ M, ∃ x, 0 ≤ x ∧ M < κ * x - σ * w x) {φ : ℕ → ℝ → ℝ}
    (hφ : ∀ n : ℕ,
      IsGlobalSolution (fun t x => ((n : ℝ) + 1) * cirG σ κ θ (v / ((n : ℝ) + 1)) w t x) (φ n)) :
    (∀ n : ℕ, InG (cirG σ κ θ (v / ((n : ℝ) + 1)) w)) ∧ InG (cirG σ κ θ 0 w) ∧
    (∀ t, barG (cirG σ κ θ 0 w) t = sInf {x | 0 < x ∧ κ * θ * t < κ * x - σ * w x}) ∧
    Tendsto (fun n => exitMetric (φ n) (barG (cirG σ κ θ 0 w))) atTop (𝓝 0) := by
  have hG : ∀ n : ℕ, InG (cirG σ κ θ (v / ((n : ℝ) + 1)) w) := fun n =>
    inG_cirG hκ hθ (div_pos hv (by positivity)).le hw hw0 hunb
  have hg₀ : InG (cirG σ κ θ 0 w) := inG_cirG hκ hθ le_rfl hw hw0 hunb
  refine ⟨hG, hg₀, fun t => ?_, (exit_limit hg₀ hG (cirG_conv hv) hφ).2⟩
  unfold barG
  congr 1
  ext x
  simp only [mem_ofPred_eq, cirG_eq, add_zero, sub_neg]

/-- Example 3.27 (Pathwise Heston to NIG): with `w_ρ = ρ w₁ + √(1 - ρ²) w₀` and `φ_n` the paths of
Example 3.19 driven by `w₁`, the Heston price paths `eₙ (t) = {exp (w_ρ (φ_n (t)) - φ_n (t) / 2)}`
converge on `(E, d_E)` to `w • φ̄₀ ∈ E`, where `w (x) = exp (w_ρ (x) - x / 2)`. The thesis takes
`ρ ∈ [-1, 1]` and `w₀ (0) = 0`, which are not needed. -/
theorem heston_to_nig (hκ : 0 < κ) (hθ : 0 < θ) (hv : 0 < v) (hw : ContinuousOn w (Ici 0))
    (hw0 : w 0 = 0) (hunb : ∀ M, ∃ x, 0 ≤ x ∧ M < κ * x - σ * w x) {w₀ : ℝ → ℝ}
    (hw₀ : ContinuousOn w₀ (Ici 0)) (ρ : ℝ) {φ : ℕ → ℝ → ℝ}
    (hφ : ∀ n : ℕ,
      IsGlobalSolution (fun t x => ((n : ℝ) + 1) * cirG σ κ θ (v / ((n : ℝ) + 1)) w t x) (φ n)) :
    Tendsto (fun n => excMetric
      (fun t => {Real.exp (ρ * w (φ n t) + √(1 - ρ ^ 2) * w₀ (φ n t) - φ n t / 2)})
      (fillComp (fun x => Real.exp (ρ * w x + √(1 - ρ ^ 2) * w₀ x - x / 2))
        (barG (cirG σ κ θ 0 w)))) atTop (𝓝 0) ∧
    InE (fillComp (fun x => Real.exp (ρ * w x + √(1 - ρ ^ 2) * w₀ x - x / 2))
      (barG (cirG σ κ θ 0 w))) := by
  have hc : ContinuousOn (fun x => Real.exp (ρ * w x + √(1 - ρ ^ 2) * w₀ x - x / 2)) (Ici 0) :=
    (((continuousOn_const.mul hw).add (continuousOn_const.mul hw₀)).sub
      (continuousOn_id.div_const 2)).rexp
  exact graph_hausdorff (g₀ := cirG σ κ θ 0 w) (G := fun n => cirG σ κ θ (v / ((n : ℝ) + 1)) w)
    (φ := φ) (w := fun x => Real.exp (ρ * w x + √(1 - ρ ^ 2) * w₀ x - x / 2))
    (inG_cirG hκ hθ le_rfl hw hw0 hunb)
    (fun n => inG_cirG hκ hθ (div_pos hv (by positivity)).le hw hw0 hunb) (cirG_conv hv) hφ hc

end PathwiseVolatility
