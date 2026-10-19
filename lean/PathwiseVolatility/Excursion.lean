/-
Copyright (c) 2026 Ryan McCrickerd. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCrickerd
-/
import PathwiseVolatility.ExitBijection

/-!
# Section 3.5: excursionary limits

Definitions 3.21 (the set `E` of compact interval-valued paths) and 3.22 (the excursionary metric
`d_E`, through Hausdorff distances between extended graphs), and Theorem 3.26 (excursionary
composite limits).

The thesis measures distances in `ℝ²` with the Euclidean norm; Mathlib's `ℝ × ℝ` carries the
maximum norm. The two are equivalent, so `d_E` defines the same convergence. Eq. (3.34), which
turns uniform convergence of parametric representations into convergence on `(E, d_E)`, is proved
here as `tendsto_excMetric_of_param`, with care at the endpoint `T`: a point of one graph whose
partner has passed `T` is matched with the vertical line `{T} × ℝ`.
-/

open Set Filter Topology

namespace PathwiseVolatility

/-- Definition 3.21 (Set `E` of paths): paths returning a compact interval `[e₋ (t), e₊ (t)]` at
each `t ∈ ℝ₊`. -/
def InE (e : ℝ → Set ℝ) : Prop := ∀ t, 0 ≤ t → ∃ a b, a ≤ b ∧ e t = Icc a b

/-- The graph `Γ_T (e)` of eq. (3.32) over `[0, T]`. -/
def excGraph (e : ℝ → Set ℝ) (T : ℝ) : Set (ℝ × ℝ) := {p | p.1 ∈ Icc 0 T ∧ p.2 ∈ e p.1}

/-- The extended graph `Γ*_T (e) = Γ_T (e) ∪ {T} × ℝ`. -/
def excGraphStar (e : ℝ → Set ℝ) (T : ℝ) : Set (ℝ × ℝ) := excGraph e T ∪ {T} ×ˢ univ

/-- Definition 3.22: the excursionary pseudometric `d_{E, T}`, the Hausdorff distance between the
extended graphs. -/
noncomputable def excT (e₁ e₂ : ℝ → Set ℝ) (T : ℝ) : ENNReal :=
  Metric.hausdorffEDist (excGraphStar e₁ T) (excGraphStar e₂ T)

/-- Definition 3.22 (Excursionary metric): `d_E = Σ_{n ≥ 1} 2^{-n} (1 ∧ d_{E, n})`. -/
noncomputable def excMetric (e₁ e₂ : ℝ → Set ℝ) : ℝ :=
  ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) * (min 1 (excT e₁ e₂ (n + 1))).toReal

/-- `(τ, σ)` parameterises `e`: the graph of `e` over `ℝ₊` is `{(τ (x), σ (x)) : x ∈ ℝ₊}`. -/
def IsParam (e : ℝ → Set ℝ) (τ σ : ℝ → ℝ) : Prop :=
  ∀ t, 0 ≤ t → ∀ y, y ∈ e t ↔ ∃ x, 0 ≤ x ∧ τ x = t ∧ σ x = y

/-! ### From parametric representations to `(E, d_E)` -/

/-- `Σ 2^{-(n+1)} aₙ ≤ η + 2^{-N}` when `0 ≤ aₙ ≤ 1` and `aₙ ≤ η` for `n < N`. -/
theorem weighted_tsum_le {a : ℕ → ℝ} {η : ℝ} (h0 : ∀ n, 0 ≤ a n) (h1 : ∀ n, a n ≤ 1) (hη : 0 ≤ η)
    (N : ℕ) (h : ∀ n < N, a n ≤ η) : ∑' n, (1 / 2 : ℝ) ^ (n + 1) * a n ≤ η + (1 / 2) ^ N := by
  have hs : Summable fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1) * a n :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (by positivity) (h0 n))
      (fun n => by
        calc (1 / 2 : ℝ) ^ (n + 1) * a n ≤ (1 / 2 : ℝ) ^ (n + 1) * 1 :=
              mul_le_mul_of_nonneg_left (h1 n) (by positivity)
          _ = 1 / 2 * (1 / 2) ^ n := by ring)
      ((summable_geometric_two).mul_left (1 / 2))
  rw [← hs.sum_add_tsum_nat_add N]
  have hhead : ∑ i ∈ Finset.range N, (1 / 2 : ℝ) ^ (i + 1) * a i ≤ η := by
    calc ∑ i ∈ Finset.range N, (1 / 2 : ℝ) ^ (i + 1) * a i
        ≤ ∑ i ∈ Finset.range N, (1 / 2 : ℝ) ^ (i + 1) * η :=
          Finset.sum_le_sum fun i hi =>
            mul_le_mul_of_nonneg_left (h i (Finset.mem_range.mp hi)) (by positivity)
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
  have htail : ∑' n, (1 / 2 : ℝ) ^ (n + N + 1) * a (n + N) ≤ (1 / 2) ^ N := by
    have hb : Summable fun n : ℕ => (1 / 2 : ℝ) ^ (n + N + 1) :=
      ((summable_geometric_two).mul_left ((1 / 2) ^ (N + 1))).congr fun n => by ring
    calc ∑' n, (1 / 2 : ℝ) ^ (n + N + 1) * a (n + N) ≤ ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + N + 1) :=
          Summable.tsum_le_tsum (fun n => by
            calc (1 / 2 : ℝ) ^ (n + N + 1) * a (n + N) ≤ (1 / 2 : ℝ) ^ (n + N + 1) * 1 :=
                  mul_le_mul_of_nonneg_left (h1 _) (by positivity)
              _ = _ := mul_one _) ((summable_nat_add_iff N).mpr hs) hb
      _ = (1 / 2) ^ (N + 1) * ∑' n : ℕ, (1 / 2 : ℝ) ^ n := by
          rw [← tsum_mul_left]; congr 1; ext n; ring
      _ = (1 / 2) ^ N := by rw [tsum_geometric_two]; ring
  linarith

/-- Convergence of every term gives convergence of `Σ 2^{-(n+1)} a_{m, n}`, for `0 ≤ a ≤ 1`. -/
theorem tendsto_weighted_tsum {a : ℕ → ℕ → ℝ} (h0 : ∀ m n, 0 ≤ a m n) (h1 : ∀ m n, a m n ≤ 1)
    (h : ∀ n η, 0 < η → ∀ᶠ m in atTop, a m n ≤ η) :
    Tendsto (fun m => ∑' n, (1 / 2 : ℝ) ^ (n + 1) * a m n) atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (half_pos hε) (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨K, hK⟩ := ((Finset.range N).eventually_all.mpr fun n _ =>
    h n (ε / 4) (by positivity)).exists_forall_of_atTop
  refine ⟨K, fun m hm => ?_⟩
  have hnn : 0 ≤ ∑' n, (1 / 2 : ℝ) ^ (n + 1) * a m n :=
    tsum_nonneg fun n => mul_nonneg (by positivity) (h0 m n)
  have := weighted_tsum_le (h0 m) (h1 m) (by positivity : (0 : ℝ) ≤ ε / 4) N
    fun n hn => hK m hm n (Finset.mem_range.mpr hn)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  linarith

/-- Convergence of each `d_{E, T}` gives convergence on `(E, d_E)`. -/
theorem tendsto_excMetric {e : ℕ → ℝ → Set ℝ} {e₀ : ℝ → Set ℝ}
    (h : ∀ T η, 0 ≤ T → 0 < η → ∀ᶠ n in atTop, excT (e n) e₀ T ≤ ENNReal.ofReal η) :
    Tendsto (fun n => excMetric (e n) e₀) atTop (𝓝 0) :=
  tendsto_weighted_tsum (fun _ _ => ENNReal.toReal_nonneg)
    (fun m n => by
      have := ENNReal.toReal_mono ENNReal.one_ne_top (min_le_left 1 (excT (e m) e₀ ((n : ℝ) + 1)))
      rwa [ENNReal.toReal_one] at this)
    fun n η hη => (h (n + 1) η (by positivity) hη).mono fun m hm =>
      ENNReal.toReal_le_of_le_ofReal hη.le ((min_le_right _ _).trans hm)

variable {e₁ e₂ : ℝ → Set ℝ} {τ₁ σ₁ τ₂ σ₂ : ℝ → ℝ} {T X η : ℝ}

/-- Each point of `Γ*_T (e₁)` is within `η` of `Γ*_T (e₂)`, when the representations are within
`η` on the part `[0, X]` of their domains that reaches `[0, T]`. -/
theorem exists_near_of_param (h₁ : IsParam e₁ τ₁ σ₁) (h₂ : IsParam e₂ τ₂ σ₂)
    (hτ₂ : ∀ x, 0 ≤ x → 0 ≤ τ₂ x) (hX : ∀ x, 0 ≤ x → τ₁ x ≤ T → x ≤ X) (hη : 0 ≤ η)
    (hτ : ∀ x ∈ Icc 0 X, |τ₁ x - τ₂ x| ≤ η) (hσ : ∀ x ∈ Icc 0 X, |σ₁ x - σ₂ x| ≤ η) :
    ∀ p ∈ excGraphStar e₁ T, ∃ q ∈ excGraphStar e₂ T, edist p q ≤ ENNReal.ofReal η := by
  rintro ⟨t, y⟩ (⟨ht, hy⟩ | ⟨hTt, -⟩)
  · change t ∈ Icc 0 T at ht
    change y ∈ e₁ t at hy
    obtain ⟨x, hx, rfl, rfl⟩ := (h₁ _ ht.1 y).mp hy
    have hxX : x ∈ Icc 0 X := ⟨hx, hX x hx ht.2⟩
    rcases le_or_gt (τ₂ x) T with hle | hgt
    · refine ⟨(τ₂ x, σ₂ x), Or.inl ⟨⟨hτ₂ x hx, hle⟩, (h₂ _ (hτ₂ x hx) _).mpr ⟨x, hx, rfl, rfl⟩⟩,
        ?_⟩
      rw [edist_le_ofReal hη, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      exact max_le (hτ x hxX) (hσ x hxX)
    · refine ⟨(T, σ₁ x), Or.inr ⟨rfl, mem_univ _⟩, ?_⟩
      rw [edist_le_ofReal hη, Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_self, abs_zero]
      refine max_le ?_ hη
      have := hτ x hxX
      rw [abs_le] at this ⊢
      constructor <;> linarith [ht.2]
  · exact ⟨(t, y), Or.inr ⟨hTt, mem_univ _⟩, by simp⟩

/-- `d_{E, T} (e₁, e₂) ≤ η` from parametric representations within `η` on `[0, X]`. -/
theorem excT_le_of_param (h₁ : IsParam e₁ τ₁ σ₁) (h₂ : IsParam e₂ τ₂ σ₂)
    (hτ₁ : ∀ x, 0 ≤ x → 0 ≤ τ₁ x) (hτ₂ : ∀ x, 0 ≤ x → 0 ≤ τ₂ x)
    (hX₁ : ∀ x, 0 ≤ x → τ₁ x ≤ T → x ≤ X) (hX₂ : ∀ x, 0 ≤ x → τ₂ x ≤ T → x ≤ X) (hη : 0 ≤ η)
    (hτ : ∀ x ∈ Icc 0 X, |τ₂ x - τ₁ x| ≤ η) (hσ : ∀ x ∈ Icc 0 X, |σ₂ x - σ₁ x| ≤ η) :
    excT e₁ e₂ T ≤ ENNReal.ofReal η := by
  refine Metric.hausdorffEDist_le_of_mem_edist
    (exists_near_of_param h₁ h₂ hτ₂ hX₁ hη (fun x hx => ?_) fun x hx => ?_)
    (exists_near_of_param h₂ h₁ hτ₁ hX₂ hη hτ hσ)
  · rw [abs_sub_comm]; exact hτ x hx
  · rw [abs_sub_comm]; exact hσ x hx

/-- Eq. (3.34): uniform convergence on compacts of parametric representations `(τₙ, σₙ)` of `eₙ`
to a representation `(τ₀, σ₀)` of `e₀` gives `d_E (eₙ, e₀) → 0`, for non-decreasing temporal
components with `τ₀` unbounded. -/
theorem tendsto_excMetric_of_param {e : ℕ → ℝ → Set ℝ} {e₀ : ℝ → Set ℝ} {τ σ : ℕ → ℝ → ℝ}
    {τ₀ σ₀ : ℝ → ℝ} (hp : ∀ n, IsParam (e n) (τ n) (σ n)) (hp₀ : IsParam e₀ τ₀ σ₀)
    (hτn : ∀ n x, 0 ≤ x → 0 ≤ τ n x) (hτ₀ : ∀ x, 0 ≤ x → 0 ≤ τ₀ x)
    (hmono : ∀ n, MonotoneOn (τ n) (Ici 0)) (hmono₀ : MonotoneOn τ₀ (Ici 0))
    (hunb : ∀ M, ∃ x, 0 ≤ x ∧ M < τ₀ x)
    (hτ : ∀ X η, 0 < η → ∀ᶠ n in atTop, ∀ x ∈ Icc 0 X, |τ₀ x - τ n x| ≤ η)
    (hσ : ∀ X η, 0 < η → ∀ᶠ n in atTop, ∀ x ∈ Icc 0 X, |σ₀ x - σ n x| ≤ η) :
    Tendsto (fun n => excMetric (e n) e₀) atTop (𝓝 0) := by
  refine tendsto_excMetric fun T η _ hη => ?_
  obtain ⟨X, hX0, hXT⟩ := hunb (T + 1)
  have hX₀ : ∀ x, 0 ≤ x → τ₀ x ≤ T → x ≤ X := fun x hx hxT => not_lt.mp fun hlt => by
    linarith [hmono₀ (mem_Ici.mpr hX0) (mem_Ici.mpr hx) hlt.le]
  filter_upwards [hτ X (min η (1 / 2)) (by positivity), hσ X η hη] with n hτn' hσn
  have hXn : ∀ x, 0 ≤ x → τ n x ≤ T → x ≤ X := fun x hx hxT => not_lt.mp fun hlt => by
    have h1 := hmono n (mem_Ici.mpr hX0) (mem_Ici.mpr hx) hlt.le
    have h2 := abs_le.mp (hτn' X ⟨hX0, le_rfl⟩)
    linarith [min_le_right η (1 / 2)]
  exact excT_le_of_param (hp n) hp₀ (hτn n) hτ₀ hXn hX₀ hη.le
    (fun x hx => (hτn' x hx).trans (min_le_left _ _)) hσn

/-! ### Composite limits -/

variable {g₀ : ℝ → ℝ → ℝ} {G : ℕ → ℝ → ℝ → ℝ} {φ : ℕ → ℝ → ℝ}

/-- The interval `φ̄_* (t) = [φ̄ (t₋), φ̄ (t)]`. -/
def jumpSet (φ : ℝ → ℝ) (t : ℝ) : Set ℝ := Icc (leftVal φ t) (φ t)

/-- The filled composition `(w • φ̄) (t) = {w (x) : x ∈ [φ̄ (t₋), φ̄ (t)]}` of eq. (3.31). -/
def fillComp (w φ : ℝ → ℝ) (t : ℝ) : Set ℝ := w '' jumpSet φ t

/-- Theorem 3.26 (Excursionary composite limits): under the assumptions of Theorem 3.17, and for
`w` continuous on `ℝ₊`, the composite paths `eₙ (t) = {w (φ_n (t))}` converge on `(E, d_E)` to
`w • φ̄₀ ∈ E`. -/
theorem graph_hausdorff (hg₀ : InG g₀) (hG : ∀ n, InG (G n))
    (hconv : ∀ T X η, 0 < η → ∀ᶠ n in atTop, ∀ t ∈ Icc 0 T, ∀ x ∈ Icc 0 X, |G n t x - g₀ t x| < η)
    (hφ : ∀ n : ℕ, IsGlobalSolution (fun t x => ((n : ℝ) + 1) * G n t x) (φ n)) {w : ℝ → ℝ}
    (hw : ContinuousOn w (Ici 0)) :
    Tendsto (fun n => excMetric (fun t => {w (φ n t)}) (fillComp w (barG g₀))) atTop (𝓝 0) ∧
    InE (fillComp w (barG g₀)) := by
  have hb := hg₀.inΦbar_barG
  have hΦ : ∀ n, InΦ (φ n) := fun n => ((hG n).const_mul (by positivity)).mem_Φ (hφ n)
  have hN := hb.inN_exitT
  have hc : ∀ t, ContinuousOn w (jumpSet (barG g₀) t) := fun t =>
    hw.mono fun x hx => mem_Ici.mpr ((leftVal_nonneg hb.nonneg t).trans hx.1)
  refine ⟨tendsto_excMetric_of_param (τ := fun n => invPath (φ n)) (σ := fun _ => w)
    (τ₀ := exitT (barG g₀)) (σ₀ := w) (fun n t ht y => ?_) (fun t ht y => ?_)
    (fun n x hx => invPath_nonneg (hΦ n).bijOn hx) (fun x _ => exitT_nonneg _ x)
    (fun n => (strictMonoOn_invPath (hΦ n).bijOn (hΦ n).strictMonoOn).monotoneOn) hN.monotoneOn
    hN.unbounded (exit_limit hg₀ hG hconv hφ).1 fun X η hη => Eventually.of_forall fun n x _ => by
      simp [hη.le], fun t ht => ?_⟩
  · simp only [mem_singleton_iff]
    constructor
    · rintro rfl
      exact ⟨φ n t, (hΦ n).bijOn.mapsTo ht, invPath_apply (hΦ n).bijOn ht, rfl⟩
    · rintro ⟨x, hx, rfl, rfl⟩
      rw [apply_invPath (hΦ n).bijOn hx]
  · constructor
    · rintro ⟨x, hx, rfl⟩
      have hx0 := (leftVal_nonneg hb.nonneg t).trans hx.1
      exact ⟨x, hx0, (hb.exitT_eq_iff ht hx0).mpr hx, rfl⟩
    · rintro ⟨x, hx, rfl, rfl⟩
      exact ⟨x, (hb.exitT_eq_iff (exitT_nonneg _ x) hx).mp rfl, rfl⟩
  · have hab := hb.leftVal_le ht
    have hcpt := isCompact_Icc.image_of_continuousOn (hc t)
    have hmem : w (barG g₀ t) ∈ w '' jumpSet (barG g₀) t := ⟨barG g₀ t, ⟨hab, le_rfl⟩, rfl⟩
    exact ⟨_, _, (csInf_le hcpt.bddBelow hmem).trans (le_csSup hcpt.bddAbove hmem),
      (hc t).image_Icc hab⟩

end PathwiseVolatility
