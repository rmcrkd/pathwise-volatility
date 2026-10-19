/-
Copyright (c) 2026 Ryan McCrickerd. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCrickerd
-/
import PathwiseVolatility.ExitLimits

/-!
# Theorem 3.3, part 4: clipped forward Euler polygons

For `g ∈ G`, the forward Euler polygons of `x' = g (t, x)`, `x (0) = 0`, clipped at `0` as in the
thesis, converge to the global solution `φ` uniformly on compacts as the mesh tends to `0`.
The thesis derives this from Theorem 2.20, which needs `g (0, 0) > 0` there; here `g (0, 0) = 0` is
allowed. The polygons are bracketed by time-shifted copies of the solution:
`φ (t - h) - η₀ < ψ (t) < φ (t + h)`, one segment of the partition at a time. Clipping keeps the
polygons non-negative. The offset `η₀` starts the lower bracket below `0`. A polygon at `0` cannot
meet the lower bracket: there the polygon's slope is close to `g (t, η₀) ≥ g (t - h, η₀) + m > 0`,
so it was not clipped.
-/

open Set Filter Topology

namespace PathwiseVolatility

variable {g : ℝ → ℝ → ℝ}

/-- A partition `t₀ = τ < t₁ < ⋯` of `[τ, ∞)`, the set `Π ([τ, ∞))` of the thesis. -/
structure IsPartition (t : ℕ → ℝ) (τ : ℝ) : Prop where
  zero : t 0 = τ
  strictMono : StrictMono t
  tendsto : Tendsto t atTop atTop

/-- Theorem 3.3, part 4: a forward Euler polygon clipped at `0`, `ψ (t₀) = 0` and
`ψ (t) = (ψ (t_k) + (t - t_k) g (t_k, ψ (t_k)))₊` on each `[t_k, t_{k+1}]`. -/
def IsClippedEulerPolygon (g : ℝ → ℝ → ℝ) (t : ℕ → ℝ) (ψ : ℝ → ℝ) : Prop :=
  ψ (t 0) = 0 ∧ ∀ k, ∀ s ∈ Icc (t k) (t (k + 1)),
    ψ s = max (ψ (t k) + (s - t k) * g (t k) (ψ (t k))) 0

/-- The values of the clipped polygon at the points of the partition. -/
def clippedValues (g : ℝ → ℝ → ℝ) (t : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => max (clippedValues g t k + (t (k + 1) - t k) * g (t k) (clippedValues g t k)) 0

theorem clippedValues_nonneg (g : ℝ → ℝ → ℝ) (t : ℕ → ℝ) : ∀ k, 0 ≤ clippedValues g t k
  | 0 => by simp [clippedValues]
  | k + 1 => by simp only [clippedValues]; exact le_max_right _ _

/-- Theorem 3.3, part 4: the clipped forward Euler polygon exists, for any partition. -/
theorem exists_clippedEulerPolygon (g : ℝ → ℝ → ℝ) {t : ℕ → ℝ} (ht : IsPartition t 0) :
    ∃ ψ, IsClippedEulerPolygon g t ψ := by
  classical
  set y := clippedValues g t with hy
  have hex : ∀ s, ∃ k, s ≤ t (k + 1) := fun s => by
    obtain ⟨k, hk⟩ := (ht.tendsto.eventually (eventually_ge_atTop s)).exists
    exact ⟨k, hk.trans (ht.strictMono.monotone (Nat.le_succ k))⟩
  let idx : ℝ → ℕ := fun s => Nat.find (hex s)
  have h0 : idx (t 0) = 0 := (Nat.find_eq_zero (hex (t 0))).mpr
    (ht.strictMono.monotone (Nat.zero_le 1))
  refine ⟨fun s => max (y (idx s) + (s - t (idx s)) * g (t (idx s)) (y (idx s))) 0, ?_, ?_⟩
  · -- at `t₀`, the first segment applies and the offset vanishes
    simp only [h0, sub_self, zero_mul, add_zero, hy, clippedValues, max_self]
  · -- the polygon's value at any point of the partition is `y k`
    have hnode : ∀ k, max (y (idx (t k)) + (t k - t (idx (t k))) * g (t (idx (t k)))
        (y (idx (t k)))) 0 = y k := by
      intro k
      rcases k with _ | k
      · simp only [h0, sub_self, zero_mul, add_zero, hy, clippedValues, max_self]
      · have hk : idx (t (k + 1)) = k := by
          refine le_antisymm (Nat.find_min' (hex _) le_rfl) ?_
          by_contra hlt
          push Not at hlt
          have := Nat.find_spec (hex (t (k + 1)))
          have h2 : t (idx (t (k + 1)) + 1) < t (k + 1) := ht.strictMono (by omega)
          exact absurd this (not_le.mpr h2)
        simp only [hk, hy, clippedValues]
    intro k s hs
    beta_reduce
    rw [hnode k]
    rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h, hnode k]
      simp only [sub_self, zero_mul, add_zero, max_eq_left (clippedValues_nonneg g t k), hy]
    · -- for `s ∈ (t_k, t_{k+1}]`, the segment found is the `k`th
      have hk : idx s = k := by
        refine le_antisymm (Nat.find_min' (hex s) hs.2) ?_
        by_contra hlt
        push Not at hlt
        have := Nat.find_spec (hex s)
        have h2 : t (idx s + 1) ≤ t k := ht.strictMono.monotone (by omega)
        linarith
      simp only [hk]

/-- Where a clipped polygon is positive, its slope is that of its segment. -/
theorem IsClippedEulerPolygon.hasDerivWithinAt {t : ℕ → ℝ} {ψ : ℝ → ℝ}
    (hψ : IsClippedEulerPolygon g t ψ) {k : ℕ} {a s : ℝ} (ha : t k ≤ a) (has : a < s)
    (hs : s ≤ t (k + 1)) (hpos : 0 < ψ s) :
    HasDerivWithinAt ψ (g (t k) (ψ (t k))) (Icc a s) s := by
  have hlin : HasDerivAt (fun u => ψ (t k) + (u - t k) * g (t k) (ψ (t k)))
      (g (t k) (ψ (t k))) s := by
    have := (((hasDerivAt_id' s).sub_const (t k)).mul_const (g (t k) (ψ (t k)))).const_add
      (ψ (t k))
    rwa [one_mul] at this
  have hseg := hψ.2 k s ⟨ha.trans has.le, hs⟩
  have hLs : 0 < ψ (t k) + (s - t k) * g (t k) (ψ (t k)) := by
    by_contra hle
    push Not at hle
    rw [hseg, max_eq_right hle] at hpos
    exact lt_irrefl _ hpos
  refine hlin.hasDerivWithinAt.congr_of_eventuallyEq ?_ (by rw [hseg, max_eq_left hLs.le])
  filter_upwards [nhdsWithin_le_nhds (hlin.continuousAt.eventually (lt_mem_nhds hLs)),
    self_mem_nhdsWithin] with u hu hmem
  rw [hψ.2 k u ⟨ha.trans hmem.1, hmem.2.trans hs⟩, max_eq_left hu.le]

/-- Theorem 3.3 (Well-posedness for Problem 1.4), part 4: for `g ∈ G`, the clipped forward Euler
polygons converge to the global solution uniformly on `[0, T]`, when the meshes of the partitions
on `[0, T]` tend to `0`. -/
theorem InG.clipped_euler_converges (hg : InG g) {φ : ℝ → ℝ} (hφ : IsGlobalSolution g φ)
    {t : ℕ → ℕ → ℝ} {ψ : ℕ → ℝ → ℝ} (ht : ∀ n, IsPartition (t n) 0)
    (hψ : ∀ n, IsClippedEulerPolygon g (t n) (ψ n)) {T : ℝ} (hT : 0 < T)
    (hmesh : ∀ δ > 0, ∀ᶠ n in atTop, ∀ k, t n k < T → t n (k + 1) - t n k < δ) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ s ∈ Icc 0 T, |ψ n s - φ s| < ε := by
  intro ε hε
  have hm := (hg.mem_Φ hφ).strictMonoOn
  have hc : ContinuousOn φ (Ici 0) := continuousOn_of_deriv hφ.deriv
  have hφ0 := hφ.nonneg
  -- the shift `h`
  obtain ⟨δ, hδ, huc⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous
      (hc.mono (Icc_subset_Ici_self : Icc (0 : ℝ) (T + 1) ⊆ Ici 0))) (ε / 2) (by positivity)
  obtain ⟨h, hhpos, hhδ, hh1⟩ : ∃ h : ℝ, 0 < h ∧ h < δ ∧ h ≤ 1 / 2 :=
    ⟨min (δ / 2) (1 / 2), by positivity, (min_le_left _ _).trans_lt (by linarith),
      min_le_right _ _⟩
  have hdist : ∀ s ∈ Icc 0 T, ∀ s' ∈ Icc 0 T, s ≤ s' → s' ≤ s + h → φ s' - φ s < ε / 2 := by
    intro s hs s' hs' h1 h2
    have := huc s' ⟨hs'.1, by linarith [hs'.2]⟩ s ⟨hs.1, by linarith [hs.2]⟩
      (by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith)
    rw [Real.dist_eq] at this
    linarith [le_abs_self (φ s' - φ s)]
  have hclose : ∀ s ∈ Icc 0 T, φ (s + h) - φ s < ε / 2 := by
    intro s hs
    have := huc (s + h) ⟨by linarith [hs.1], by linarith [hs.2]⟩ s ⟨hs.1, by linarith [hs.2]⟩
      (by rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hhpos]; exact hhδ)
    rw [Real.dist_eq] at this
    linarith [le_abs_self (φ (s + h) - φ s)]
  -- the box `[0, T] × [0, X]`
  set X := φ (T + 1) + 1
  have hX0 : 0 < X := by linarith [hφ0 (T + 1) (by linarith)]
  have hφX : ∀ s ∈ Icc 0 (T + 1), φ s < X := fun s hs => by
    linarith [hm.monotoneOn (mem_Ici.mpr hs.1) (mem_Ici.mpr (by linarith : (0 : ℝ) ≤ T + 1)) hs.2]
  set B := Icc (0 : ℝ) T ×ˢ Icc (0 : ℝ) X
  have hBc : IsCompact B := isCompact_Icc.prod isCompact_Icc
  have hBne : B.Nonempty := (nonempty_Icc.mpr hT.le).prod (nonempty_Icc.mpr hX0.le)
  have hgc : ContinuousOn (Function.uncurry g) B :=
    hg.continuousOn.mono (prod_mono Icc_subset_Ici_self Icc_subset_Ici_self)
  have hmapsB : MapsTo (fun p : ℝ × ℝ => (p.1 + h, p.2)) B (Ici 0 ×ˢ Ici 0) := fun p hp =>
    ⟨mem_Ici.mpr (by linarith [hp.1.1]), mem_Ici.mpr hp.2.1⟩
  have hgch : ContinuousOn (fun p : ℝ × ℝ => g (p.1 + h) p.2) B :=
    hg.continuousOn.comp ((continuous_fst.add continuous_const).prodMk continuous_snd).continuousOn
      hmapsB
  -- the gap `m`, the bound `M` and the modulus of `g` on the box
  obtain ⟨p₀, hp₀, hmin⟩ := hBc.exists_isMinOn hBne (hgch.sub hgc)
  set m := g (p₀.1 + h) p₀.2 - g p₀.1 p₀.2
  have hmpos : 0 < m := sub_pos.mpr (hg.lt_of_lt hp₀.1.1 hp₀.2.1 (by linarith))
  have hgap : ∀ s ∈ Icc 0 T, ∀ x ∈ Icc 0 X, m ≤ g (s + h) x - g s x := fun s hs x hx =>
    hmin (mk_mem_prod hs hx)
  obtain ⟨M, hM⟩ := hBc.exists_bound_of_continuousOn hgc
  have hM' : ∀ s ∈ Icc 0 T, ∀ x ∈ Icc 0 X, |g s x| ≤ M := fun s hs x hx => by
    have := hM (s, x) (mk_mem_prod hs hx); rwa [Real.norm_eq_abs] at this
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM' 0 ⟨le_rfl, hT.le⟩ 0 ⟨le_rfl, hX0.le⟩)
  obtain ⟨δ₁, hδ₁, hucg⟩ := Metric.uniformContinuousOn_iff.mp
    (hBc.uniformContinuousOn_of_continuous hgc) (m / 4) (by positivity)
  have hmod : ∀ s ∈ Icc 0 T, ∀ x ∈ Icc 0 X, ∀ s' ∈ Icc 0 T, ∀ x' ∈ Icc 0 X,
      |s - s'| < δ₁ → |x - x'| < δ₁ → |g s x - g s' x'| < m / 4 := by
    intro s hs x hx s' hs' x' hx' h1 h2
    have := hucg (s, x) (mk_mem_prod hs hx) (s', x') (mk_mem_prod hs' hx')
      (by rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]; exact max_lt h1 h2)
    rwa [Real.dist_eq] at this
  -- the step `κ`, the offset `η₀` and the mesh `δm`
  obtain ⟨η₀, hη₀pos, hη₀δ, hη₀ε⟩ : ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ δ₁ / 4 ∧ η₀ ≤ ε / 2 :=
    ⟨min (δ₁ / 4) (ε / 2), by positivity, min_le_left _ _, min_le_right _ _⟩
  have hMf1 : 0 < M + 1 := by linarith
  obtain ⟨δm, hδmpos, hδmκ, hδmδ⟩ : ∃ δm : ℝ, 0 < δm ∧ δm * (M + 1) < δ₁ / 4 ∧ δm < δ₁ :=
    ⟨δ₁ / 8 / (M + 1), by positivity, by rw [div_mul_cancel₀ _ hMf1.ne']; linarith,
      (div_le_self (by positivity) (by linarith)).trans_lt (by linarith)⟩
  filter_upwards [hmesh δm hδmpos] with n hmn
  obtain ⟨hψ0, hψseg⟩ := hψ n
  have htn := ht n
  rw [htn.zero] at hψ0
  have hnode : ∀ k, 0 ≤ t n k := fun k => htn.zero ▸ htn.strictMono.monotone (Nat.zero_le k)
  have hnn : ∀ k, ∀ s ∈ Icc (t n k) (t n (k + 1)), 0 ≤ ψ n s := fun k s hs => by
    rw [hψseg k s hs]; exact le_max_right _ _
  have hnnode : ∀ k, 0 ≤ ψ n (t n k) := fun k => by
    cases k with
    | zero => exact ((congrArg (ψ n) htn.zero).trans hψ0).symm.le
    | succ k => exact hnn k _ ⟨(htn.strictMono (Nat.lt_succ_self k)).le, le_rfl⟩
  -- a step from a node in the box moves less than `δ₁ / 4`
  have hstep : ∀ k, t n k < T → ∀ s ∈ Icc (t n k) (t n (k + 1)), ψ n (t n k) ≤ X →
      |ψ n s - ψ n (t n k)| < δ₁ / 4 := by
    intro k hk s hs hyX
    have h1 := abs_max_sub_max_le_abs (ψ n (t n k) + (s - t n k) * g (t n k) (ψ n (t n k)))
      (ψ n (t n k)) 0
    rw [max_eq_left (hnnode k), ← hψseg k s hs, add_sub_cancel_left, abs_mul,
      abs_of_nonneg (show (0 : ℝ) ≤ s - t n k by linarith [hs.1])] at h1
    have h2 : s - t n k < δm := by have := hmn k hk; linarith [hs.2]
    have h3 := hM' _ ⟨hnode k, hk.le⟩ _ ⟨hnnode k, hyX⟩
    calc |ψ n s - ψ n (t n k)| ≤ (s - t n k) * |g (t n k) (ψ n (t n k))| := h1
      _ ≤ δm * (M + 1) := mul_le_mul h2.le (by linarith) (abs_nonneg _) hδmpos.le
      _ < δ₁ / 4 := hδmκ
  have hcont_seg : ∀ k a b, t n k ≤ a → b ≤ t n (k + 1) → ContinuousOn (ψ n) (Icc a b) := by
    intro k a b ha hb
    have hlin : ContinuousOn
        (fun u => max (ψ n (t n k) + (u - t n k) * g (t n k) (ψ n (t n k))) 0) (Icc a b) :=
      ((continuous_const.add ((continuous_id.sub continuous_const).mul continuous_const)).max
        continuous_const).continuousOn
    exact hlin.congr fun u hu => hψseg k u ⟨ha.trans hu.1, hu.2.trans hb⟩
  have hseg : ∀ k s, min (t n k) T < s → s ≤ min (t n (k + 1)) T →
      t n k < s ∧ s ≤ t n (k + 1) ∧ s ≤ T ∧ t n k < T := by
    intro k s h1 h2
    have hsT : s ≤ T := h2.trans (min_le_right _ _)
    have htks : t n k < s := by
      rcases le_total (t n k) T with h | h
      · rwa [min_eq_left h] at h1
      · rw [min_eq_right h] at h1; linarith
    exact ⟨htks, h2.trans (min_le_left _ _), hsT, htks.trans_le hsT⟩
  have hφh : ∀ s ∈ Icc 0 T, φ (s + h) < X := fun s hs => hφX _ ⟨by linarith [hs.1], by
    linarith [hs.2]⟩
  -- the upper bracket, one segment at a time
  have hP : ∀ k, ∀ s ∈ Icc 0 (min (t n k) T), ψ n s < φ (s + h) ∧ 0 ≤ ψ n s := by
    intro k
    induction k with
    | zero =>
      intro s hs
      have hs0 : s = 0 := le_antisymm (hs.2.trans ((min_le_left _ _).trans htn.zero.le)) hs.1
      rw [hs0, hψ0, zero_add]
      refine ⟨?_, le_rfl⟩
      have := hm (mem_Ici.mpr le_rfl) (mem_Ici.mpr hhpos.le) hhpos
      rwa [hφ.init] at this
    | succ k ih =>
      intro s hs
      by_cases hsk : s ≤ min (t n k) T
      · exact ih s ⟨hs.1, hsk⟩
      obtain ⟨htks, hsk1, hsT, htkT⟩ := hseg k s (not_le.mp hsk) hs.2
      obtain ⟨hk1, -⟩ := ih (t n k) ⟨hnode k, le_min le_rfl htkT.le⟩
      have htkB : t n k ∈ Icc 0 T := ⟨hnode k, htkT.le⟩
      have hyX : ψ n (t n k) ∈ Icc 0 X := ⟨hnnode k, (hk1.trans (hφh _ htkB)).le⟩
      refine ⟨?_, hnn k s ⟨htks.le, hsk1⟩⟩
      have hmaps : MapsTo (fun u => u + h) (Icc (t n k) s) (Ici 0) := fun u hu =>
        mem_Ici.mpr (by linarith [hu.1, hnode k])
      refine lt_of_first_meeting (u := fun u => φ (u + h)) (v := ψ n) htks.le
        (hc.comp (continuous_id.add continuous_const).continuousOn hmaps)
        (hcont_seg k _ _ le_rfl hsk1) hk1 fun s' hs' hmeet => ?_
      have hmeet' : φ (s' + h) = ψ n s' := hmeet
      have hs'B : s' ∈ Icc 0 T := ⟨by linarith [hs'.1, hnode k], hs'.2.trans hsT⟩
      have hpos : 0 < ψ n s' := by
        rw [← hmeet']
        have := hm (mem_Ici.mpr le_rfl) (mem_Ici.mpr (by linarith [hs'B.1]))
          (show (0 : ℝ) < s' + h by linarith [hs'B.1])
        rwa [hφ.init] at this
      have hc' : ψ n s' ∈ Icc 0 X := ⟨hpos.le, by rw [← hmeet']; exact (hφh _ hs'B).le⟩
      have hdu : HasDerivWithinAt (fun u => φ (u + h)) (g (s' + h) (φ (s' + h)))
          (Icc (t n k) s') s' := by
        have := (hφ.deriv (s' + h) (hmaps ⟨hs'.1.le, hs'.2⟩)).comp s'
          ((hasDerivAt_id' s').add_const h).hasDerivWithinAt
          (hmaps.mono_left (Icc_subset_Icc_right hs'.2))
        rwa [mul_one] at this
      refine ⟨_, _, hdu, (hψ n).hasDerivWithinAt le_rfl hs'.1 (hs'.2.trans hsk1) hpos, ?_⟩
      rw [hmeet']
      have h2 := hmod _ htkB _ hyX _ hs'B _ hc'
        (by rw [abs_sub_comm, abs_of_pos (by linarith [hs'.1])]
            have := hmn k htkT; linarith [hs'.2, hsk1])
        (by rw [abs_sub_comm]
            linarith [hstep k htkT s' ⟨hs'.1.le, hs'.2.trans hsk1⟩ hyX.2])
      have h3 := hgap _ hs'B _ hc'
      linarith [le_abs_self (g (t n k) (ψ n (t n k)) - g s' (ψ n s'))]
  obtain ⟨K, hK⟩ := (htn.tendsto.eventually (eventually_ge_atTop T)).exists
  have hAll : ∀ s ∈ Icc 0 T, ψ n s < φ (s + h) ∧ 0 ≤ ψ n s :=
    fun s hs => hP K s ⟨hs.1, le_min (hs.2.trans hK) hs.2⟩
  -- the lower bracket, one segment at a time
  have hQ : ∀ k, ∀ s ∈ Icc h (min (t n k) T), φ (s - h) - η₀ < ψ n s := by
    intro k
    induction k with
    | zero =>
      intro s hs
      have := hs.2.trans (min_le_left _ _)
      rw [htn.zero] at this
      linarith [hs.1]
    | succ k ih =>
      intro s hs
      by_cases hsk : s ≤ min (t n k) T
      · exact ih s ⟨hs.1, hsk⟩
      obtain ⟨htks, hsk1, hsT, htkT⟩ := hseg k s (not_le.mp hsk) hs.2
      have htkB : t n k ∈ Icc 0 T := ⟨hnode k, htkT.le⟩
      have hyX : ψ n (t n k) ∈ Icc 0 X := ⟨hnnode k, ((hAll _ htkB).1.trans (hφh _ htkB)).le⟩
      have hka : t n k ≤ max (t n k) h := le_max_left _ _
      have hha : h ≤ max (t n k) h := le_max_right _ _
      have has : max (t n k) h ≤ s := max_le htks.le hs.1
      have hmaps : MapsTo (fun u => u - h) (Icc (max (t n k) h) s) (Ici 0) :=
        fun u hu => mem_Ici.mpr (by linarith [hu.1])
      refine lt_of_first_meeting (u := ψ n) (v := fun u => φ (u - h) - η₀) has
        (hcont_seg k _ _ hka hsk1)
        ((hc.comp (continuous_id.sub continuous_const).continuousOn hmaps).sub continuousOn_const)
        ?_ fun s' hs' hmeet => ?_
      · show φ (max (t n k) h - h) - η₀ < ψ n (max (t n k) h)
        rcases le_total h (t n k) with h1 | h1
        · rw [max_eq_left h1]
          exact ih _ ⟨h1, le_min le_rfl htkT.le⟩
        · rw [max_eq_right h1, sub_self, hφ.init]
          linarith [hnn k h ⟨h1, hsk1.trans' (by linarith [hs.1, has])⟩]
      · have hmeet' : ψ n s' = φ (s' - h) - η₀ := hmeet
        have hs'1 : t n k < s' := lt_of_le_of_lt hka hs'.1
        have hs'B : s' ∈ Icc 0 T := ⟨by linarith [hs'.1], hs'.2.trans hsT⟩
        have hs'h : s' - h ∈ Icc 0 T := ⟨by linarith [hs'.1], by linarith [hs'B.2]⟩
        have hφs' : φ (s' - h) ∈ Icc 0 X :=
          ⟨hφ0 _ hs'h.1, (hφX _ ⟨hs'h.1, by linarith [hs'h.2]⟩).le⟩
        have hnear : |t n k - s'| < δ₁ := by
          rw [abs_sub_comm, abs_of_pos (by linarith)]
          have := hmn k htkT; linarith [hs'.2, hsk1]
        have hstep' := hstep k htkT s' ⟨hs'1.le, hs'.2.trans hsk1⟩ hyX.2
        have hgapc := hgap _ hs'h _ hφs'
        rw [sub_add_cancel] at hgapc
        have hdv : HasDerivWithinAt (fun u => φ (u - h) - η₀) (g (s' - h) (φ (s' - h)))
            (Icc (max (t n k) h) s') s' := by
          have := ((hφ.deriv (s' - h) (hmaps ⟨hs'.1.le, hs'.2⟩)).comp s'
            ((hasDerivAt_id' s').sub_const h).hasDerivWithinAt
            (hmaps.mono_left (Icc_subset_Icc_right hs'.2))).sub_const η₀
          rwa [mul_one] at this
        rcases eq_or_lt_of_le (hnn k s' ⟨hs'1.le, hs'.2.trans hsk1⟩) with h0 | hpos
        · -- a polygon at `0` would have been rising, so it cannot meet the bracket there
          exfalso
          have hη : φ (s' - h) = η₀ := by linarith
          have hψk : ψ n (t n k) < δ₁ / 4 := by
            rw [← h0, zero_sub, abs_neg, abs_of_nonneg (hnnode k)] at hstep'
            exact hstep'
          have hη₀X : η₀ ∈ Icc 0 X := hη ▸ hφs'
          have h2 := hmod _ htkB _ hyX _ hs'B _ hη₀X hnear (by
            rw [abs_lt]; constructor <;> linarith [hnnode k])
          have hd0 : 0 ≤ g (s' - h) η₀ := by
            rw [← hη]
            exact deriv_nonneg_of_monotoneOn hm.monotoneOn hs'h.1 (hφ.deriv _ hs'h.1)
          rw [hη] at hgapc
          have hslope : 0 < g (t n k) (ψ n (t n k)) := by
            linarith [neg_abs_le (g (t n k) (ψ n (t n k)) - g s' η₀)]
          have hseg' := hψseg k s' ⟨hs'1.le, hs'.2.trans hsk1⟩
          rw [← h0] at hseg'
          have : 0 < ψ n (t n k) + (s' - t n k) * g (t n k) (ψ n (t n k)) := by
            nlinarith [hnnode k, mul_pos (sub_pos.mpr hs'1) hslope]
          rw [max_eq_left this.le] at hseg'
          linarith
        · refine ⟨_, _, (hψ n).hasDerivWithinAt hka hs'.1 (hs'.2.trans hsk1) hpos, hdv, ?_⟩
          have h2 := hmod _ htkB _ hyX _ hs'B _ hφs' hnear (by
            rw [abs_lt]; constructor <;> linarith [neg_abs_le (ψ n s' - ψ n (t n k)),
              le_abs_self (ψ n s' - ψ n (t n k))])
          linarith [neg_abs_le (g (t n k) (ψ n (t n k)) - g s' (φ (s' - h)))]
  -- so the polygon is within `ε` of `φ`
  intro s hs
  obtain ⟨hup, hge⟩ := hAll s hs
  rw [abs_lt]
  refine ⟨?_, by linarith [hclose s hs]⟩
  rcases lt_or_ge s h with hsh | hsh
  · have := hdist 0 ⟨le_rfl, hT.le⟩ s hs hs.1 (by linarith)
    rw [hφ.init] at this
    linarith
  · have hlo := hQ K s ⟨hsh, le_min (hs.2.trans hK) hs.2⟩
    have := hclose (s - h) ⟨by linarith, by linarith [hs.2]⟩
    rw [sub_add_cancel] at this
    linarith

end PathwiseVolatility
