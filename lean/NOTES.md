# Notes on the Lean formalisation

How the formal statements in this folder read, and where the Lean proofs differ from the thesis's. [README.md](README.md) lists the results.

## Cited results proved here

| Cited result | Lean | File |
| --- | --- | --- |
| Peano's existence theorem, forward in time (Theorem 1.1.2 of Lakshmikantham and Leela) | `peano_exists` | `Peano.lean` |
| Continuation to a maximal solution (Theorem 1.1.3 of Lakshmikantham and Leela), for the IVPs of Problem 1.2 | `maxSol_isMaximal` | `Maximal.lean` |
| Exit-time bijectivity (Lemmas 13.6.2 and 13.6.5 of Whitt), the thesis's Lemma 3.11 | `InΦbar.inN_exitT`, `InN.inΦbar_exitT`, `InΦbar.exitT_exitT`, `InN.exitT_exitT` | `ExitBijection.lean`, `ExitConstruct.lean` |

## How the formal statements read

- **Notation.** `f t x` is `f (t, x)`, the initial value is `(τ, ξ)`, and a solution lives on `Dom τ T`, the interval `[τ, T)`. The end `T ∈ (τ, ∞]`, the path of zeros `ϕ (x) ∈ [-∞, ∞]` (`zeroPath`) and the bound `φ̄ (t) ∈ [ξ, ∞]` (`upperBound`) are extended reals, with `sup ∅ = -∞` and `inf ∅ = ∞` as in the thesis.
- **Solutions.** `IsSolution f τ ξ T φ` asks for `φ (τ) = ξ` and the derivative `f (t, φ (t))` within `[τ, T)` at each point, so a right derivative at `τ`. That `φ` is then `C¹` follows from the continuity of `f` (`IsSolution.continuousOn_deriv`).
- **Maximality.** `IsMaximalSolution` adds the thesis's condition `T_* ∨ sup_{[τ, T_*)} |φ| = ∞`, written as `T = ∞` or `|φ|` unbounded on `[τ, T)`.
- **The limit `X_*`.** A maximal solution is strictly increasing, with `X_* = lim_{t → T_*} φ (t)`. So `X_* > X` is written as `φ (t) > X` for some `t`, and `X_* = ∞` as `φ` unbounded above. In Theorem 2.8, `T_* ∨ X_* = ∞` is written as `T = ∞` or `φ` unbounded above.
- **Hypotheses.** Results carry `f ∈ F` (`InF f`). Most of Chapter 2 is stated under the line condition of Theorem 3.1 (`LineCondition f τ ξ`: `f > 0` on a line `{(τ + c x, ξ - x) : x ∈ (0, ε)}` running down from `(τ, ξ)`), rather than the thesis's `f (τ, ξ) > 0`. This is a weaker hypothesis, since `f (τ, ξ) > 0` implies it (`lineCondition_of_pos`), so these statements give the Chapter 2 results, and also hold under Theorem 3.1's line condition, which Theorem 3.3 needs for `g (0, 0) = 0`. Other hypotheses are as in the thesis, except where one turned out not to be needed, as noted in the log below.
- **Chapter 3's functions.** Functions in `G`, defined on `ℝ₊²` in the thesis, are functions on `ℝ²` of which only the values on `ℝ₊²` matter. A path `φ ∈ Φ` comes with its derivative `φ'`, given as a separate function.

## Where the proofs differ from the thesis

The theorems are the thesis's. Some proofs take a different route, and some statements are slightly more general. Each difference is listed here.

- **Lemma 2.16.**
  - *Scope.* It is stated for any solution on `[τ, T)`, maximal or not, with the inverse `φ̂` on the image `φ ([τ, T))`, which is the thesis's `[ξ, X_*)`.
  - *Derivative relation.* `φ' (t) φ̂' (φ (t)) = 1` is stated at times `t > τ`, where both derivatives are two-sided, and at `t = τ` between one-sided derivatives, within `[τ, T)` and the image (`hasDerivWithinAt_solInv_init`, and conversely `mul_eq_one_of_hasDerivWithinAt_solInv_init`).
  - *Integral.* Lebesgue's theorem comes from Mathlib (`MonotoneOn.intervalIntegral_deriv_mem_uIcc`). The finite exceptions are handled by Mathlib's fundamental theorem of calculus with countably many exceptional points, rather than by splitting `[a, b]` at them as the thesis does. Absolute continuity follows because `φ̂` is a constant plus an indefinite integral.
  - *Use.* The result is not used by the Lean proof of Theorem 2.17, which goes by comparison instead.
- **Corollary 2.1, Theorem 2.17.**
  - *Agreement.* Two solutions are shown to agree by comparison, not through their inverses and Lebesgue's theorem (Lemma 2.16, which is not needed). For `h > 0`, the copy `t ↦ φ₁ (t + h)` stays strictly above any other solution `φ₂`. It starts above, since `φ₁` is strictly increasing. Where the two would first meet, at a level `c`, the copy's slope `f (t + h, c)` would exceed `f (t, c)`, since `f (·, c)` is strictly increasing. Letting `h → 0` gives `φ₂ ≤ φ₁`, and by symmetry `φ₁ = φ₂` wherever both are defined. Maximality is not used for this part.
  - *Same interval.* Two maximal solutions have the same interval, by compactness: if one interval `[τ, T₁)` ended strictly before the other, the second solution would be bounded on `[τ, T₁]`, and so would the first, which contradicts maximality. The thesis uses a case analysis.
  - *Existence* is as in Theorem 2.8 below.
- **Lemma 2.3.** Continuity into `[-∞, ∞]` is proved through the order topology, not with sequences and the Bolzano–Weierstrass theorem. Since `f (·, x)` is strictly increasing, `ϕ (x) > a` exactly when `f (t, x) < 0` for some `t > a`, and `ϕ (x) < a` exactly when `f (t, x) > 0` for some `t < a`. Both sets of `x` are unions of open sets.
- **Lemma 2.4.**
  - *Exit time.* `φ̄ = E (ϕ)` holds because the two sets in the infima are the same: `ϕ (x) > t` exactly when `f (t, x) < 0`.
  - *Proofs.* The other properties are proved from the definition of `φ̄` directly, not through `ϕ` and the properties of exit times. Right-continuity holds because `f (t, x) < 0` persists for times just after `t`, and the left limits exist because `φ̄` is non-decreasing.
  - *Statements.* `φ̄` is non-decreasing and càdlàg on all of `ℝ`, without the condition `f (τ, ξ) ≥ 0`, which is needed only for the zero and strict-increase claims. The strict increase is stated pairwise: `φ̄ (s) < φ̄ (t)` for `τ ≤ s < t` whenever `φ̄ (t) < ∞`. This is the thesis's statement over `[τ, T]` when `φ̄ (T) < ∞`.
- **Lemma 2.6.**
  - *Proof.* The upper bound is proved by a last-crossing argument, not through the path of zeros and the mean value theorem. If `φ (t) > x` at a level `x > ξ` where `f (t, x) < 0`, take the last time `s ≤ t` at which `φ` is at `x`. Since `f (·, x)` is increasing, `f (s, x) < 0`. But `φ > x` just after `s`, so its right derivative there is non-negative. The lower bound uses the same argument, mirrored.
  - *Statement.* Both bounds hold for every solution, maximal or not, and the upper bound does not need `f (τ, ξ) > 0`.
  - *Under the line condition.* The lower bound `ξ ≤ φ` (`le_solution`) is stated under the line condition of Theorem 3.1 (see *Hypotheses* above), and needs a new argument when `f (τ, ξ) = 0`. A solution which dipped below `ξ - x` would cross that level for the last time to the left of the line, before `τ + c x`. To get there from `ξ` it would need a slope below `-1 / c` somewhere near `(τ, ξ)`, where `f` is close to `f (τ, ξ) = 0`. The thesis argues geometrically through the region to the right of the line.
- **Theorem 2.8.**
  - *Existence.* The thesis takes existence from classical theory. Here it is proved from Peano's theorem (below) and from uniqueness:
    - `T_*` is the supremum of the ends of all solutions, which agree wherever they overlap, and the maximal solution is their common value.
    - If it ended at a finite `T_*` while bounded, Peano's theorem would extend it past `T_*`. This uses an interval length that is uniform over the bounded region.

    The continuation therefore uses the uniqueness of Theorem 2.17, which holds for the IVPs of Problem 1.2. It is not the general continuation theorem for arbitrary continuous `f`.
  - *Strict increase* is proved directly. If a solution were constant at a level `c` on an interval, the ODE would give `f (·, c) = 0` at two different times, which is impossible because `f (·, c)` is strictly increasing. The thesis argues through `φ̄`. Non-negativity of `f (t, φ (t))` comes from the bounds, as in the thesis.
  - *Bijection.* The image `[ξ, X_*)` is stated as the set of `x ≥ ξ` below some value of `φ` (`image_dom`).
- **Lemma 2.9.** If the solution's interval ended at a finite `T_* ≤ T`, the solution would be bounded above by a level `x > ξ` where `f (T, x) < 0`, by the upper bound of Lemma 2.6, which contradicts maximality. The thesis instead finds a touching point with `φ̄ (T)`. The lemma holds for any `T`, not only `T > τ`.
- **Lemma 2.10.**
  - *Condition.* The thesis's condition `lim_{t → ∞} f (t, x) > 0` is written as `f (t, x) > 0` for some `t`. The two are equivalent since `f (·, x)` is increasing.
  - *The "only if" direction* follows the thesis.
  - *The "if" direction* uses compactness instead of the thesis's line and touching point. The open sets `{x : f (n, x) > 0}` increase with `n` and cover `[ξ, X]`, so a single `n` covers it. Then `f ≥ c > 0` on `[n, ∞) × [ξ, X]`. While the solution stays below `X`, it grows at rate at least `c`, so it passes `X` in finite time.
- **Theorem 2.18.**
  - *Statement.* Uniform convergence on `[τ, T] × [ξ, X]` is written with an explicit `η` for each `ε`. The conclusion includes that `φ_n` exists on `[τ, T]` from some `n` on, which the thesis's statement leaves implicit.
  - *Proof.* The thesis extracts convergent subsequences by the Arzelà–Ascoli lemma, identifies their limits by uniqueness, and extends the interval step by step. Here the solutions are instead bracketed by copies of `φ₀` shifted in time:
    - For a small `h > 0`, `f₀ (t + h, x) - f₀ (t, x) ≥ m > 0` on the compact box, since `f₀ (·, x)` is strictly increasing.
    - Once `f_n` is within `m` of `f₀` there, comparison at first meeting points gives `φ₀ (t - h) < φ_n (t) < φ₀ (t + h)`.
    - The upper bracket keeps `φ_n` bounded, so by maximality it exists beyond `T`.
    - `φ₀` moves by less than `ε` over a time `h`.
- **Theorem 3.3.**
  - *The extension.* As in the thesis, `g ∈ G` is extended to `f ∈ F` with eq. (3.6). It is written as `f (t, x) = g (t⁺, x⁺) + g (0, x⁺) - g (t⁻, x⁺)`, which is the thesis's two cases in one continuous formula.
  - *Parts 1 to 3* follow from the Chapter 2 results under the line condition, as in the thesis. The unboundedness of `φ̄` in part 2 is written as `φ̄ (t)` exceeding any real number, since `φ̄` takes extended-real values. Part 3 is stated, like Theorem 2.18, for each `[0, T]`.
  - *Part 4.* The thesis derives it from Theorem 2.20, which needs `g (0, 0) > 0`. Here it is proved directly for the clipped polygons (`InG.clipped_euler_converges`), so `g (0, 0) = 0` is covered. The polygons are bracketed by `φ (t - h) - η₀ < ψ (t) < φ (t + h)`, one segment of the partition at a time; clipping keeps them non-negative, and a polygon at `0` cannot meet the lower bracket, since its slope there is close to `g (t, η₀) ≥ g (t - h, η₀) + m > 0`, so it was not clipped. The theorem concerns any such polygons, as in the thesis, and they exist for any partition (`exists_clippedEulerPolygon`).
- **Theorem 3.4.** It is split into its three claims: every global solution is in `Φ`; every `φ ∈ Φ` solves the IVP for the `g` of eq. (3.10), whatever `ϑ`; and for `ϑ` as stated, that `g` is in `G`, so `φ` is its only global solution. `ϑ` need only be continuous on `ℝ₊`; the thesis's `ϑ (0) = 0` is not needed.
- **Corollary 3.5.** Surjectivity and non-injectivity are stated together: every `φ ∈ Φ` is the global solution for two different functions in `G`. These are the functions of eq. (3.10) with `ϑ (t) = a t + max_{[0, t]} φ' - φ' (0)` for `a = 1, 2`, after the thesis's example. That the running maximum is continuous is proved here (`continuousOn_runMax`).
- **Theorem 3.6, Corollary 3.7.** The bijection is stated as three facts:
  - for `w ∈ W`, the solution is in `Φ_ϑ`;
  - two `w` with the same solution agree on `ℝ₊`;
  - every path in `Φ_ϑ` arises from some `w ∈ W`.

  The function `g = ϑ - w` is the image of `w`, so these give Theorem 3.6 and Corollary 3.7 together.
- **Definitions 3.9, 3.12, and the supremum functional `M`.**
  - *`E`.* It is defined for any real function. `sInf ∅ = 0` in Lean, but the thesis only applies `E` to paths unbounded above, for which the set is never empty.
  - *The metric.* `d_Φ̄` is defined through the seminorm of eq. (1.12). Convergence in it is obtained through the bound `‖w‖_{ℝ₊} ≤ η + 2^{-N}` whenever `|w| ≤ η` on `[0, N]` (`uniNorm_le`). That bound is slightly sharper than the thesis's eq. (3.20).
- **Lemma 3.11** is cited in the thesis, from Whitt. Here it is proved from the definitions, as four facts: `E` maps `Φ̄` to `N` and `N` to `Φ̄`, and `E ∘ E = id` on both, on `ℝ₊`. Bijectivity follows, for paths compared on `ℝ₊`.
  - *`Φ̄` to `N`.* The key fact is that `E (φ̄) (x) > t` exactly when `φ̄ (t) < x`. So the level set `{x : E (φ̄) (x) = t}` is `[φ̄ (t₋), φ̄ (t)]`, and `E (φ̄)` is continuous because `φ̄` is strictly increasing.
  - *`N` to `Φ̄`.* For `ψ ∈ N`, `ψ (E (ψ) (x)) = x`, by continuity. So `E (ψ)` is strictly increasing. It is right-continuous, and has left limits as a monotone function.
  - *Also proved.* The bound `φ̄` of Theorem 3.3 is in `Φ̄`, through `φ̄ = E (M (ϕ))` with `M (ϕ) ∈ N`.
- **Corollary 3.15.**
  - *The zero path.* `ϕ` (`zeroG`) is shown to be continuous on `ℝ₊` through the order topology, as for Lemma 2.3. That continuity is what `E (φ̄) = M (ϕ)` needs.
  - *`E (φ̄) = M (ϕ)`.* The thesis derives it from the general identity `E ∘ E = M`. Here it is proved directly: for `t > 0`, `φ̄ (t) > x` exactly when `ϕ ≤ t` on `[0, x]` and a little beyond.
- **Lemma 3.16.**
  - *Statement.* Uniform convergence on compacts of `ℝ₊²` is written box by box, with an explicit `η` for each `ε`.
  - *Proof.* The thesis argues separately where `ϕ₀ > 0` and where `ϕ₀ = 0`. Here, the gap `g₀ (t + ε, x) - g₀ (t, x) ≥ m > 0` on a compact box keeps `ϕ_n` within `ε` of `ϕ₀` in one step, once `g_n` is within `m / 2` of `g₀`. `M` is then `1`-Lipschitz.
- **Theorem 3.17.**
  - *Statement.* It is stated for `x' = (n + 1) g_n (t, x)`, so that every `n` gives a function in `G`; this is the thesis's `n g_n` shifted by one. The conclusion is given both as uniform convergence of `φ_n⁻¹` to `E (φ̄₀)` on compacts and as convergence in `d_Φ̄`.
  - *Proof of the lower bound.* As in the thesis, from Corollary 3.15 and Lemma 3.16.
  - *Proof of the upper bound.* The thesis compares `φ_n` with `μ⁻¹`, using a Lipschitz bound on `μ⁻¹`. Here the inverses are compared directly: `φ_n⁻¹ < μ = E (φ̄₀) + λ`. At a first meeting point `x'`, `φ_n⁻¹` has the derivative `1 / ((n + 1) g_n (μ (x'), x')) < κ` (Lemma 2.16), while the slopes of `μ` from the left are at least `κ`, the slope of `λ`, because `E (φ̄₀)` is non-decreasing.
- **Theorem 3.18.**
  - *Example.* `w = ϑ ∘ E (φ̄)` is in `W` with `M (w) = ϑ ∘ E (φ̄)` (`InΦbar.construct_example`), using the continuity of `E (φ̄)` from Lemma 3.11.
  - *Proof.* `φ̄₀ = φ̄` is proved through `E ∘ M = E` (`sInf_lt_supF`), the strict increase of `ϑ`, and `E ∘ E = id` on `Φ̄`, as in the thesis.
- **Example 3.19.**
  - *Indexing.* As in Theorem 3.17, the sequence starts at `0`: `φ_n` solves `x' = (n + 1) g_{n + 1}`.
  - *Hypotheses.* The thesis assumes `σ > 0`, which is not needed. Membership in `G` is proved assuming `κ x - σ w (x)` is unbounded above, the condition the thesis names. As in the thesis, the condition is also necessary (`inG_cirG_iff`), and equivalent to `φ̄₀` being finite (`unbounded_iff_bound_finite`).
- **Definitions 3.21, 3.22.**
  - *Paths.* An excursionary path is a set-valued function `e : ℝ → Set ℝ`, with `e (t)` a compact interval for `t ≥ 0`.
  - *Distance.* `d_{E, T}` is Mathlib's Hausdorff edistance between the extended graphs. Mathlib's `ℝ × ℝ` has the maximum norm, not the Euclidean norm of the thesis; the two are equivalent, so convergence in `d_E` is the same. The edistance can be infinite, which `1 ∧ d_{E, n}` in `d_E` caps at `1`, as in the thesis.
- **Theorem 3.26.**
  - *Eq. (3.34).* Uniform convergence of parametric representations gives convergence on `(E, d_E)` (`tendsto_excMetric_of_param`). The thesis's argument maps the representations onto `[0, 1)`. Here the endpoint `T` needs care: a point of one graph whose partner in the other has passed `T` is matched with the vertical line `{T} × ℝ`. The parts of the domains which reach `[0, T]` lie in a common `[0, X]` for large `n`, since `E (φ̄₀)` is unbounded.
  - *Representation.* As in the thesis, the limit is represented by `(E (φ̄₀), w)`, through the level sets of Lemma 3.11.
  - *Also proved.* The limit is in `E`.
- **Example 3.27.** As for Example 3.19. The thesis takes `ρ ∈ [-1, 1]` and `w₀ (0) = 0`, which are not needed for the convergence.
- **Peano's theorem.** The thesis cites it. Here it is proved for scalar ODEs, forward in time:
  - approximate the field uniformly by averaging it over small spatial intervals, which makes it Lipschitz in space;
  - solve each approximation with Mathlib's Picard–Lindelöf theorem;
  - extract a uniformly convergent subsequence with the Arzelà–Ascoli theorem;
  - pass to the limit in the integral equation.

  The Mathlib version used here does not have Peano's theorem; `Peano.lean` can be replaced by Mathlib's version once it has one.
