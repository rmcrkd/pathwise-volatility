# Lean formalisation

A formalisation of the thesis's main results in Lean 4 with Mathlib, with the results they rest on. Every result marked as proved below is proved in full: there is no `sorry`, and nothing depends on axioms beyond Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`).

The Lean code was written with an AI assistant (Claude). Its correctness rests on Lean's kernel, and `Axioms.lean` lists the axioms each result uses.

## Building

With [elan](https://github.com/leanprover/elan) installed, from this folder:

    lake exe cache get    # downloads Mathlib's compiled files
    lake build
    lake env lean Axioms.lean    # lists the axioms each result depends on

## The results

The main results are those the thesis's abstract describes: existence, uniqueness and continuous dependence for the IVPs of Chapter 2, their well-posedness and solution set for the class `G` of Chapter 3, and the exit-time and excursionary limits behind the integrated CIR to IG and Heston to NIG relationships. Each is proved in full, as are the results they rest on; definitions are stated. [NOTES.md](NOTES.md) explains how the formal statements read and records where the Lean proofs differ from the thesis's. The tables are generated from `results.tsv` by `scripts/catalogue.py`.

<!-- results:start -->

### Main results

| Result | Lean |
| --- | --- |
| Theorem 2.8 (Maximal existence and bijectivity) | `exists_maximal`, `strictMonoOn_solution`, `maximal_unbounded`, `image_dom` (`Maximal.lean`, `Bounds.lean`, `SolutionFacts.lean`) |
| Lemma 2.9 (Temporal existence) | `lt_of_upperBound_lt_top`, `eq_top_of_upperBound_lt_top` (`Bounds.lean`) |
| Corollary 2.11 (Spatio-temporal existence) | `spatio_temporal` (`Existence.lean`) |
| Theorem 2.17 (Maximal uniqueness) | `maximal_existence_uniqueness`, `maximal_uniqueness` (`Maximal.lean`, `Uniqueness.lean`) |
| Theorem 2.18 (Solution map continuity) | `solution_map_continuous` (`Dependence.lean`) |
| Theorem 3.3 (Well-posedness for Problem 1.4) | `InG.exists_unique_global`, `InG.upper_bound`, `InG.solution_continuous`, `InG.clipped_euler_converges`, `InG.isGlobalSolution_iff`, `exists_clippedEulerPolygon` (`Global.lean`, `EulerClipped.lean`) |
| Theorem 3.4 (The solution set) | `solution_set`, `InG.mem_Φ`, `solves_gOfPath`, `gOfPath_mem_G` (`SolutionSet.lean`) |
| Theorem 3.6 (Solution map bijectivity) | `InW.inG`, `InW.solution_mem`, `InW.injective`, `InΦϑ.exists_w` (`SolutionSet.lean`) |
| Theorem 3.17 (Uniform exit-time limits) | `exit_limit` (`ExitLimits.lean`) |
| Theorem 3.18 (Construction of exit-time limits) | `construct_limit`, `barG_construct`, `InΦbar.construct_example` (`ExitConstruct.lean`, `ExitBijection.lean`) |
| Example 3.19 (Pathwise integrated CIR to IG) | `cir_to_ig`, `inG_cirG`, `cirG_conv`, `inG_cirG_iff`, `unbounded_iff_bound_finite` (`ExitExamples.lean`) |
| Theorem 3.26 (Excursionary composite limits) | `graph_hausdorff`, `fillComp` (`Excursion.lean`) |
| Example 3.27 (Pathwise Heston to NIG) | `heston_to_nig` (`ExitExamples.lean`) |

### Supporting results

The numbered results of the thesis that the main results rest on.

| Result | Lean |
| --- | --- |
| Definition 1.1 (Set F of functions) | `InF` (`Basic.lean`) |
| Problem 1.2 (IVPs of Chapter 2) | `IsSolution`, `IsMaximalSolution`, `IsSolution.continuousOn_deriv` (`Basic.lean`, `SolutionFacts.lean`) |
| Definition 1.3 (Set G of functions) | `InG` (`Global.lean`) |
| Problem 1.4 (IVPs of Chapter 3) | `IsGlobalSolution` (`Global.lean`) |
| Definition 1.5 (Set Φ of paths) | `InΦ` (`Global.lean`) |
| Definition 1.6 (Set Φ̄ of paths) | `InΦbar` (`Global.lean`) |
| Corollary 2.1 (Maximal uniqueness) | `maximal_existence_uniqueness` (`Maximal.lean`) |
| Lemma 2.3 (Path of zeros) | `continuous_zeroPath`, `f_zeroPath_eq_zero` (`Zeros.lean`) |
| Lemma 2.4 (Càdlàg zeros) | `upperBound_eq_exitTime`, `le_upperBound`, `upperBound_mono`, `upperBound_continuousWithinAt`, `upperBound_tendsto_left`, `f_upperBound_eq_zero`, `upperBound_lt` (`Zeros.lean`) |
| Lemma 2.6 (Spatial solution bounds) | `spatial_bounds` (`Bounds.lean`) |
| Lemma 2.10 (Spatial existence) | `exceeds_iff`, `unbounded_iff` (`Existence.lean`) |
| Lemma 2.16 (Solutions' inverse properties) | `strictMonoOn_solInv`, `continuousOn_solInv`, `hasDerivAt_solInv`, `pos_of_hasDerivAt_solInv`, `solInv_lebesgue`, `solInv_absolutelyContinuous`, `hasDerivWithinAt_solInv_init`, `mul_eq_one_of_hasDerivWithinAt_solInv_init` (`InverseSolution.lean`, `SolutionFacts.lean`) |
| Corollary 3.5 (Solution map surjectivity) | `solution_map_surjective` (`SolutionSet.lean`) |
| Corollary 3.7 | `InW.solution_mem`, `InW.injective`, `InΦϑ.exists_w` (`SolutionSet.lean`) |
| Definition 3.9 (The exit-time functional) | `exitT`, `exitT_eq_invPath` (`ExitTime.lean`) |
| Definition 3.10 (Set N of paths) | `InN` (`ExitTime.lean`) |
| Lemma 3.11 (Exit-time bijectivity) | `InΦbar.inN_exitT`, `InN.inΦbar_exitT`, `InΦbar.exitT_exitT`, `InN.exitT_exitT`, `InΦbar.exitT_eq_iff` (`ExitBijection.lean`, `ExitConstruct.lean`) |
| Definition 3.12 (Exit-time metric) | `exitMetric`, `uniNorm_le`, `tendsto_exitMetric` (`ExitTime.lean`) |
| Corollary 3.15 (Exit-time lower bound) | `InG.exitT_zeroG`, `InG.exitT_barG`, `InG.exitT_barG_le` (`ExitLimits.lean`) |
| Lemma 3.16 (Convergence of bounds) | `bounds_converge` (`ExitLimits.lean`) |
| Definition 3.21 (Set E of paths) | `InE` (`Excursion.lean`) |
| Definition 3.22 (Excursionary metric) | `excT`, `excMetric`, `excGraphStar` (`Excursion.lean`) |

<!-- results:end -->

## Licence

The Lean files in this folder are licensed under the Apache License 2.0, the licence of Mathlib. See [LICENSE](LICENSE).
