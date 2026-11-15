# PolygonLean

A Lean 4 / Mathlib formalization of the mathematics in

1. D. Johnston, *Online Testing Entropy and Entropy Tests with a Two State Markov
   Model*, SPACE 2024, LNCS 15351, pp. 110–128 (the "first paper"), and
2. *An Exact Analytic Derivation of the Polygon Test Boundary for Online
   Min-Entropy Testing of Binary Data* (`../paper/polygon_exact_paper.tex`, the
   "second paper").

Everything is proved. There is no `sorry`, `admit` or `axiom`; the main theorems
depend only on Lean's standard axioms (`propext`, `Classical.choice`,
`Quot.sound`).

```bash
lake exe cache get   # fetch prebuilt Mathlib
lake build
```

## Map from the papers to the Lean theorems

| Paper statement | Lean |
|---|---|
| **First paper** | |
| Model, Eqs. (1)–(2), stationary distribution | `Markov`, `Markov.stationary` |
| Eqs. (3), (4), (5), (6), (8), (10) | `Markov.eq3` … `Markov.eq10` |
| Eqs. (11)–(12) and the (μ, SCC) ↔ (P₀₁, P₁₀) bijection | `Markov.ofMuScc`, `ofMuScc_mu`, `ofMuScc_scc`, `ext_of_mu_scc` |
| Eq. (18), symbol probability; normalization | `Markov.symProb`, `symProb_cons`, `sum_symProb`, `sum_unweighted` |
| Tables 3 and 4, MCV candidate probabilities | `prob_ones`, `prob_zeros`, `prob_alt_odd`, `prob_alt_even`, `prefactor_one`, `prefactor_zero` |
| Eqs. (13)–(15) | `eq13`, `eq14`, `eq15` |
| Eq. (19) and the min-entropy rate | `minEntropyPerBit`, **`minEntropy_tendsto`** |
| §11: `n-1 = Σ countab`, `count1 = count10 + count11`, `count01 ≈ count10` | `cnt_sum`, `count1_eq`, `count0_eq`, `cnt01_cnt10_close` |
| Eq. (20) → Eq. (21), SCC from counts | `knuthSCC`, `eq21`, `scc_normalized` |
| §12 polygon (Table 5), its edges, integer forms, `n = 2304` | `First.edges_through_corners`, `accepts_iff_int`, `acceptsCounts_iff`, `constants_2304` |
| §12–13 shift-add logic and 17-bit datapath | `First.shift_add`, `First.fits_17_bits` |
| **Second paper** | |
| §2 inverse map (Eq. 1), in the model and in counts | `Markov.inverse_map`, `counts_inverse`, `Markov.scc_from_counts` |
| §3 Eq. (2) agrees with the model's rate | `Hinf_model` |
| §4 `R_H` = intersection of the constraints | **`Hinf_ge_iff`** |
| Prop. 1: ellipse, discriminant, lower branch, convex | `ellipse_expand`, `ellipse_discriminant`, `ellipse_iff_arc`, `yArc_convex` |
| Complement symmetry | `InRegion.complement`, `corner_symmetry` |
| §5.1 corners A–E, A′, C′ and their uniqueness | `cornerA` … `cornerA'`, `cornerB_unique`, `cornerE_unique`, `cornerD_unique`, `cornerC'_unique`, `cornerA'_unique` |
| Discarded roots | `arc_neg_of_lt_xE`, `arc_lt_lCD_of_xD_lt` |
| Regime condition, `H* = log₂ φ` | `xA_le_xE_iff`, `xD_le_xC_iff`, `yA'_pos_iff`, `transition_coincide`, `quad_nonneg_iff`, `regime_iff`, `Hstar_between` |
| Apex B inside iff p ≥ 1/2 | `apexB_in_iff` |
| Markov cross-check table | `markov_corners`, `A'_feasible_iff` |
| §6 slope-1 chord and its intercept c(H) | `chord5`, `chord3` |
| Chord lies above the arc | `chord5_above`, `chord3_above` |
| Maximum chord–arc gap | `chord_gap_max` |
| §7.1 perfect fit for H ≤ H* | `chord5_perfect_fit` |
| §7.3 monotonicity, nesting | `InRegion.mono`, `region_nested` |
| Linear tests are sound (five-edge / triangle) | **`linear5_entropy`**, **`linear3_entropy`** |
| §8 integer comparators are one-sided | **`int5_sound`**, **`int3_sound`** |
| Table 3 (every entry) and §9 `P₂` | `row1` … `row9` |
| `A₁ + B₁ = 8191` | `A1_add_B1`, `floor_add_floor` |
| §7.2 the H = 0.5 case | `half_case`, `half_arc_exact` |
| §8 spot check, 25-bit comparison | `spot_check`, `bitwidth_25` |
| §9 exact arc test is sound; 35/33-bit widths | **`intArc_sound`**, `arc_bitwidth` |
| Worked instance: the H = 0.4, n = 2304 integer test is sound | `row4_sound` |
| The first paper's polygon is not conservative | `First.not_conservative`, `First.not_conservative_counts` |

## Discrepancies found while formalizing

1. **Tables 3 and 4 of the first paper (prefactors). Agreed with the author;
   correction: replace `(P₀₁ + P₁₁)` with `μ` and `(P₀₀ + P₁₀)` with `1 - μ`.**
   The prefactor accounts for the unknown preceding bit by adding the two cases
   `P₀₁x + P₁₁x`. Eq. (18) weights them by the probability of the preceding
   bit, `P₀P₀₁x + P₁P₁₁x = μx`. Unweighted, the probabilities of all `n`-bit
   symbols sum to 2 (`sum_unweighted`) rather than 1 (`sum_symProb`); e.g. the
   1-bit symbol `1` at `P₀₁ = 0.9`, `P₁₀ = 0.1` gets 1.8. The corrected
   prefactors are `prefactor_one` and `prefactor_zero`. The prefactor does not
   grow with `b`, so the asymptotic rate and the second paper's boundary are
   unaffected; only finite-`b` MCV probabilities change. The second paper's §3
   has been updated to state the weighted prefactors.
2. **Second paper §9, `P₂` at H = 0.6. Fixed in the paper.**
   `⌊2^{-1.2}·4096⌋ = ⌊1782.89⌋ = 1782`; the draft printed 1783, which was
   rounded up and so enlarged the accept region (the non-conservative
   direction). See `row6`, `P2_row6_paper_value_too_large`.
3. **Second paper Table 3, bitwidth column. Fixed in the paper.** Every entry
   was one bit short for a signed comparison: e.g. `631706 > 2¹⁹`, so `-A₀`
   needs 21 bits, not 20. The column now gives the listing's
   `ceil(log2(A0)) + 1`: 21, 22, 22, 23, 23, 23, 23, 23, 24. See `bitwidth_column`. (The 25-bit claim in the text is right:
   `bitwidth_25`.)
4. **Second paper §6, maximum chord–arc gap. Fixed in the paper.** The draft
   gave `c(H) - (1-p)/2`. The gap at `x = 1/2` is `(1/2 - c) - (1-p)/2 = p/2 - c`,
   which is the quoted value 0.014 at H = 0.4 (the old formula gives 0.244). See `chord_gap_max`.
5. **First paper, H = 0.4 polygon.** The graphically extracted polygon accepts
   some points whose entropy rate is below 0.4, e.g. `(0.5, 0.39)`, or
   `count1 = 1152, count11 = 898` for `n = 2304`. This confirms the motivation of
   the second paper. See `First.not_conservative_counts`.

## Scope notes

* The first paper's claim that the MCV of a `b`-bit symbol is always one of the
  repeating-pattern candidates of Tables 3/4 is not formalized as stated. What is
  proved is the consequence the second paper uses: every symbol has probability
  at most `K·mᵇ⁻¹` and one of the candidates has probability at least `c·mᵇ⁻¹`,
  so the per-bit min-entropy converges to `-log₂ m` (`minEntropy_tendsto`).
* The statistical behaviour of the test (sampling error of the counts) is
  outside the papers' derivations and is not modelled.
