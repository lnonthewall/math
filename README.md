# `math` — Written Proofs & Lean 4 Formalizations

**Authors:** Gemini & Opus & GPT Pro

[![Lean 4](https://img.shields.io/badge/Lean-v4.36.0-blue.svg)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.36.0-blueviolet.svg)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)

This repository contains the complete written LaTeX manuscripts and machine-checked **Lean 4 (`v4.36.0`) + Mathlib (`v4.36.0`)** formalizations of the core algebraic, combinatorial, spectral, and rank theorems of two standalone pure-mathematics papers (with external citations and analytical corollaries explicitly noted in the scope notes below):

1. **Paper 1** ([`papers/paper1_minors_tensor/main.tex`](papers/paper1_minors_tensor/main.tex), Lean library **`SemaevRCB`**)<br>
   *Arithmetic Obstructions to Saturated Koszul Flattenings: Cross Products and Exterior Tensors*
2. **Paper 2** ([`papers/paper2_addition_xor/main.tex`](papers/paper2_addition_xor/main.tex), Lean library **`CarryAutomaton`**)<br>
   *Biclique Partitions, Balanced Local Covers, and Fourier Spectra of the Modular Addition–XOR Relation*

All Lean modules compile with **zero `sorry`**, **zero `admit`**, **zero `native_decide`**, **zero `bv_decide`**, **zero custom axioms**, **zero `set_option` overrides**, and **zero compiler warnings**. The umbrella module [`Papers.lean`](Papers.lean) verifies `#print axioms` on all headline theorems at compile time via `#guard_msgs`, confirming exclusive dependence on Lean's standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`). All finite enumeration certificates (including the 14-term KGP integer identity in Paper 1 and the $`s = 3`$ equivariant grid obstruction in Paper 2 Appendix A) are verified inside Lean's trusted kernel via `decide`.

---

## Reproducing Locally

1. Install [`elan`](https://github.com/leanprover/elan) (which reads [`lean-toolchain`](lean-toolchain) and selects `leanprover/lean4:v4.36.0` automatically).
2. Clone the repository, fetch prebuilt Mathlib (`v4.36.0`) oleans, and verify all proofs:

```sh
git clone https://github.com/lnonthewall/math.git
cd math
lake exe cache get
lake build
```

Running `lake build` (or `lake env lean Papers.lean`) compiles the umbrella module [`Papers.lean`](Papers.lean), which runs `#guard_msgs in #print axioms` across the headline theorems of both libraries so local compilation simultaneously verifies the axiom report.

You can also verify each paper's Lean library or typeset either `amsart` manuscript individually:

```sh
lake build SemaevRCB
lake build CarryAutomaton
pdflatex papers/paper1_minors_tensor/main.tex
pdflatex papers/paper2_addition_xor/main.tex
```

---

## Repository Layout

```text
.
├── lean-toolchain                   # leanprover/lean4:v4.36.0
├── lakefile.toml                    # Package manifest (both Lean libraries)
├── Papers.lean                      # Umbrella root & #print axioms guards
├── papers/
│   ├── paper1_minors_tensor/
│   │   └── main.tex                 # Paper 1 LaTeX manuscript (amsart)
│   └── paper2_addition_xor/
│       └── main.tex                 # Paper 2 LaTeX manuscript (amsart)
├── SemaevRCB.lean                   # Paper 1 Lean library root
├── SemaevRCB/
│   ├── Defs.lean                    # Tensor3, ranks, Remark 2.3(a), T_RCB
│   ├── SaturatedFlattening.lean     # Saturation, trace obstruction, Δ_d
│   ├── RCBBlockAndPencil.lean       # T_RCB ≅ T₂ congruence & pencil Ψ_RCB
│   ├── RCBDichotomy.lean            # Koszul det, 9-term limit, Step 5
│   ├── GeneralMinorsAndChar3.lean   # All-char T_m, char-3, 14-term KGP
│   └── ExteriorArithmetic.lean      # Kneser inverse, U_{p,m}, 5-Pfaffian
├── CarryAutomaton.lean              # Paper 2 Lean library root
├── CarryAutomaton/
│   ├── Defs.lean                    # M_t, C_t (K_coreRel/Mat), bicliques
│   ├── CoreBicliques.lean           # Core factorization, 4^s cocycle pairs
│   ├── CyclicCutAndLocalCover.lean  # Carry-cut P_m, lbc = lbp, s = 3 cert
│   ├── NegacyclicSpectrum.lean      # Borrow Walsh blocks & negacyclic DFT
│   └── FocusedExtensions.lean       # Group-circulant, field ranks, DISJ_s
├── LICENSE                          # MIT License
└── README.md
```

---

## Paper 1 Correspondence (`SemaevRCB`)

**Manuscript:** [`papers/paper1_minors_tensor/main.tex`](papers/paper1_minors_tensor/main.tex) — *Arithmetic Obstructions to Saturated Koszul Flattenings: Cross Products and Exterior Tensors*

All Lean declarations in the table below live under [`SemaevRCB/`](SemaevRCB/).

| Paper 1 Result | Hypotheses | Lean 4 Module & Declaration |
| :--- | :--- | :--- |
| **Defs. 2.1–2.2 & Remark 2.3(a)** — Tensor/border ranks & algebraic flattening minor bound | Arbitrary field $`\mathbb{K}`$ | **Defs.lean**: `HasTensorRankLe`, `HasSym12RankLe`, `HasFormalBorderRankLe`, `HasSym12FormalBorderRankLe`, `formalBorderRank_flattening_lower_bound` |
| **Lemma 2.5, Theorem 1.3, & Proposition 2.7** — Rank-sum saturation, trace obstruction $`\mathrm{rank}_{\mathbb{K}}(T) \ge \lfloor N/\kappa \rfloor + 1`$, & polynomial response $`\det(F(T) + t F(S_i)) = \det F(T)(1 + t)^\kappa`$ | Arbitrary field $`\mathbb{K}`$, $`\kappa \neq 0`$ in $`\mathbb{K}`$ | **SaturatedFlattening.lean**: `linearMap_rank_sum_saturation`, `matrix_sum_one_saturated_idempotents`, `trace_obstruction_saturated_flattening`, `det_add_smul_saturated_summand`, `det_add_smul_saturated_flattening` |
| **Lemma 2.4(1) & Lemma 3.1** — Equivalence $`\widetilde{T}_2 \cong T_2`$, $`2 \times 3`$ maximal minors, & $`T_m`$ normalized Koszul trace $`\frac{3}{2}\mathrm{Tr}(C_w U V^T)`$ | $`\mathrm{char}\,\mathbb{K} \neq 2`$ | **RCBBlockAndPencil.lean**: `symEps3_equiv_I2_eps3`<br>**GeneralMinorsAndChar3.lean**: `minors2x3_eval`, `koszulFlat_Im_eps3_mul_inv`, `koszulFlat_Im_eps3_normalized_trace` |
| **Theorem 1.1(1)–(2)** — Universal formal border rank $`9`$ & all-characteristic $`9`$ vs. $`10`$ cube-root-of-unity rank dichotomy of $`T_2`$ and $`\widetilde{T}_2`$ | $`\mathrm{char}\,\mathbb{K} \neq 2`$ (incl. $`\mathrm{char}\,\mathbb{K} = 3`$) | **RCBDichotomy.lean**: `I2_eps3_borderRank_ge_nine`, `symEps3_hasSym12FormalBorderRankLe_nine`, `rank_9_implies_isSquare_neg_three`<br>**GeneralMinorsAndChar3.lean**: `I2_eps3_rank_nine_imp_char_ne_three`, `minors2x3_all_char_dichotomy`, `rcb_minors_char3_corollary` |
| **Propositions 3.2 & 3.3** — Non-Hesse equiangular frames ($`3`$ vs. $`12`$ collinear triples) & equiangular idempotent bases in $`\mathrm{Mat}_d(\mathbb{K})`$ ($`\Delta_d`$ square class & ordered-field obstruction) | $`\mathrm{char}\,\mathbb{K} \neq 2, 3`$ (Prop. 3.2); arbitrary / ordered $`\mathbb{K}`$, $`d \ge 2`$ (Prop. 3.3) | **GeneralMinorsAndChar3.lean**: `nonHesse_equiangular_idempotents`<br>**SaturatedFlattening.lean**: `equiangular_idempotent_basis_discriminant`, `no_equiangular_idempotent_basis_orderedField` |
| **Theorem 1.2(1)–(3)** — General $`m`$ border/split ranks $`\lceil 9m/2 \rceil`$, $`\widetilde{T}_{2k}`$ rank $`9k`$, $`\mathrm{rank}(\varepsilon_3) = 5`$, 14-term $`\mathbb{Z}[1/2]`$ KGP scheme ($`\mathrm{rank}_{\mathbb{K}}(T_3) = 14`$), & nonsplit bounds for $`m = 4, 5, 6`$ | $`\mathrm{char}\,\mathbb{K} \neq 2`$, $`m, k \ge 1`$ | **GeneralMinorsAndChar3.lean**: `eps3_exact_rank_and_borderRank_five`, `det_koszulFlat_Im_eps3`, `Im_eps3_exact_formalBorderRank`, `Im_eps3_exact_rank_of_primCubeRoot`, `symEps3Block_equiv_Im_eps3`, `symEps3Block_exact_sym12FormalBorderRank`, `symEps3Block_exact_sym12Rank_of_primCubeRoot`, `I3_eps3_hasTensorRankLe_fourteen`, `I3_eps3_exact_rank_fourteen`, `I4_eps3_hasTensorRankLe_nineteen`, `I5_eps3_hasTensorRankLe_twentyfour`, `I6_eps3_hasTensorRankLe_twentyeight` |
| **Theorem 1.2(4)** — Uniform characteristic $`3`$ lower bound $`\mathrm{rank}_{\mathbb{K}}(T_m) \ge \lfloor 9m/2 \rfloor + 1`$, strict gap $`9k + 1 > 9k`$ for $`T_{2k}, \widetilde{T}_{2k}`$, & exact values $`\mathrm{rank}_{\mathbb{K}}(T_4) = 19`$, $`\mathrm{rank}_{\mathbb{K}}(T_6) = 28`$ | $`\mathrm{char}\,\mathbb{K} = 3`$, $`m, k \ge 1`$ | **GeneralMinorsAndChar3.lean**: `Im_eps3_char3_rank_ge_floor_add_one`, `Im_eps3_even_char3_strict_gap`, `symEps3Block_char3_strict_gap`, `I4_eps3_char3_exact_rank_nineteen`, `I6_eps3_char3_exact_rank_twentyeight` |
| **Lemmas 5.1–5.2, Corollary 5.3, Proposition 5.4, & Theorem 1.4** — Signed Kneser blocks ($`B_0 = (1)`$), explicit $`\mathbb{Z}[1/(q+1)!]`$ inverse, coordinate trace, shared exterior bound $`\mathrm{rank}_{\mathbb{K}}(U_{p,m}) \ge \lfloor m a^2 / \kappa \rfloor + 1`$, & characteristic $`5`$ 5-Pfaffian bound $`\ge 51`$ | Odd prime $`\ell = 2p + 1`$, $`\mathrm{char}\,\mathbb{K} = \ell`$, $`p, m \ge 1`$ | **ExteriorArithmetic.lean**: `psiFlat_Omega_signed_kneser_block`, `kneserMat_mul_adj`, `kneserMat_mul_inv`, `psiFlat_Omega_invertible`, `psiFlat_pm_U_invertible`, `psiFlat_Omega_coord_trace`, `psiFlat_pm_coord_trace`, `shared_exterior_prime_char_rank_ge`, `pfaffian5_shared3_char5_rank_ge_51` |
| **Proposition 1.5 & Remark 6.1** — (1,2)-congruence $`T_{\mathrm{RCB}} \cong \widetilde{T}_2`$, completeness, & pencil $`\Psi_{\mathrm{RCB}}`$ ($`\mathrm{rank} = 8`$, $`\underline{\mathrm{rank}} = 6`$) | $`\mathrm{char}\,\mathbb{K} \neq 2, 3`$, $`b \neq 0`$ | **RCBBlockAndPencil.lean**: `rcb_cross_product_identity`, `T_RCB_sym12Congruent_symEps3`, `rcb_unconditionally_complete_iff`, `Psi_RCB_equiv_kroneckerDouble`, `Psi_RCB_rank_ge_eight`, `Psi_RCB_hasTensorRankLe_eight`, `Psi_RCB_borderRank_ge_six`, `Psi_RCB_hasFormalBorderRankLe_six`<br>**RCBDichotomy.lean**: `rcb_border_rank_nine`, `rcb_rank_dichotomy` |

> **Scope note:** Every main theorem and proposition of Paper 1 (Theorems 1.1–1.4, Propositions 1.5, 2.7, 3.3, and 5.4, Lemmas 2.4, 2.5, 3.1, 5.1, and 5.2, Corollary 5.3, and Remarks 2.3(a) and 6.1) is directly formalized in the six-module `SemaevRCB` library. In particular, `I3_eps3_exact_rank_fourteen` kernel-verifies the 14-product $`\mathbb{Z}[1/2]`$ scheme of Khoruzhii, Gelß, and Pokutta ([arXiv:2511.10786](https://arxiv.org/abs/2511.10786)) in Lean, yielding the formalized characteristic $`3`$ exact ranks $`19`$ and $`28`$ for $`T_4`$ and $`T_6`$, and `shared_exterior_prime_char_rank_ge` proves Theorem 1.4 for all $`p, m \ge 1`$ with $`2p + 1`$ prime (exact-rank lower bounds only for $`p \ge 2`$). Only the general $`(a, b, c)`$ algebraic parameter family of Proposition 3.2 beyond the formalized $`(2, 1, 1)`$ witness (`nonHesse_equiangular_idempotents`), together with the remark-level Jacobi/Euler observation (Remark 2.6) and the $`T_5`$ rank-23 slack identities (Remark 4.1(1)), remains written-only algebra.

---

## Paper 2 Correspondence (`CarryAutomaton`)

**Manuscript:** [`papers/paper2_addition_xor/main.tex`](papers/paper2_addition_xor/main.tex) — *Biclique Partitions, Balanced Local Covers, and Fourier Spectra of the Modular Addition–XOR Relation*

All Lean declarations in the table below live under [`CarryAutomaton/`](CarryAutomaton/).

> **Note:** The carry-core matrix denoted $`C_t`$ in the manuscript corresponds to `K_coreRel s` and `K_coreMat R s` with $`s = t - 1`$ in Lean.

| Paper 2 Result | Lean 4 Module & Declaration |
| :--- | :--- |
| **Section 1** — Biregularity & $`t \ge 2`$ obstruction $`\bigl(\begin{smallmatrix}1 & 1 \\ 0 & 1\end{smallmatrix}\bigr)`$ to single-valued equality labels | **CoreBicliques.lean**: `M_rel_edge_card`, `M_rel_two_by_two_obstruction`, `M_rel_no_single_valued` |
| **Theorem 2.1** — Factorization $`M_t \cong I_2 \otimes C_t \otimes J_2`$, anchor lifting, $`4^s`$ cocycle pairs, $`(2X + 2Y)^s`$, $`8^s`$ bicliques, & $`A_{\max}`$ | **CoreBicliques.lean**: `M_rel_core_factorization`, `K_coreRel_biclique_iff_three_conds`, `maxCocyclePairs_card`, `maxCocyclePairs_shape_gf`, `K_coreRel_maxBicliques_card`, `M_rel_biclique_area_le` |
| **Lemma 2.2, Def. 2.3, & Theorem 2.4** — Modular-quotient carry identity, cyclic carry-cut partitions $`\mathcal{P}_m`$, $`\mathrm{bc} = \mathrm{cp} = 2^{2t-1}`$, degree-product & real-weighted ($`\alpha, \beta > 0`$) optima, & `iff` equality criteria | **CyclicCutAndLocalCover.lean**: `modular_quotient_carry_identity`, `mechanismIICStar_isPartition`, `bc_M_lower`, `prod_load_M_lower`<br>**FocusedExtensions.lean**: `weighted_sum_M_lower_real`, `weighted_sum_M_attained_real`, `bc_M_eq_iff`, `prod_load_M_eq_iff` |
| **Lemma 3.1, Theorem 3.2, Proposition 3.3, & Proposition A.1** — Balanced 4-star blowup lemma, $`\mathrm{lbc} = \mathrm{lbp} = \lceil(2^{\lfloor s/2\rfloor} + 2^{\lceil s/2\rceil})/2\rceil`$, & kernel-verified $`s = 3`$ equivariant obstruction | **FocusedExtensions.lean**: `abstract_balanced_star_blowup`<br>**CyclicCutAndLocalCover.lean**: `local_load_lower_M`, `starBlowupPartition`, `exists_optimal_local_partition_K`, `exists_optimal_local_partition_M`, `no_equivariant_cover_K4_load_le_3`, `prop_A1_s3_grid_obstruction` |
| **Theorem 4.1** — Group-circulant invariance, negacyclic identity $`D\widetilde{H}_\alpha D = G_\alpha(T)`$, all-field ranks ($`\frac{2 \cdot 4^s + 1}{3}`$ for $`\mathrm{char}\,F \neq 2`$ vs. $`\binom{2^s + 1}{2}`$ for $`\mathrm{char}\,F = 2`$), sharp cosine envelope, & $`\Lambda(C_t) = 2^{t-3/2}`$ | **FocusedExtensions.lean**: `M_rel_group_circulant`, `K_coreRel_group_circulant`, `rank_K_coreMat_char_ne_two`, `rank_M_mat_char_ne_two`, `rank_K_coreMat_char_two`, `rank_K_coreMat_char_two_choose`, `rank_M_mat_char_two`<br>**NegacyclicSpectrum.lean**: `walsh_conj_K_coreMat`, `D_sign_conj_Htilde_eq_G_alpha_int`, `spectralNorm2_H_alpha_eq_envelope_iff`, `centeredSpectralGap_K_core` |
| **Proposition 4.2 & Remark 4.3** — Embedded $`\mathrm{DISJ}_s`$ submatrix, explicit $`\le 8s`$ zero-rectangle cover ($`8s - 4`$ for $`s \ge 1`$), signed margin witness ($`\gamma_2(S) \le 16s + 1`$), & centered spectral cover bound | **FocusedExtensions.lean**: `disj_embedded_in_K_coreRel`, `zero_cover_K_coreRel_card_le_eight_s`, `margin_witness_K_coreRel`<br>**NegacyclicSpectrum.lean**: `centered_spectral_biclique_cover_div_le`, `K_coreRel_spectral_avg_degree_lower_bound` |

> **Scope note:** All core algebraic, combinatorial, spectral, arbitrary-field rank, $`\mathrm{DISJ}_s`$ embedding, $`\le 8s`$ zero-cover, and signed margin-witness theorems of Paper 2 are directly formalized in `CarryAutomaton` (including the universal bounds and `iff` equality characterizations for $`\mathrm{bc}`$ and the degree product, plus the universal lower bound and attainment for real weights $`\alpha, \beta > 0`$). The communication-complexity, $`\gamma_2`$ factorization-norm, and discrepancy deductions (invoking Razborov, Aaronson–Ambainis, and Shi–Zhu on $`\mathrm{DISJ}_s`$), the equality-case structure for general real weights $`(\alpha, \beta)`$, and the $`O(1)`$ word-RAM interpretation of the formalized `BitVec` masks follow analytically in Sections 2 and 4 of the manuscript.

---

## License

Released under the [MIT License](LICENSE) — Copyright (c) 2026 Gemini & Opus & GPT Pro.
