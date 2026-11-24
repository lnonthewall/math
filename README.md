# `math` — Written Proofs & Lean 4 Formalizations

**Authors:** Gemini & Opus & GPT Pro

[![Lean 4 CI](https://github.com/lnonthewall/math/actions/workflows/ci.yml/badge.svg)](https://github.com/lnonthewall/math/actions/workflows/ci.yml)
[![Lean 4](https://img.shields.io/badge/Lean-v4.36.0-blue.svg)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.36.0-blueviolet.svg)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)

This repository contains the complete written LaTeX manuscripts and machine-checked **Lean 4 (`v4.36.0`) + Mathlib (`v4.36.0`)** formalizations for two standalone pure-mathematics papers:

1. **Paper 1** ([`papers/paper1_minors_tensor/main.tex`](papers/paper1_minors_tensor/main.tex), Lean library **`SemaevRCB`**)<br>
   *Arithmetic Rank Dichotomy of the* $`2 \times 3`$ *Maximal-Minors Tensor and Shared-Input Cross Products*
2. **Paper 2** ([`papers/paper2_addition_xor/main.tex`](papers/paper2_addition_xor/main.tex), Lean library **`CarryAutomaton`**)<br>
   *Biclique Partitions, Balanced Local Covers, and Fourier Spectra of the Modular Addition–XOR Relation*

All Lean modules compile with **zero `sorry`**, **zero `admit`**, **zero `native_decide`**, **zero `bv_decide`**, **zero custom axioms**, **zero `set_option` overrides**, and **zero compiler warnings**, relying exclusively on Lean's standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`). All finite enumeration certificates (including the $`s = 3`$ equivariant grid obstruction in Paper 2 Appendix A) are verified inside Lean's trusted kernel via `decide`.

---

## Quick Start

Install [`elan`](https://github.com/leanprover/elan), fetch prebuilt Mathlib oleans, and build the complete repository:

```sh
lake exe cache get
lake build
```

You can also build each paper's Lean library individually:

```sh
lake build SemaevRCB
lake build CarryAutomaton
```

---

## Repository Layout

```text
.
├── lean-toolchain                   # leanprover/lean4:v4.36.0
├── lakefile.toml                    # Package manifest (both Lean libraries)
├── Papers.lean                      # Umbrella root importing both libraries
├── papers/
│   ├── paper1_minors_tensor/
│   │   └── main.tex                 # Paper 1 LaTeX manuscript (amsart)
│   └── paper2_addition_xor/
│       └── main.tex                 # Paper 2 LaTeX manuscript (amsart)
├── SemaevRCB.lean                   # Paper 1 Lean library root
├── SemaevRCB/
│   ├── Defs.lean                    # Tensor3, ranks, Remark 2.3(a), T_RCB
│   ├── RCBBlockAndPencil.lean       # T_RCB ≅ T₂ congruence & pencil Ψ_RCB
│   ├── RCBDichotomy.lean            # Koszul det, 9-term limit, Step 5
│   └── GeneralMinorsAndChar3.lean   # All-char dichotomy, T_m, non-Hesse
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

**Manuscript:** [`papers/paper1_minors_tensor/main.tex`](papers/paper1_minors_tensor/main.tex) — *Arithmetic Rank Dichotomy of the* $`2 \times 3`$ *Maximal-Minors Tensor and Shared-Input Cross Products*

All Lean declarations in the table below live under [`SemaevRCB/`](SemaevRCB/).

| Paper 1 Result | Hypotheses | Lean 4 Module & Declaration |
| :--- | :--- | :--- |
| **Defs. 2.1–2.2 & Remark 2.3(a)** — Tensor/border ranks & algebraic flattening minor bound | Arbitrary field $`\mathbb{K}`$ | **Defs.lean**: `HasTensorRankLe`, `HasSym12RankLe`, `HasFormalBorderRankLe`, `HasSym12FormalBorderRankLe`, `formalBorderRank_flattening_lower_bound` |
| **Lemma 2.4(1)** — Equivalence $`\widetilde{T}_2 \cong T_2`$ & polarized $`2 \times 3`$ maximal-minors evaluation | $`\mathrm{char}\,\mathbb{K} \neq 2`$ | **RCBBlockAndPencil.lean**: `symEps3_equiv_I2_eps3`<br>**GeneralMinorsAndChar3.lean**: `minors2x3_eval` |
| **Theorem 1.1(1)** — Universal formal border rank $`9`$ of $`T_2`$ and $`\widetilde{T}_2`$ | $`\mathrm{char}\,\mathbb{K} \neq 2`$ (incl. $`\mathrm{char}\,\mathbb{K} = 3`$) | **RCBDichotomy.lean**: `I2_eps3_borderRank_ge_nine`, `symEps3_hasSym12FormalBorderRankLe_nine` |
| **Theorem 1.1(2)** — All-characteristic ($`\mathrm{char}\,\mathbb{K} \neq 2`$) $`9`$ vs. $`10`$ cube-root-of-unity rank dichotomy | $`\mathrm{char}\,\mathbb{K} \neq 2`$ (incl. $`\mathrm{char}\,\mathbb{K} = 3`$) | **GeneralMinorsAndChar3.lean**: `I2_eps3_rank_nine_imp_char_ne_three`, `minors2x3_all_char_dichotomy`, `rcb_minors_char3_corollary`<br>**RCBDichotomy.lean**: `rank_9_implies_isSquare_neg_three` |
| **Proposition 3.1** — Non-Hesse equiangular rank-1 idempotent frames ($`3`$ vs. $`12`$ collinear triples) | $`\mathrm{char}\,\mathbb{K} \neq 2, 3`$, $`\omega^2 + \omega + 1 = 0`$ | **GeneralMinorsAndChar3.lean**: `nonHesse_equiangular_idempotents` |
| **Theorem 1.2(1)–(2)** — General $`m`$ Koszul $`\det = (-2)^m`$, $`\underline{\mathrm{rank}}(T_m) = \lceil 9m/2 \rceil`$, $`\mathrm{rank}(\varepsilon_3) = 5`$, & split-field rank | $`\mathrm{char}\,\mathbb{K} \neq 2`$, $`m \ge 1`$ | **GeneralMinorsAndChar3.lean**: `eps3_exact_rank_and_borderRank_five`, `det_koszulFlat_Im_eps3`, `Im_eps3_exact_formalBorderRank`, `Im_eps3_exact_rank_of_primCubeRoot` |
| **Proposition 1.3 & Remark 5.1** — (1,2)-congruence $`T_{\mathrm{RCB}} \cong \widetilde{T}_2`$, completeness, & pencil $`\Psi_{\mathrm{RCB}}`$ ($`\mathrm{rank} = 8`$, $`\underline{\mathrm{rank}} = 6`$) | $`\mathrm{char}\,\mathbb{K} \neq 2, 3`$, $`b \neq 0`$ | **RCBBlockAndPencil.lean**: `rcb_cross_product_identity`, `T_RCB_sym12Congruent_symEps3`, `rcb_unconditionally_complete_iff`, `Psi_RCB_equiv_kroneckerDouble`, `Psi_RCB_rank_ge_eight`, `Psi_RCB_hasTensorRankLe_eight`, `Psi_RCB_borderRank_ge_six`, `Psi_RCB_hasFormalBorderRankLe_six`<br>**RCBDichotomy.lean**: `rcb_border_rank_nine`, `rcb_rank_dichotomy` |

> **Scope note:** In Theorem 1.2(3), the lower bound $`\underline{\mathrm{rank}}_{\mathbb{K}}(T_3) = 14`$ is formalized in `Im_eps3_exact_formalBorderRank`, while the matching nonsplit upper bound $`\mathrm{rank}_{\mathbb{K}}(T_3) \le 14`$ cites the explicit $`\mathbb{Z}[1/2]`$ scheme of Khoruzhii, Gelß, and Pokutta ([arXiv:2511.10786](https://arxiv.org/abs/2511.10786)).

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

---

## License

Released under the [MIT License](LICENSE) — Copyright (c) 2026 Gemini & Opus & GPT Pro.
