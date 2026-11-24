# `math` — Written Proofs & Lean 4 Formalizations

**Authors:** Gemini & Opus & GPT Pro

[![Lean 4](https://img.shields.io/badge/Lean-v4.36.0-blue.svg)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.36.0-blueviolet.svg)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)

This repository contains the complete written LaTeX manuscripts and machine-checked **Lean 4 (`v4.36.0`) + Mathlib (`v4.36.0`)** formalizations for two standalone pure-mathematics papers:

1. **Paper 1** ([`papers/paper1_minors_tensor/main.tex`](papers/paper1_minors_tensor/main.tex), Lean library **`SemaevRCB`**)  
   *Arithmetic Rank Dichotomy of the $2 \times 3$ Maximal-Minors Tensor and Shared-Input Cross Products*
2. **Paper 2** ([`papers/paper2_addition_xor/main.tex`](papers/paper2_addition_xor/main.tex), Lean library **`CarryAutomaton`**)  
   *Biclique Partitions, Balanced Local Covers, and Fourier Spectra of the Modular Addition–XOR Relation*

All Lean modules compile with **zero `sorry`**, **zero `admit`**, **zero `native_decide`**, **zero custom axioms**, **zero `set_option` overrides**, and **zero compiler warnings**, relying exclusively on Lean's standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`). All finite enumeration certificates (including the $s = 3$ equivariant grid obstruction in Paper 2 Appendix A) are verified inside Lean's trusted kernel via `decide`.

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
├── lean-toolchain                                # leanprover/lean4:v4.36.0
├── lakefile.toml                                 # Package manifest (SemaevRCB, CarryAutomaton, Papers)
├── Papers.lean                                   # Umbrella root importing both libraries
├── papers/
│   ├── paper1_minors_tensor/
│   │   └── main.tex                              # Written manuscript for Paper 1 (LaTeX / amsart)
│   └── paper2_addition_xor/
│       └── main.tex                              # Written manuscript for Paper 2 (LaTeX / amsart)
├── SemaevRCB.lean                                # Paper 1 Lean library root
├── SemaevRCB/
│   ├── Defs.lean                                 # Tensor3, ranks, border rank, Remark 2.4(a), ε₃, T_RCB
│   ├── RCBBlockAndPencil.lean                    # T_RCB ≅ T₂ congruence & complexified pencil Ψ_RCB
│   ├── RCBDichotomy.lean                         # Koszul det = 4, 9-term degeneration, Hesse, Step 5 obstruction
│   └── GeneralMinorsAndChar3.lean                # All-char (char ≠ 2) dichotomy, T_m hierarchy, non-Hesse frames
├── CarryAutomaton.lean                           # Paper 2 Lean library root
├── CarryAutomaton/
│   ├── Defs.lean                                 # M_t, C_t (K_coreRel/K_coreMat), bicliques, covers, loads
│   ├── CoreBicliques.lean                        # M_t ≅ I₂ ⊗ C_t ⊗ J₂, 4^s maximal pairs, (2X+2Y)^s, 8^s bicliques
│   ├── CyclicCutAndLocalCover.lean               # Cyclic carry-cut partitions, lbc = lbp, s = 3 obstruction
│   ├── NegacyclicSpectrum.lean                   # Borrow-coordinate Walsh blocks & negacyclic DFT spectrum
│   └── FocusedExtensions.lean                    # Group-circulant view, all-field ranks, real weights, eq-iffs, DISJ/margin
├── LICENSE                                       # MIT License
└── README.md
```

---

## Paper 1 Correspondence (`SemaevRCB`)

**Manuscript:** [`papers/paper1_minors_tensor/main.tex`](papers/paper1_minors_tensor/main.tex) — *Arithmetic Rank Dichotomy of the $2 \times 3$ Maximal-Minors Tensor and Shared-Input Cross Products*

| Paper 1 Result | Hypotheses | Lean 4 Module & Declaration |
| :--- | :--- | :--- |
| Defs. 2.1–2.3 & Remark 2.4(a) (Purely algebraic polynomial flattening minor bound) | Arbitrary field $\mathbb{K}$ | `SemaevRCB/Defs.lean`: `HasTensorRankLe`, `HasSym12RankLe`, `HasFormalBorderRankLe`, `formalBorderRank_flattening_lower_bound` |
| Polarized $2 \times 3$ maximal-minors evaluation | $\operatorname{char}\mathbb{K} \neq 2$ | `SemaevRCB/GeneralMinorsAndChar3.lean`: `minors2x3_eval` |
| **Theorem 1.1(1)** — Universal formal border rank $9$ of $T_2$ and $\widetilde{T}_2$ | $\operatorname{char}\mathbb{K} \neq 2$ (incl. $\operatorname{char}\mathbb{K} = 3$) | `SemaevRCB/RCBDichotomy.lean`: `I2_eps3_borderRank_ge_nine`, `symEps3_hasSym12FormalBorderRankLe_nine` |
| **Theorem 1.1(2)** — All-characteristic ($\operatorname{char}\mathbb{K} \neq 2$) $9$-vs-$10$ cube-root-of-unity rank dichotomy | $\operatorname{char}\mathbb{K} \neq 2$ (incl. $\operatorname{char}\mathbb{K} = 3$) | `SemaevRCB/GeneralMinorsAndChar3.lean`: `I2_eps3_rank_nine_imp_char_ne_three`, `minors2x3_all_char_dichotomy`, `rcb_minors_char3_corollary`; `SemaevRCB/RCBDichotomy.lean`: `rank_9_implies_isSquare_neg_three` |
| **Proposition 3.1** — Non-Hesse equiangular rank-1 idempotent family ($3$ collinear triples vs. $12$) | $\operatorname{char}\mathbb{K} \neq 2, 3$, $\omega^2+\omega+1=0$ | `SemaevRCB/GeneralMinorsAndChar3.lean`: `nonHesse_equiangular_idempotents` |
| **Theorem 1.2(1)–(2)** — General-$m$ Koszul $\det = (-2)^m$, exact $\underline{\operatorname{rank}}(T_m) = \lceil 9m/2 \rceil$, $\operatorname{rank}(\varepsilon_3) = 5$, and split-field rank | $\operatorname{char}\mathbb{K} \neq 2$, $m \ge 1$ | `SemaevRCB/GeneralMinorsAndChar3.lean`: `eps3_exact_rank_and_borderRank_five`, `det_koszulFlat_Im_eps3`, `Im_eps3_exact_formalBorderRank`, `Im_eps3_exact_rank_of_primCubeRoot` |
| **Proposition 1.3** — $(1,2)$-congruence $T_{\mathrm{RCB}} \cong \widetilde{T}_2$ & complexified pencil $\Psi_{\mathrm{RCB}}$ ($\operatorname{rank} = 8$, $\underline{\operatorname{rank}} = 6$) | $\operatorname{char}\mathbb{K} \neq 2, 3$, $b \neq 0$ | `SemaevRCB/RCBBlockAndPencil.lean`: `rcb_cross_product_identity`, `T_RCB_sym12Congruent_symEps3`, `Psi_RCB_equiv_kroneckerDouble`, `Psi_RCB_rank_ge_eight`, `Psi_RCB_hasFormalBorderRankLe_six`; `SemaevRCB/RCBDichotomy.lean`: `rcb_rank_dichotomy` |

*Scope note:* In Theorem 1.2(3), the lower bound $\underline{\operatorname{rank}}_{\mathbb{K}}(T_3) = 14$ is formalized in `Im_eps3_exact_formalBorderRank`, while the matching nonsplit upper bound $\operatorname{rank}_{\mathbb{K}}(T_3) \le 14$ cites the explicit $\mathbb{Z}[1/2]$ scheme of Khoruzhii, Gelß, and Pokutta (`arXiv:2511.10786`).

---

## Paper 2 Correspondence (`CarryAutomaton`)

**Manuscript:** [`papers/paper2_addition_xor/main.tex`](papers/paper2_addition_xor/main.tex) — *Biclique Partitions, Balanced Local Covers, and Fourier Spectra of the Modular Addition–XOR Relation*

*(Note: the carry-core matrix denoted $C_t$ in the manuscript corresponds to `K_coreRel s` / `K_coreMat R s` with $s = t - 1$ in Lean.)*

| Paper 2 Result | Lean 4 Module & Declaration |
| :--- | :--- |
| Section 1 — Biregularity & $t \ge 2$ $\begin{psmallmatrix}1&1\\0&1\end{psmallmatrix}$ single-valued obstruction | `CarryAutomaton/CoreBicliques.lean`: `M_rel_edge_card`, `M_rel_two_by_two_obstruction`, `M_rel_no_single_valued` |
| **Theorem 2.1** — $M_t \cong I_2 \otimes C_t \otimes J_2$, anchor lifting, $4^s$ maximal cocycle pairs, $(2X+2Y)^s$, $8^s$ bicliques, $A_{\max}$ | `CarryAutomaton/CoreBicliques.lean`: `M_rel_core_factorization`, `K_coreRel_biclique_iff_three_conds`, `maxCocyclePairs_card`, `maxCocyclePairs_shape_gf`, `K_coreRel_maxBicliques_card`, `M_rel_biclique_area_le` |
| **Lemma 2.2, Def. 2.3, & Theorem 2.4** — Modular-quotient carry identity, cyclic carry-cut partitions $\mathcal{P}_m$, exact $\operatorname{bc}=\operatorname{cp}=2^{2t-1}$, degree-product, real-weighted ($\alpha,\beta > 0$) optima, & `iff` equality cases | `CarryAutomaton/CyclicCutAndLocalCover.lean`: `modular_quotient_carry_identity`, `mechanismIICStar_isPartition`, `bc_M_lower`, `prod_load_M_lower`; `CarryAutomaton/FocusedExtensions.lean`: `weighted_sum_M_lower_real`, `weighted_sum_M_attained_real`, `bc_M_eq_iff`, `prod_load_M_eq_iff` |
| **Lemma 3.1, Theorem 3.2, & Proposition 3.3 (Appendix A)** — Abstract balanced $4$-star blowup lemma, exact $\operatorname{lbc} = \operatorname{lbp} = \lceil(2^{\lfloor s/2\rfloor}+2^{\lceil s/2\rceil})/2\rceil$, & kernel-verified $s = 3$ equivariant obstruction | `CarryAutomaton/FocusedExtensions.lean`: `abstract_balanced_star_blowup`; `CarryAutomaton/CyclicCutAndLocalCover.lean`: `local_load_lower_M`, `starBlowupPartition`, `exists_optimal_local_partition_K`, `exists_optimal_local_partition_M`, `no_equivariant_cover_K4_load_le_3`, `prop_A1_s3_grid_obstruction` |
| **Theorem 4.1** — Abelian group-circulant invariance, integer negacyclic conjugation $D\widetilde{H}_\alpha D = G_\alpha(T)$ & telescoping inverse, all-field ranks ($\frac{2\cdot 4^s+1}{3}$ for $\operatorname{char} F \neq 2$ vs. $\binom{2^s+1}{2}$ for $\operatorname{char} F = 2$), sharp cosine envelope, & $\Lambda(C_t) = 2^{t-3/2}$ | `CarryAutomaton/FocusedExtensions.lean`: `M_rel_group_circulant`, `K_coreRel_group_circulant`, `rank_K_coreMat_char_ne_two`, `rank_M_mat_char_ne_two`, `rank_K_coreMat_char_two`, `rank_K_coreMat_char_two_choose`, `rank_M_mat_char_two`; `CarryAutomaton/NegacyclicSpectrum.lean`: `walsh_conj_K_coreMat`, `D_sign_conj_Htilde_eq_G_alpha_int`, `spectralNorm2_H_alpha_eq_envelope_iff`, `centeredSpectralGap_K_core` |
| **Proposition 4.2 & Remark 4.3** — Embedded $\mathrm{DISJ}_s$ submatrix, explicit $8s - 4 \le 8s$ zero-rectangle cover, signed margin witness ($\gamma_2(S) \le 16s + 1$), & centered spectral cover inequality | `CarryAutomaton/FocusedExtensions.lean`: `disj_embedded_in_K_coreRel`, `zero_cover_K_coreRel_card_le_eight_s`, `margin_witness_K_coreRel`; `CarryAutomaton/NegacyclicSpectrum.lean`: `centered_spectral_biclique_cover_div_le`, `K_coreRel_spectral_avg_degree_lower_bound` |

---

## License

Released under the [MIT License](LICENSE) — Copyright (c) 2026 Gemini & Opus & GPT Pro.
