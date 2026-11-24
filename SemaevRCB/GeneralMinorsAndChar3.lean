module

public import SemaevRCB.RCBDichotomy
import Mathlib.Tactic

@[expose] public section

/-!
# General-`m` Shared-Input Cross Products, Characteristic-`3` Dichotomy, and Non-Hesse Frames

Extensions to `SemaevRCB` formalizing:
1. Exact rank and formal border rank `5` of the single Levi-Civita tensor `ε₃` over every field `K`
   with `char K ≠ 2` (`eps3_borderRank_ge_five`, `eps3_exact_rank_and_borderRank_five`).
2. Explicit identification of `(2 : K)⁻¹ • symEps3 K` with the simultaneous quadratic forms of the
   three `2 × 2` maximal minors of a generic `2 × 3` matrix (`minors2x3_eval`).
3. Characteristic-`3` rank-`9` obstruction (`I2_eps3_rank_nine_imp_char_ne_three`), primitive cube
   root of unity criterion, and the all-characteristic (`char K ≠ 2`, including `char K = 3`)
   rank dichotomy `9` vs. `10` (`minors2x3_all_char_dichotomy`, `rcb_minors_char3_corollary`).
4. General-`m` shared-input cross-product hierarchy `T_m = I_m ⊗₁,₂ ε₃` (`Im_eps3`): determinant
   `(-2)^m` of the `9m × 9m` Koszul flattening, exact formal border rank `⌈9m / 2⌉` over every
   field with `char K ≠ 2` (`Im_eps3_exact_formalBorderRank`), and exact split-field tensor rank
   `⌈9m / 2⌉` when `K` has a primitive cube root of unity (`Im_eps3_exact_rank_of_primCubeRoot`).
5. Explicit non-Hesse `9`-element rank-`1` idempotent solution to the equiangular trace-frame
   system `Tr(Q_r Q_s) = (3/4) δ_{rs} + 1/4` with exactly `3` collinear point triples instead of
   `12` (`nonHesse_equiangular_idempotents`).
-/

namespace SemaevRCB

open Matrix Polynomial BigOperators

/-! ## Section 1: Exact Rank and Formal Border Rank `5` of `ε₃` (`m = 1`) -/

/-- Coefficient array of the `9 × 9` single-copy Koszul flattening `Φ : Mat₃(K) → Mat₃(K)` on
`K³ ⊗ K³ ⊗ K³`. -/
def koszulCoeff1 (K : Type*) [CommRing K] :
    Idx9 → Idx9 → Fin 3 → Fin 3 → Fin 3 → K :=
  fun row col i j k =>
    if i = col.1 ∧ j = row.1 then eps3 K k col.2 row.2 else 0

lemma koszulFlat1_apply {K R : Type*} [CommRing K] [CommRing R]
    (φ : K →+* R) (T : Tensor3 R (Fin 3) (Fin 3) (Fin 3)) (row col : Idx9) :
    linearFlattening φ (koszulCoeff1 K) T row col =
      ∑ k : Fin 3, φ (eps3 K k col.2 row.2) * T col.1 row.1 k := by
  simp only [linearFlattening, koszulCoeff1]
  have hinner : ∀ i j : Fin 3,
      (∑ k : Fin 3,
        φ (if i = col.1 ∧ j = row.1 then eps3 K k col.2 row.2 else 0) * T i j k) =
      if i = col.1 ∧ j = row.1 then
        ∑ k : Fin 3, φ (eps3 K k col.2 row.2) * T i j k
      else 0 := by
    intro i j
    split_ifs <;> simp
  simp_rw [hinner]
  simp [ite_and]

/-- Every pure tensor `u ⊗ v ⊗ w` over any field `F` maps under the single-copy `9 × 9` Koszul
flattening to a matrix of rank at most `2`. -/
theorem koszul1_rankOne_le_two {K F : Type*} [CommRing K] [Field F]
    (φ : K →+* F) (u v w : Fin 3 → F) :
    (linearFlattening φ (koszulCoeff1 K) (rankOneTensor u v w)).rank ≤ 2 := by
  by_cases hw : w = 0
  · have hzero : linearFlattening φ (koszulCoeff1 K) (rankOneTensor u v w) = 0 := by
      ext row col
      rw [koszulFlat1_apply]
      simp [rankOneTensor, hw]
    rw [hzero, Matrix.rank_zero]
    omega
  · obtain ⟨b₀, b₁, c₀, c₁, _, _, _, _, _, _, _, hspan⟩ := exists_perp_basis_of_ne_zero hw
    let A : Matrix Idx9 (Fin 2) F := Matrix.of fun row t =>
      v row.1 * (if t = 0 then b₀ row.2 else b₁ row.2)
    let B : Matrix (Fin 2) Idx9 F := Matrix.of fun t col =>
      u col.1 *
        (if t = 0 then c₀ (cross3 w (stdBasis3 col.2))
         else c₁ (cross3 w (stdBasis3 col.2)))
    have hfac : linearFlattening φ (koszulCoeff1 K) (rankOneTensor u v w) = A * B := by
      ext row col
      rw [koszulFlat1_apply, Matrix.mul_apply]
      simp only [Fin.sum_univ_two, A, B, Matrix.of_apply, Fin.isValue, ↓reduceIte, one_ne_zero]
      have hcr_perp : dot3 w (cross3 w (stdBasis3 col.2)) = 0 :=
        dot3_cross3_self_left w (stdBasis3 col.2)
      have hdecomp := congrFun (hspan (cross3 w (stdBasis3 col.2)) hcr_perp) row.2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hdecomp
      calc ∑ k : Fin 3, φ (eps3 K k col.2 row.2) * rankOneTensor u v w col.1 row.1 k
          = u col.1 * v row.1 * ∑ k : Fin 3, eps3 F k col.2 row.2 * w k := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun k _ => ?_
              simp only [map_eps3, rankOneTensor]
              ring
        _ = u col.1 * v row.1 * cross3 w (stdBasis3 col.2) row.2 := by
              rw [sum_eps3_mul_eq_cross3_stdBasis]
        _ = v row.1 * b₀ row.2 * (u col.1 * c₀ (cross3 w (stdBasis3 col.2))) +
            v row.1 * b₁ row.2 * (u col.1 * c₁ (cross3 w (stdBasis3 col.2))) := by
              rw [hdecomp]; ring
    rw [hfac]
    exact le_trans (matrix_rank_mul_right_le A B)
      (by simpa using matrix_rank_le_card_col A)

lemma koszulFlat1_eps3_eq {K : Type*} [CommRing K] :
    linearFlattening (RingHom.id K) (koszulCoeff1 K) (eps3 K) = koszulPhi9 K := by
  ext ⟨j, l⟩ ⟨i, m⟩
  rw [koszulFlat1_apply]
  simp only [RingHom.id_apply, koszulPhi9]
  fin_cases j <;> fin_cases l <;> fin_cases i <;> fin_cases m <;>
    simp [Fin.sum_univ_three, eps3]

/-- Over every field `K` with `(2 : K) ≠ 0`, `eps3 K` has formal border rank at least `5`. -/
theorem eps3_borderRank_ge_five {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) :
    (∀ r : ℕ, HasFormalBorderRankLe (eps3 K) r → 5 ≤ r) ∧
    ¬ HasFormalBorderRankLe (eps3 K) 4 := by
  have hdet : ((linearFlattening (RingHom.id K) (koszulCoeff1 K) (eps3 K)).submatrix
      id id).det ≠ 0 := by
    simpa [koszulFlat1_eps3_eq, det_koszulPhi9] using neg_ne_zero.mpr h2
  have hge : ∀ r : ℕ, HasFormalBorderRankLe (eps3 K) r → 5 ≤ r := by
    intro r hr
    have h9 := formalBorderRank_flattening_lower_bound (koszulCoeff1 K) 2
      (fun u v w => koszul1_rankOne_le_two (algebraMap K (RatFunc K)) u v w) id id hdet hr
    have hcard : Fintype.card Idx9 = 9 := by decide
    rw [hcard] at h9
    omega
  exact ⟨hge, fun h4 => absurd (hge 4 h4) (by omega)⟩

/-- Over every field `K` with `(2 : K) ≠ 0`, both the ordinary tensor rank and the formal algebraic
border rank of the `3 × 3 × 3` Levi-Civita tensor `eps3 K` are equal to `5`. -/
theorem eps3_exact_rank_and_borderRank_five {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) :
    HasTensorRankLe (eps3 K) 5 ∧
    ¬ HasTensorRankLe (eps3 K) 4 ∧
    HasFormalBorderRankLe (eps3 K) 5 ∧
    ¬ HasFormalBorderRankLe (eps3 K) 4 := by
  have hr5 := eps3_hasTensorRankLe_five h2
  have hn4_brk := (eps3_borderRank_ge_five h2).2
  exact ⟨hr5, fun hr4 => hn4_brk hr4.toFormalBorderRankLe, hr5.toFormalBorderRankLe, hn4_brk⟩

/-! ## Section 2: `symEps3` and the `2 × 2` Maximal Minors of a Generic `2 × 3` Matrix -/

/-- Over any field `K` with `(2 : K) ≠ 0`, contracting `(2 : K)⁻¹ • symEps3 K` symmetrically against
the flattened entries of a `2 × 3` matrix `M = ![![x₀, x₁, x₂], ![y₀, y₁, y₂]]` evaluates to the
three signed `2 × 2` maximal minors `[x₁ y₂ - x₂ y₁, x₂ y₀ - x₀ y₂, x₀ y₁ - x₁ y₀]`. -/
theorem minors2x3_eval {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (x₀ x₁ x₂ y₀ y₁ y₂ : K) :
    let M : Matrix (Fin 2) (Fin 3) K := ![![x₀, x₁, x₂], ![y₀, y₁, y₂]]
    (fun k : Fin 3 =>
      (2 : K)⁻¹ * ∑ p : Fin 2 × Fin 3, ∑ q : Fin 2 × Fin 3,
        M p.1 p.2 * M q.1 q.2 * symEps3 K p q k) =
      ![x₁ * y₂ - x₂ * y₁, x₂ * y₀ - x₀ * y₂, x₀ * y₁ - x₁ * y₀] ∧
    ![x₁ * y₂ - x₂ * y₁, x₂ * y₀ - x₀ * y₂, x₀ * y₁ - x₁ * y₀] =
      ![(M.submatrix id ![1, 2]).det,
        -(M.submatrix id ![0, 2]).det,
        (M.submatrix id ![0, 1]).det] := by
  intro M
  constructor
  · funext k
    fin_cases k
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
        sum_symEps3_zero (fun p => M p.1 p.2) (fun q => M q.1 q.2), M]
      simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      field_simp [h2]; ring
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
        sum_symEps3_one (fun p => M p.1 p.2) (fun q => M q.1 q.2), M]
      simp only [Fin.isValue, Matrix.cons_val]
      field_simp [h2]; ring
    · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val,
        sum_symEps3_two (fun p => M p.1 p.2) (fun q => M q.1 q.2), M]
      field_simp [h2]; ring
  · funext k
    fin_cases k <;>
      simp [M, Matrix.det_fin_two, Matrix.submatrix]

/-! ## Section 3: Characteristic-`3` Obstruction and All-Characteristic (`char K ≠ 2`) Dichotomy -/

/-- **Characteristic-`3` obstruction to rank `9`:** Over *every* field `K` with `(2 : K) ≠ 0`,
if `I₂ ⊗₁,₂ ε₃` has tensor rank at most `9`, then `(3 : K) ≠ 0`. Indeed, up to Equation (3.8)
(`β₁ × β₂ = (3/2)(β₁ᵀ G_{rr} β₂) w_r` on `w_r⊥`), only `(2 : K) ≠ 0` is used; if `(3 : K) = 0`,
`β₁ × β₂` vanishes identically on the `2`-dimensional subspace `w_0⊥`, a contradiction. -/
theorem I2_eps3_rank_nine_imp_char_ne_three {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (hr9 : HasTensorRankLe (I2_eps3 K) 9) :
    (3 : K) ≠ 0 := by
  classical
  intro h3_zero
  rcases hr9 with ⟨u, v, w, hT⟩
  let L_mat : Fin 9 → Matrix Idx18 Idx18 K := fun r =>
    linearFlattening (RingHom.id K) (koszulCoeff K) (rankOneTensor (u r) (v r) (w r))
  let P_mat : Fin 9 → Matrix Idx18 Idx18 K := fun r => L_mat r * koszulInv18 K
  have hL_sum : ∑ r : Fin 9, L_mat r =
      linearFlattening (RingHom.id K) (koszulCoeff K) (I2_eps3 K) := by
    rw [← linearFlattening_sum]
    congr 1
    funext p q k
    exact (hT p q k).symm
  have hP_sum : ∑ r : Fin 9, P_mat r = 1 := by
    dsimp [P_mat]
    rw [← Finset.sum_mul, hL_sum, koszulFlat_mul_inv18 h2]
  have hfac_all : ∀ r : Fin 9,
      ∃ (b₀ b₁ : Fin 3 → K) (c₀ c₁ : (Fin 3 → K) → K),
        dot3 (w r) b₀ = 0 ∧ dot3 (w r) b₁ = 0 ∧
        (w r = 0 → b₀ = 0 ∧ b₁ = 0) ∧
        (w r ≠ 0 → ∀ y : Fin 3 → K, dot3 (w r) y = 0 → y = c₀ y • b₀ + c₁ y • b₁) ∧
        L_mat r =
          (Matrix.of fun (row : Idx18) (t : Fin 2) =>
            v r (row.1, row.2.1) * (if t = 0 then b₀ row.2.2 else b₁ row.2.2)) *
          (Matrix.of fun (t : Fin 2) (col : Idx18) =>
            u r (col.1, col.2.1) *
              (if t = 0 then c₀ (cross3 (w r) (stdBasis3 col.2.2))
               else c₁ (cross3 (w r) (stdBasis3 col.2.2)))) :=
    fun r => koszul_rankOne_factor (RingHom.id K) (u r) (v r) (w r)
  choose b₀ b₁ c₀ c₁ _ _ hw0_zero hw_span hL_fac using hfac_all
  let A_fac : Fin 9 → Matrix Idx18 (Fin 2) K := fun r =>
    Matrix.of fun row t =>
      v r (row.1, row.2.1) * (if t = 0 then b₀ r row.2.2 else b₁ r row.2.2)
  let B_raw : Fin 9 → Matrix (Fin 2) Idx18 K := fun r =>
    Matrix.of fun t col =>
      u r (col.1, col.2.1) *
        (if t = 0 then c₀ r (cross3 (w r) (stdBasis3 col.2.2))
         else c₁ r (cross3 (w r) (stdBasis3 col.2.2)))
  let B_fac : Fin 9 → Matrix (Fin 2) Idx18 K := fun r => B_raw r * koszulInv18 K
  have hP_fac : ∀ r : Fin 9, P_mat r = A_fac r * B_fac r := by
    intro r
    dsimp [P_mat, B_fac, A_fac, B_raw]
    rw [hL_fac r, Matrix.mul_assoc]
  let A_big : Matrix Idx18 (Fin 9 × Fin 2) K := fun row rt => A_fac rt.1 row rt.2
  let B_big : Matrix (Fin 9 × Fin 2) Idx18 K := fun rt col => B_fac rt.1 rt.2 col
  have hAB_big : A_big * B_big = 1 := by
    rw [← hP_sum]
    ext row col
    rw [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hP_fac r, Matrix.mul_apply]
  let e18 : Idx18 ≃ Fin 9 × Fin 2 :=
    Fintype.equivOfCardEq (by decide : Fintype.card Idx18 = Fintype.card (Fin 9 × Fin 2))
  have hBA_big : B_big * A_big = 1 := matrix_mul_eq_one_comm_of_equiv e18 hAB_big
  have hBA_diag : ∀ r : Fin 9, B_fac r * A_fac r = 1 := by
    intro r
    ext t₁ t₂
    have hent := congrFun (congrFun hBA_big (r, t₁)) (r, t₂)
    rw [Matrix.mul_apply] at hent ⊢
    simpa [B_big, A_big, Matrix.one_apply] using hent
  have hw0_ne : w 0 ≠ 0 := by
    intro h0
    rcases hw0_zero 0 h0 with ⟨hb0_0, hb1_0⟩
    have hA0 : A_fac 0 = 0 := by
      ext row t; fin_cases t <;> simp [A_fac, hb0_0, hb1_0]
    have h1 := hBA_diag 0
    rw [hA0, Matrix.mul_zero] at h1
    exact one_ne_zero (congrFun (congrFun h1 0) 0).symm
  have hv0_ne : v 0 ≠ 0 := by
    intro h0
    have hA0 : A_fac 0 = 0 := by
      ext row t; simp [A_fac, h0]
    have h1 := hBA_diag 0
    rw [hA0, Matrix.mul_zero] at h1
    exact one_ne_zero (congrFun (congrFun h1 0) 0).symm
  have eq_I_zero : ∀ β : Fin 3 → K, dot3 (w 0) β = 0 →
      cross3 (w 0) (matM3 (u 0) (v 0) *ᵥ β) = β := by
    intro β hβ
    have hβ_eq := hw_span 0 hw0_ne β hβ
    have hvec_eq : vecTensor18 (v 0) β = A_fac 0 *ᵥ ![c₀ 0 β, c₁ 0 β] := by
      funext ⟨b, j, l⟩
      have hl := congrFun hβ_eq l
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hl
      simp only [vecTensor18, hl, Matrix.mulVec, dotProduct, Fin.sum_univ_two, A_fac,
        Matrix.of_apply, Fin.isValue, ↓reduceIte, one_ne_zero, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      ring
    have hact1 : P_mat 0 *ᵥ vecTensor18 (v 0) β = vecTensor18 (v 0) β := by
      calc P_mat 0 *ᵥ vecTensor18 (v 0) β
          = A_fac 0 *ᵥ ((B_fac 0 * A_fac 0) *ᵥ ![c₀ 0 β, c₁ 0 β]) := by
              rw [hvec_eq, hP_fac 0]
              simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
        _ = vecTensor18 (v 0) β := by rw [hBA_diag 0, Matrix.one_mulVec, ← hvec_eq]
    have hact2 : P_mat 0 *ᵥ vecTensor18 (v 0) β =
        vecTensor18 (v 0) (cross3 (w 0) (matM3 (u 0) (v 0) *ᵥ β)) :=
      koszulRankOne_mul_inv18_vecTensor (u 0) (v 0) (w 0) (v 0) β
    rw [hact2] at hact1
    have hex_v : ∃ p₀ : Fin 2 × Fin 3, v 0 p₀ ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hv0_ne (funext hall)
    rcases hex_v with ⟨⟨b₀_idx, j₀_idx⟩, hv_ne⟩
    funext l
    have hl := congrFun hact1 (b₀_idx, (j₀_idx, l))
    simp only [vecTensor18] at hl
    exact mul_left_cancel₀ hv_ne hl
  have hG00_alt : ∀ β : Fin 3 → K, dot3 (w 0) β = 0 →
      dot3 β (matG3 (u 0) (v 0) *ᵥ β) = 0 := by
    intro β hβ
    have hcr := eq_I_zero β hβ
    have horth : dot3 (matM3 (u 0) (v 0) *ᵥ β) β = 0 := by
      calc dot3 (matM3 (u 0) (v 0) *ᵥ β) β
          = dot3 (matM3 (u 0) (v 0) *ᵥ β) (cross3 (w 0) (matM3 (u 0) (v 0) *ᵥ β)) := by
              nth_rw 2 [← hcr]
        _ = 0 := by simp [dot3, cross3]; ring
    rw [dot3_comm, dot3_matM3_mulVec] at horth
    field_simp [h2] at horth
    linear_combination -horth
  have hG00_skew : ∀ β₁ β₂ : Fin 3 → K,
      dot3 (w 0) β₁ = 0 → dot3 (w 0) β₂ = 0 →
      dot3 β₂ (matG3 (u 0) (v 0) *ᵥ β₁) = -dot3 β₁ (matG3 (u 0) (v 0) *ᵥ β₂) := by
    intro β₁ β₂ h₁ h₂
    have hsum_perp : dot3 (w 0) (β₁ + β₂) = 0 := by
      rw [dot3_add_right, h₁, h₂, add_zero]
    have h0 := hG00_alt (β₁ + β₂) hsum_perp
    have h10 := hG00_alt β₁ h₁
    have h20 := hG00_alt β₂ h₂
    have hexp : dot3 (β₁ + β₂) (matG3 (u 0) (v 0) *ᵥ (β₁ + β₂)) =
        dot3 β₁ (matG3 (u 0) (v 0) *ᵥ β₁) + dot3 β₁ (matG3 (u 0) (v 0) *ᵥ β₂) +
        dot3 β₂ (matG3 (u 0) (v 0) *ᵥ β₁) + dot3 β₂ (matG3 (u 0) (v 0) *ᵥ β₂) := by
      simp only [dot3, matG3, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.add_apply]
      ring
    rw [hexp, h10, h20] at h0
    linear_combination h0
  obtain ⟨p₀, p₁, _, _, s_0, hp₀, hp₁, hs_ne, hcr_p, _, _, _⟩ :=
    exists_perp_basis_of_ne_zero hw0_ne
  have hcr_ne : cross3 p₀ p₁ ≠ 0 := by
    rw [hcr_p]
    intro h0
    have : s_0⁻¹ • (s_0 • w 0) = 0 := by rw [h0, smul_zero]
    rw [smul_smul, inv_mul_cancel₀ hs_ne, one_smul] at this
    exact hw0_ne this
  have hcr_zero : cross3 p₀ p₁ = 0 := by
    have hcr₂ := eq_I_zero p₁ hp₁
    calc cross3 p₀ p₁
        = cross3 p₀ (cross3 (w 0) (matM3 (u 0) (v 0) *ᵥ p₁)) := by
            conv_lhs => rw [← hcr₂]
      _ = (dot3 p₀ (matM3 (u 0) (v 0) *ᵥ p₁)) • w 0 -
            (dot3 p₀ (w 0)) • (matM3 (u 0) (v 0) *ᵥ p₁) := bac_cab _ _ _
      _ = ((3 * (2 : K)⁻¹) * dot3 p₀ (matG3 (u 0) (v 0) *ᵥ p₁)) • w 0 := by
            rw [dot3_comm p₀ (w 0), hp₀, zero_smul, sub_zero, dot3_matM3_mulVec,
              hG00_skew p₀ p₁ hp₀ hp₁]
            congr 1
            field_simp [h2]; ring
      _ = 0 := by rw [h3_zero, zero_mul, zero_mul, zero_smul]
  exact hcr_ne hcr_zero

/-- Over any field `K` with `(2 : K) ≠ 0`, `K` contains a primitive cube root of unity
(`ω ≠ 1` with `ω² + ω + 1 = 0`) if and only if `(3 : K) ≠ 0` and `-3` is a square in `K`.
In characteristic `3`, `ω² + ω + 1 = (ω - 1)²`, forcing `ω = 1`. -/
theorem char_ne_three_and_isSquare_neg_three_iff_primCubeRoot {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) :
    ((3 : K) ≠ 0 ∧ IsSquare (-3 : K)) ↔ ∃ ω : K, ω ≠ 1 ∧ ω ^ 2 + ω + 1 = 0 := by
  constructor
  · rintro ⟨h3, ⟨s, hs⟩⟩
    let ω : K := (-1 + s) * (2 : K)⁻¹
    have hω_quad : ω ^ 2 + ω + 1 = 0 := by
      dsimp [ω]
      field_simp [h2]
      linear_combination -hs
    refine ⟨ω, ?_, hω_quad⟩
    intro hω1
    rw [hω1] at hω_quad
    apply h3
    linear_combination hω_quad
  · rintro ⟨ω, hω1, hω⟩
    refine ⟨?_, ⟨2 * ω + 1, by linear_combination -4 * hω⟩⟩
    intro h3
    have hsq : (ω - 1) * (ω - 1) = 0 := by
      calc (ω - 1) * (ω - 1) = (ω ^ 2 + ω + 1) - 3 * ω := by ring
        _ = 0 := by rw [hω, h3, zero_mul, sub_zero]
    exact hω1 (sub_eq_zero.mp (mul_self_eq_zero.mp hsq))

/-- **All-characteristic (`char K ≠ 2`) rank dichotomy for `I₂ ⊗₁,₂ ε₃` and `symEps3`:**
Over *every* field `K` with `(2 : K) ≠ 0` (including characteristic `3`):
1. Both `I2_eps3 K` and `symEps3 K` have exact formal border rank `9`.
2. If `∃ ω : K, ω ≠ 1 ∧ ω ^ 2 + ω + 1 = 0`, both ordinary and `(1,2)`-symmetric rank equal `9`.
3. Otherwise (including all fields of characteristic `3`), both ordinary and `(1,2)`-symmetric
   rank equal `10`. -/
theorem minors2x3_all_char_dichotomy {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) :
    HasSym12FormalBorderRankLe (symEps3 K) 9 ∧
    HasFormalBorderRankLe (I2_eps3 K) 9 ∧
    ¬ HasFormalBorderRankLe (I2_eps3 K) 8 ∧
    ¬ HasFormalBorderRankLe (symEps3 K) 8 ∧
    ¬ HasTensorRankLe (I2_eps3 K) 8 ∧
    HasSym12RankLe (symEps3 K) 10 ∧
    HasTensorRankLe (I2_eps3 K) 10 ∧
    (HasTensorRankLe (I2_eps3 K) 9 ↔ ∃ ω : K, ω ≠ 1 ∧ ω ^ 2 + ω + 1 = 0) ∧
    (HasSym12RankLe (symEps3 K) 9 ↔ ∃ ω : K, ω ≠ 1 ∧ ω ^ 2 + ω + 1 = 0) ∧
    (¬ (∃ ω : K, ω ≠ 1 ∧ ω ^ 2 + ω + 1 = 0) →
      HasSym12RankLe (symEps3 K) 10 ∧
      ¬ HasTensorRankLe (I2_eps3 K) 9 ∧
      ¬ HasTensorRankLe (symEps3 K) 9 ∧
      ∀ r : ℕ, HasTensorRankLe (I2_eps3 K) r → 10 ≤ r) := by
  have heq := symEps3_equiv_I2_eps3 K
  have hbs9 := symEps3_hasSym12FormalBorderRankLe_nine h2
  have hbi9 : HasFormalBorderRankLe (I2_eps3 K) 9 :=
    (heq.hasFormalBorderRankLe_iff 9).mp hbs9.toFormalBorderRankLe
  rcases I2_eps3_borderRank_ge_nine h2 with ⟨hge9_brk, hn8_I⟩
  have hn8_sym : ¬ HasFormalBorderRankLe (symEps3 K) 8 :=
    fun h8 => hn8_I ((heq.hasFormalBorderRankLe_iff 8).mp h8)
  have hn8_rk : ¬ HasTensorRankLe (I2_eps3 K) 8 :=
    fun h8 => hn8_I h8.toFormalBorderRankLe
  have hs10 := symEps3_hasSym12RankLe_ten h2
  have hr10_I : HasTensorRankLe (I2_eps3 K) 10 :=
    (heq.hasTensorRankLe_iff 10).mp hs10.toTensorRankLe
  have hprim_iff := char_ne_three_and_isSquare_neg_three_iff_primCubeRoot h2
  have hiff_I9 : HasTensorRankLe (I2_eps3 K) 9 ↔ ∃ ω : K, ω ≠ 1 ∧ ω ^ 2 + ω + 1 = 0 := by
    rw [← hprim_iff]
    constructor
    · intro hr9
      have h3 := I2_eps3_rank_nine_imp_char_ne_three h2 hr9
      exact ⟨h3, rank_9_implies_isSquare_neg_three h2 h3 hr9⟩
    · rintro ⟨h3, hsq⟩
      exact (heq.hasTensorRankLe_iff 9).mp
        (symEps3_hasSym12RankLe_nine_of_isSquare_neg_three h2 h3 hsq).toTensorRankLe
  have hiff_sym9 : HasSym12RankLe (symEps3 K) 9 ↔ ∃ ω : K, ω ≠ 1 ∧ ω ^ 2 + ω + 1 = 0 := by
    rw [← hprim_iff]
    constructor
    · intro hs9
      have hr9 : HasTensorRankLe (I2_eps3 K) 9 :=
        (heq.hasTensorRankLe_iff 9).mp hs9.toTensorRankLe
      have h3 := I2_eps3_rank_nine_imp_char_ne_three h2 hr9
      exact ⟨h3, rank_9_implies_isSquare_neg_three h2 h3 hr9⟩
    · rintro ⟨h3, hsq⟩
      exact symEps3_hasSym12RankLe_nine_of_isSquare_neg_three h2 h3 hsq
  refine ⟨hbs9, hbi9, hn8_I, hn8_sym, hn8_rk, hs10, hr10_I, hiff_I9, hiff_sym9, ?_⟩
  intro hno_ω
  have hnot_I9 : ¬ HasTensorRankLe (I2_eps3 K) 9 := fun hr9 => hno_ω (hiff_I9.mp hr9)
  have hnot_sym9 : ¬ HasTensorRankLe (symEps3 K) 9 :=
    fun hr9 => hnot_I9 ((heq.hasTensorRankLe_iff 9).mp hr9)
  refine ⟨hs10, hnot_I9, hnot_sym9, ?_⟩
  intro r hr
  have h9le : 9 ≤ r := hge9_brk r hr.toFormalBorderRankLe
  by_contra hlt10
  have hr9_eq : r = 9 := by omega
  subst hr9_eq
  exact hnot_I9 hr

/-- **Characteristic-`3` Corollary (`CharP K 3`, e.g. `ZMod 3` or `AlgebraicClosure (ZMod 3)`):**
Over *every* field `K` of characteristic `3`, both `I2_eps3 K` and `symEps3 K` have exact ordinary
and `(1,2)`-symmetric rank `10` alongside exact formal border rank `9`. -/
theorem rcb_minors_char3_corollary (K : Type*) [Field K] [CharP K 3] :
    HasSym12RankLe (symEps3 K) 10 ∧
    HasTensorRankLe (I2_eps3 K) 10 ∧
    ¬ HasTensorRankLe (I2_eps3 K) 9 ∧
    ¬ HasTensorRankLe (symEps3 K) 9 ∧
    (∀ r : ℕ, HasTensorRankLe (I2_eps3 K) r → 10 ≤ r) ∧
    HasSym12FormalBorderRankLe (symEps3 K) 9 ∧
    HasFormalBorderRankLe (I2_eps3 K) 9 ∧
    ¬ HasFormalBorderRankLe (I2_eps3 K) 8 ∧
    ¬ HasFormalBorderRankLe (symEps3 K) 8 := by
  have h3_zero : (3 : K) = 0 := by
    simpa using (CharP.cast_eq_zero K 3)
  have h2 : (2 : K) ≠ 0 := by
    intro h2_zero
    have h1 : (1 : K) = (3 : K) - (2 : K) := by ring
    rw [h3_zero, h2_zero, sub_self] at h1
    exact one_ne_zero h1
  rcases minors2x3_all_char_dichotomy h2 with
    ⟨hbs9, hbi9, hn8_I, hn8_sym, _, _, hr10_I, _, _, hno_branch⟩
  have hno_ω : ¬ (∃ ω : K, ω ≠ 1 ∧ ω ^ 2 + ω + 1 = 0) := by
    intro hω
    exact ((char_ne_three_and_isSquare_neg_three_iff_primCubeRoot h2).mpr hω).1 h3_zero
  rcases hno_branch hno_ω with ⟨hs10, hn9_I, hn9_sym, hge10⟩
  exact ⟨hs10, hr10_I, hn9_I, hn9_sym, hge10, hbs9, hbi9, hn8_I, hn8_sym⟩

/-! ## Section 4: General-`m` Hierarchy `I_m ⊗₁,₂ ε₃` (`Im_eps3`) -/

/-- General-`m` mode-shared Levi-Civita tensor `T_m = I_m ⊗₁,₂ ε₃ ∈ (K^m ⊗ K³) ⊗ (K^m ⊗ K³) ⊗ K³`
representing `m` cross products sharing one `K³` factor. -/
def Im_eps3 (K : Type*) [CommRing K] (m : ℕ) :
    Tensor3 K (Fin m × Fin 3) (Fin m × Fin 3) (Fin 3) :=
  fun p q k => if p.1 = q.1 then eps3 K p.2 q.2 k else 0

/-- `9m`-element index type `(Fin m) × (Fin 3 × Fin 3)` for the `9m × 9m` Koszul flattening. -/
abbrev Idx9m (m : ℕ) := Fin m × Idx9

/-- Coefficient array of the `9m × 9m` Koszul flattening on `(K^m ⊗ K³) ⊗ (K^m ⊗ K³) ⊗ K³`. -/
def koszulCoeffM (K : Type*) [CommRing K] (m : ℕ) :
    Idx9m m → Idx9m m → (Fin m × Fin 3) → (Fin m × Fin 3) → Fin 3 → K :=
  fun row col p q k =>
    if p = (col.1, col.2.1) ∧ q = (row.1, row.2.1) then eps3 K k col.2.2 row.2.2 else 0

lemma koszulFlatM_apply {K R : Type*} [CommRing K] [CommRing R] {m : ℕ}
    (φ : K →+* R) (T : Tensor3 R (Fin m × Fin 3) (Fin m × Fin 3) (Fin 3))
    (row col : Idx9m m) :
    linearFlattening φ (koszulCoeffM K m) T row col =
      ∑ k : Fin 3, φ (eps3 K k col.2.2 row.2.2) * T (col.1, col.2.1) (row.1, row.2.1) k := by
  simp only [linearFlattening, koszulCoeffM]
  have hinner : ∀ p q : Fin m × Fin 3,
      (∑ k : Fin 3,
        φ (if p = (col.1, col.2.1) ∧ q = (row.1, row.2.1) then eps3 K k col.2.2 row.2.2 else 0) *
          T p q k) =
      if p = (col.1, col.2.1) ∧ q = (row.1, row.2.1) then
        ∑ k : Fin 3, φ (eps3 K k col.2.2 row.2.2) * T p q k
      else 0 := by
    intro p q
    split_ifs <;> simp
  simp_rw [hinner]
  simp [ite_and]

/-- Every pure tensor `u ⊗ v ⊗ w` over any field `F` maps under the `9m × 9m` Koszul flattening
to a matrix of rank at most `2`. -/
theorem koszulM_rankOne_le_two {K F : Type*} [CommRing K] [Field F] (m : ℕ)
    (φ : K →+* F) (u v : Fin m × Fin 3 → F) (w : Fin 3 → F) :
    (linearFlattening φ (koszulCoeffM K m) (rankOneTensor u v w)).rank ≤ 2 := by
  by_cases hw : w = 0
  · have hzero : linearFlattening φ (koszulCoeffM K m) (rankOneTensor u v w) = 0 := by
      ext row col
      rw [koszulFlatM_apply]
      simp [rankOneTensor, hw]
    rw [hzero, Matrix.rank_zero]
    omega
  · obtain ⟨b₀, b₁, c₀, c₁, _, _, _, _, _, _, _, hspan⟩ := exists_perp_basis_of_ne_zero hw
    let A : Matrix (Idx9m m) (Fin 2) F := Matrix.of fun row t =>
      v (row.1, row.2.1) * (if t = 0 then b₀ row.2.2 else b₁ row.2.2)
    let B : Matrix (Fin 2) (Idx9m m) F := Matrix.of fun t col =>
      u (col.1, col.2.1) *
        (if t = 0 then c₀ (cross3 w (stdBasis3 col.2.2))
         else c₁ (cross3 w (stdBasis3 col.2.2)))
    have hfac : linearFlattening φ (koszulCoeffM K m) (rankOneTensor u v w) = A * B := by
      ext row col
      rw [koszulFlatM_apply, Matrix.mul_apply]
      simp only [Fin.sum_univ_two, A, B, Matrix.of_apply, Fin.isValue, ↓reduceIte, one_ne_zero]
      have hcr_perp : dot3 w (cross3 w (stdBasis3 col.2.2)) = 0 :=
        dot3_cross3_self_left w (stdBasis3 col.2.2)
      have hdecomp := congrFun (hspan (cross3 w (stdBasis3 col.2.2)) hcr_perp) row.2.2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hdecomp
      calc ∑ k : Fin 3, φ (eps3 K k col.2.2 row.2.2) *
              rankOneTensor u v w (col.1, col.2.1) (row.1, row.2.1) k
          = u (col.1, col.2.1) * v (row.1, row.2.1) *
              ∑ k : Fin 3, eps3 F k col.2.2 row.2.2 * w k := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun k _ => ?_
              simp only [map_eps3, rankOneTensor]
              ring
        _ = u (col.1, col.2.1) * v (row.1, row.2.1) *
              cross3 w (stdBasis3 col.2.2) row.2.2 := by
              rw [sum_eps3_mul_eq_cross3_stdBasis]
        _ = v (row.1, row.2.1) * b₀ row.2.2 *
              (u (col.1, col.2.1) * c₀ (cross3 w (stdBasis3 col.2.2))) +
            v (row.1, row.2.1) * b₁ row.2.2 *
              (u (col.1, col.2.1) * c₁ (cross3 w (stdBasis3 col.2.2))) := by
              rw [hdecomp]; ring
    rw [hfac]
    exact le_trans (matrix_rank_mul_right_le A B)
      (by simpa using matrix_rank_le_card_col A)

/-- `m`-fold block-diagonal lift `I_m ⊗ M` of a square matrix `M`. -/
def blockDiagM {K α : Type*} [Zero K] (m : ℕ) (M : Matrix α α K) :
    Matrix (Fin m × α) (Fin m × α) K :=
  fun row col => if row.1 = col.1 then M row.2 col.2 else 0

lemma det_blockDiagM {K α : Type*} [CommRing K] [Fintype α] [DecidableEq α]
    (m : ℕ) (M : Matrix α α K) :
    (blockDiagM m M).det = M.det ^ m := by
  induction m with
  | zero =>
    have : IsEmpty (Fin 0 × α) := ⟨fun p => Fin.elim0 p.1⟩
    simp [Matrix.det_isEmpty]
  | succ m ih =>
    let e : α ⊕ (Fin m × α) ≃ (Fin (m + 1) × α) :=
      { toFun := fun s => match s with
          | .inl x => (0, x)
          | .inr p => (p.1.succ, p.2)
        invFun := fun p => Fin.cases (.inl p.2) (fun i => .inr (i, p.2)) p.1
        left_inv := fun s => by rcases s with x | ⟨i, x⟩ <;> simp
        right_inv := fun ⟨i, x⟩ => by refine Fin.cases ?_ (fun j => ?_) i <;> simp }
    rw [← Matrix.det_reindex_self e.symm (blockDiagM (m + 1) M)]
    have hblk : Matrix.reindex e.symm e.symm (blockDiagM (m + 1) M) =
        Matrix.fromBlocks M 0 0 (blockDiagM m M) := by
      ext x y
      change blockDiagM (m + 1) M (e x) (e y) =
        Matrix.fromBlocks M 0 0 (blockDiagM m M) x y
      rcases x with x | ⟨i, x⟩ <;> rcases y with y | ⟨j, y⟩
      · simp [e, blockDiagM, Matrix.fromBlocks]
      · simp [e, blockDiagM, Matrix.fromBlocks, (Fin.succ_ne_zero j).symm]
      · simp [e, blockDiagM, Matrix.fromBlocks, Fin.succ_ne_zero i]
      · simp [e, blockDiagM, Matrix.fromBlocks, Fin.succ_inj]
    rw [hblk, Matrix.det_fromBlocks_zero₂₁, ih, pow_succ']

lemma koszulFlatM_Im_eps3_eq {K : Type*} [CommRing K] (m : ℕ) :
    linearFlattening (RingHom.id K) (koszulCoeffM K m) (Im_eps3 K m) =
      blockDiagM m (koszulPhi9 K) := by
  ext ⟨b, j, l⟩ ⟨a, i, m_idx⟩
  rw [koszulFlatM_apply]
  simp only [RingHom.id_apply, Im_eps3, blockDiagM]
  by_cases hab : a = b
  · subst hab
    simp only [↓reduceIte, koszulPhi9]
    fin_cases j <;> fin_cases l <;> fin_cases i <;> fin_cases m_idx <;>
      simp [Fin.sum_univ_three, eps3]
  · have hba : b ≠ a := Ne.symm hab
    simp [hab, hba]

/-- Over every commutative ring `K` and every `m : ℕ`, the `9m × 9m` Koszul flattening of
`Im_eps3 K m` has determinant `(-2 : K) ^ m`. -/
theorem det_koszulFlat_Im_eps3 (K : Type*) [CommRing K] (m : ℕ) :
    (linearFlattening (RingHom.id K) (koszulCoeffM K m) (Im_eps3 K m)).det = (-2 : K) ^ m := by
  rw [koszulFlatM_Im_eps3_eq, det_blockDiagM, det_koszulPhi9]

/-- Koszul formal border-rank lower bound `(9 * m + 1) / 2 ≤ r` for `Im_eps3 K m` over any field
`K` with `(2 : K) ≠ 0` and all `m : ℕ`. -/
theorem Im_eps3_borderRank_ge {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) (m : ℕ) :
    ∀ r : ℕ, HasFormalBorderRankLe (Im_eps3 K m) r → (9 * m + 1) / 2 ≤ r := by
  intro r hr
  have hdet : ((linearFlattening (RingHom.id K) (koszulCoeffM K m) (Im_eps3 K m)).submatrix
      id id).det ≠ 0 := by
    simpa [det_koszulFlat_Im_eps3] using pow_ne_zero m (neg_ne_zero.mpr h2)
  have h9m := formalBorderRank_flattening_lower_bound (koszulCoeffM K m) 2
    (fun u v w => koszulM_rankOne_le_two m (algebraMap K (RatFunc K)) u v w) id id hdet hr
  have hcard : Fintype.card (Idx9m m) = m * 9 := by
    rw [Fintype.card_prod, Fintype.card_fin]
    have h9 : Fintype.card Idx9 = 9 := by decide
    rw [h9]
  rw [hcard] at h9m
  omega

lemma Im_eps3_zero_hasTensorRankLe (K : Type*) [CommRing K] :
    HasTensorRankLe (Im_eps3 K 0) 0 :=
  ⟨fun t => Fin.elim0 t, fun t => Fin.elim0 t, fun t => Fin.elim0 t, fun p _ _ => Fin.elim0 p.1⟩

lemma Im_eps3_one_hasTensorRankLe {K : Type*} [CommRing K] {r : ℕ}
    (hr : HasTensorRankLe (eps3 K) r) :
    HasTensorRankLe (Im_eps3 K 1) r := by
  rcases hr with ⟨u, v, w, hT⟩
  refine ⟨fun t p => u t p.2, fun t q => v t q.2, w, fun p q k => ?_⟩
  have hpq : p.1 = q.1 := Subsingleton.elim p.1 q.1
  simp [Im_eps3, hpq, hT p.2 q.2 k]

lemma Im_eps3_add_hasTensorRankLe {K : Type*} [CommRing K] {m₁ m₂ r₁ r₂ : ℕ}
    (h₁ : HasTensorRankLe (Im_eps3 K m₁) r₁)
    (h₂ : HasTensorRankLe (Im_eps3 K m₂) r₂) :
    HasTensorRankLe (Im_eps3 K (m₁ + m₂)) (r₁ + r₂) := by
  rcases h₁ with ⟨u₁, v₁, w₁, hT₁⟩
  rcases h₂ with ⟨u₂, v₂, w₂, hT₂⟩
  let u : Fin (r₁ + r₂) → Fin (m₁ + m₂) × Fin 3 → K :=
    Fin.addCases
      (fun t₁ p => if ha : p.1.val < m₁ then u₁ t₁ (⟨p.1.val, ha⟩, p.2) else 0)
      (fun t₂ p => if ha : p.1.val < m₁ then 0 else u₂ t₂ (⟨p.1.val - m₁, by omega⟩, p.2))
  let v : Fin (r₁ + r₂) → Fin (m₁ + m₂) × Fin 3 → K :=
    Fin.addCases
      (fun t₁ q => if hb : q.1.val < m₁ then v₁ t₁ (⟨q.1.val, hb⟩, q.2) else 0)
      (fun t₂ q => if hb : q.1.val < m₁ then 0 else v₂ t₂ (⟨q.1.val - m₁, by omega⟩, q.2))
  let w : Fin (r₁ + r₂) → Fin 3 → K := Fin.addCases w₁ w₂
  refine ⟨u, v, w, fun p q k => ?_⟩
  rw [Fin.sum_univ_add]
  simp only [u, v, w, Fin.addCases_left, Fin.addCases_right]
  by_cases ha : p.1.val < m₁ <;> by_cases hb : q.1.val < m₁
  · simp only [ha, hb, ↓reduceDIte, zero_mul, Finset.sum_const_zero, add_zero]
    rw [← hT₁ (⟨p.1.val, ha⟩, p.2) (⟨q.1.val, hb⟩, q.2) k]
    have heq : ((⟨p.1.val, ha⟩ : Fin m₁) = ⟨q.1.val, hb⟩) ↔ p.1 = q.1 := by
      simp [Fin.ext_iff]
    simp [Im_eps3, heq]
  · have hpq : p.1 ≠ q.1 := by intro h; rw [h] at ha; exact hb ha
    simp [ha, hb, Im_eps3, hpq]
  · have hpq : p.1 ≠ q.1 := by intro h; rw [← h] at hb; exact ha hb
    simp [ha, hb, Im_eps3, hpq]
  · simp only [ha, hb, ↓reduceDIte, zero_mul, Finset.sum_const_zero, zero_add]
    rw [← hT₂ (⟨p.1.val - m₁, by omega⟩, p.2) (⟨q.1.val - m₁, by omega⟩, q.2) k]
    have heq : ((⟨p.1.val - m₁, by omega⟩ : Fin m₂) = ⟨q.1.val - m₁, by omega⟩) ↔ p.1 = q.1 := by
      constructor <;> intro h <;> ext <;> simp [Fin.ext_iff] at h ⊢ <;> omega
    simp [Im_eps3, heq]

lemma Im_eps3_add_hasFormalBorderRankLe {K : Type*} [CommRing K] {m₁ m₂ r₁ r₂ : ℕ}
    (h₁ : HasFormalBorderRankLe (Im_eps3 K m₁) r₁)
    (h₂ : HasFormalBorderRankLe (Im_eps3 K m₂) r₂) :
    HasFormalBorderRankLe (Im_eps3 K (m₁ + m₂)) (r₁ + r₂) := by
  rcases h₁ with ⟨d₁, U₁, V₁, W₁, E₁, hT₁⟩
  rcases h₂ with ⟨d₂, U₂, V₂, W₂, E₂, hT₂⟩
  let U : Fin (r₁ + r₂) → Fin (m₁ + m₂) × Fin 3 → K[X] :=
    Fin.addCases
      (fun t₁ p => if ha : p.1.val < m₁ then U₁ t₁ (⟨p.1.val, ha⟩, p.2) else 0)
      (fun t₂ p => if ha : p.1.val < m₁ then 0 else U₂ t₂ (⟨p.1.val - m₁, by omega⟩, p.2))
  let V : Fin (r₁ + r₂) → Fin (m₁ + m₂) × Fin 3 → K[X] :=
    Fin.addCases
      (fun t₁ q => if hb : q.1.val < m₁ then V₁ t₁ (⟨q.1.val, hb⟩, q.2) else 0)
      (fun t₂ q => if hb : q.1.val < m₁ then 0 else V₂ t₂ (⟨q.1.val - m₁, by omega⟩, q.2))
  let W : Fin (r₁ + r₂) → Fin 3 → K[X] :=
    Fin.addCases (fun t₁ k => W₁ t₁ k * X ^ d₂) (fun t₂ k => W₂ t₂ k * X ^ d₁)
  let E : Fin (m₁ + m₂) × Fin 3 → Fin (m₁ + m₂) × Fin 3 → Fin 3 → K[X] := fun p q k =>
    if ha : p.1.val < m₁ then
      if hb : q.1.val < m₁ then E₁ (⟨p.1.val, ha⟩, p.2) (⟨q.1.val, hb⟩, q.2) k else 0
    else
      if hb : q.1.val < m₁ then 0
      else E₂ (⟨p.1.val - m₁, by omega⟩, p.2) (⟨q.1.val - m₁, by omega⟩, q.2) k
  refine ⟨d₁ + d₂, U, V, W, E, fun p q k => ?_⟩
  rw [Fin.sum_univ_add]
  simp only [U, V, W, E, Fin.addCases_left, Fin.addCases_right]
  by_cases ha : p.1.val < m₁ <;> by_cases hb : q.1.val < m₁
  · simp only [ha, hb, ↓reduceDIte, zero_mul, Finset.sum_const_zero, add_zero]
    have hmul : (∑ x : Fin r₁,
        U₁ x (⟨p.1.val, ha⟩, p.2) * V₁ x (⟨q.1.val, hb⟩, q.2) * (W₁ x k * X ^ d₂)) =
        (∑ x : Fin r₁,
          U₁ x (⟨p.1.val, ha⟩, p.2) * V₁ x (⟨q.1.val, hb⟩, q.2) * W₁ x k) * X ^ d₂ := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [hmul, hT₁ (⟨p.1.val, ha⟩, p.2) (⟨q.1.val, hb⟩, q.2) k]
    have heq : ((⟨p.1.val, ha⟩ : Fin m₁) = ⟨q.1.val, hb⟩) ↔ p.1 = q.1 := by
      simp [Fin.ext_iff]
    simp only [Im_eps3, heq, pow_add]
    ring
  · have hpq : p.1 ≠ q.1 := by intro h; rw [h] at ha; exact hb ha
    simp [ha, hb, Im_eps3, hpq]
  · have hpq : p.1 ≠ q.1 := by intro h; rw [← h] at hb; exact ha hb
    simp [ha, hb, Im_eps3, hpq]
  · simp only [ha, hb, ↓reduceDIte, zero_mul, Finset.sum_const_zero, zero_add]
    have hmul : (∑ x : Fin r₂,
        U₂ x (⟨p.1.val - m₁, by omega⟩, p.2) * V₂ x (⟨q.1.val - m₁, by omega⟩, q.2) *
          (W₂ x k * X ^ d₁)) =
        (∑ x : Fin r₂,
          U₂ x (⟨p.1.val - m₁, by omega⟩, p.2) * V₂ x (⟨q.1.val - m₁, by omega⟩, q.2) *
            W₂ x k) * X ^ d₁ := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [hmul, hT₂ (⟨p.1.val - m₁, by omega⟩, p.2) (⟨q.1.val - m₁, by omega⟩, q.2) k]
    have heq : ((⟨p.1.val - m₁, by omega⟩ : Fin m₂) = ⟨q.1.val - m₁, by omega⟩) ↔ p.1 = q.1 := by
      constructor <;> intro h <;> ext <;> simp [Fin.ext_iff] at h ⊢ <;> omega
    simp only [Im_eps3, heq, pow_add]
    ring

lemma Im_eps3_hasFormalBorderRankLe_all {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) :
    ∀ m : ℕ, HasFormalBorderRankLe (Im_eps3 K m) ((9 * m + 1) / 2)
  | 0 => (Im_eps3_zero_hasTensorRankLe K).toFormalBorderRankLe
  | 1 => (Im_eps3_one_hasTensorRankLe (eps3_hasTensorRankLe_five h2)).toFormalBorderRankLe
  | m + 2 => by
      have hm := Im_eps3_hasFormalBorderRankLe_all h2 m
      have h2_copy : HasFormalBorderRankLe (Im_eps3 K 2) 9 :=
        ((symEps3_equiv_I2_eps3 K).hasFormalBorderRankLe_iff 9).mp
          (symEps3_hasSym12FormalBorderRankLe_nine h2).toFormalBorderRankLe
      have hsum := Im_eps3_add_hasFormalBorderRankLe hm h2_copy
      have harith : (9 * m + 1) / 2 + 9 = (9 * (m + 2) + 1) / 2 := by omega
      rwa [harith] at hsum

lemma Im_eps3_hasTensorRankLe_of_primCubeRoot_all {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (hω : ∃ ω : K, ω ≠ 1 ∧ ω ^ 2 + ω + 1 = 0) :
    ∀ m : ℕ, HasTensorRankLe (Im_eps3 K m) ((9 * m + 1) / 2)
  | 0 => Im_eps3_zero_hasTensorRankLe K
  | 1 => Im_eps3_one_hasTensorRankLe (eps3_hasTensorRankLe_five h2)
  | m + 2 => by
      have hm := Im_eps3_hasTensorRankLe_of_primCubeRoot_all h2 hω m
      have h2_copy : HasTensorRankLe (Im_eps3 K 2) 9 :=
        ((minors2x3_all_char_dichotomy h2).2.2.2.2.2.2.2.1).mpr hω
      have hsum := Im_eps3_add_hasTensorRankLe hm h2_copy
      have harith : (9 * m + 1) / 2 + 9 = (9 * (m + 2) + 1) / 2 := by omega
      rwa [harith] at hsum

/-- Over every field `K` with `(2 : K) ≠ 0` and every `m ≥ 1`, the formal algebraic border rank of
`Im_eps3 K m` equals `(9 * m + 1) / 2 = ⌈9m / 2⌉` (attained via `m / 2` copies of the `9`-term
degeneration of `I₂ ⊗₁,₂ ε₃` plus `m % 2` copy of the `5`-term decomposition of `ε₃`, where
`9 * (m / 2) + 5 * (m % 2) = (9 * m + 1) / 2`). -/
theorem Im_eps3_exact_formalBorderRank {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {m : ℕ} (hm : 1 ≤ m) :
    HasFormalBorderRankLe (Im_eps3 K m) ((9 * m + 1) / 2) ∧
    (∀ r : ℕ, HasFormalBorderRankLe (Im_eps3 K m) r → (9 * m + 1) / 2 ≤ r) ∧
    ¬ HasFormalBorderRankLe (Im_eps3 K m) ((9 * m + 1) / 2 - 1) ∧
    9 * (m / 2) + 5 * (m % 2) = (9 * m + 1) / 2 := by
  have hge := Im_eps3_borderRank_ge h2 m
  refine ⟨Im_eps3_hasFormalBorderRankLe_all h2 m, hge, ?_, by omega⟩
  intro hlt
  have hle := hge ((9 * m + 1) / 2 - 1) hlt
  omega

/-- Over every field `K` with `(2 : K) ≠ 0` containing a primitive cube root of unity
(`∃ ω : K, ω ≠ 1 ∧ ω ^ 2 + ω + 1 = 0`), for every `m ≥ 1`, the ordinary tensor rank of
`Im_eps3 K m` equals `(9 * m + 1) / 2 = ⌈9m / 2⌉`. -/
theorem Im_eps3_exact_rank_of_primCubeRoot {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (hω : ∃ ω : K, ω ≠ 1 ∧ ω ^ 2 + ω + 1 = 0) {m : ℕ} (hm : 1 ≤ m) :
    HasTensorRankLe (Im_eps3 K m) ((9 * m + 1) / 2) ∧
    (∀ r : ℕ, HasTensorRankLe (Im_eps3 K m) r → (9 * m + 1) / 2 ≤ r) ∧
    ¬ HasTensorRankLe (Im_eps3 K m) ((9 * m + 1) / 2 - 1) := by
  have hge_brk := Im_eps3_borderRank_ge h2 m
  have hge_rk : ∀ r : ℕ, HasTensorRankLe (Im_eps3 K m) r → (9 * m + 1) / 2 ≤ r :=
    fun r hr => hge_brk r hr.toFormalBorderRankLe
  refine ⟨Im_eps3_hasTensorRankLe_of_primCubeRoot_all h2 hω m, hge_rk, ?_⟩
  intro hlt
  have hle := hge_rk ((9 * m + 1) / 2 - 1) hlt
  omega

/-! ## Section 5: Non-Hesse Equiangular Rank-`1` Idempotent Counterexample -/

/-- Vectors `x_{j, t} ∈ K³` at `(a, b, c) = (2, 1, 1)` for `j, t ∈ Fin 3`:
`x_{0, t} = (0, 1, 2 ω^t)`, `x_{1, t} = (ω^t, 0, 1)`, `x_{2, t} = (1, ω^t, 0)`. -/
def nonHesseVecX {K : Type*} [CommRing K] (ω : K) : Idx9 → Fin 3 → K
  | (0, t) => ![0, 1, 2 * ω ^ t.val]
  | (1, t) => ![ω ^ t.val, 0, 1]
  | (2, t) => ![1, ω ^ t.val, 0]

/-- Dual covectors `y_{j, t} ∈ K³` at `(a, b, c) = (2, 1, 1)` for `j, t ∈ Fin 3`:
`y_{0, t} = (0, 1/2, (1/4) ω^{2t})`, `y_{1, t} = ((1/2) ω^{2t}, 0, 1/2)`,
`y_{2, t} = (1/2, (1/2) ω^{2t}, 0)`. -/
def nonHesseVecY {K : Type*} [Field K] (ω : K) : Idx9 → Fin 3 → K
  | (0, t) => ![0, (2 : K)⁻¹, (4 : K)⁻¹ * ω ^ (2 * t.val)]
  | (1, t) => ![(2 : K)⁻¹ * ω ^ (2 * t.val), 0, (2 : K)⁻¹]
  | (2, t) => ![(2 : K)⁻¹, (2 : K)⁻¹ * ω ^ (2 * t.val), 0]

/-- Rank-`1` matrices `Q_{j, t} = x_{j, t} y_{j, t}ᵀ ∈ Mat₃(K)` at `(a, b, c) = (2, 1, 1)`. -/
def nonHesseIdempotent {K : Type*} [Field K] (ω : K) (p : Idx9) : Matrix (Fin 3) (Fin 3) K :=
  fun i k => nonHesseVecX ω p i * nonHesseVecY ω p k

/-- A `3`-element subset `S` of indices is collinear under `x` if all `3 × 3` determinants formed
by rows from `S` vanish. -/
def IsCollinearTriple {K ι : Type*} [CommRing K] (x : ι → Fin 3 → K) (S : Finset ι) : Prop :=
  S.card = 3 ∧ ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, (Matrix.of ![x p, x q, x r]).det = 0

lemma omega_cube_eq_one {K : Type*} [CommRing K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    ω ^ 3 = 1 := by
  linear_combination (ω - 1) * hω

lemma omega_ne_zero_of_quad {K : Type*} [Field K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    ω ≠ 0 := by
  intro h0
  rw [h0] at hω
  norm_num at hω

lemma omega_ne_one_of_quad {K : Type*} [Field K] (h3 : (3 : K) ≠ 0)
    {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    ω ≠ 1 := by
  intro h1
  rw [h1] at hω
  apply h3
  linear_combination hω

lemma omega_pow_sub_ne_zero {K : Type*} [Field K] (h3 : (3 : K) ≠ 0)
    {ω : K} (hω : ω ^ 2 + ω + 1 = 0) {t₁ t₂ : Fin 3} (ht : t₁ ≠ t₂) :
    ω ^ t₁.val - ω ^ t₂.val ≠ 0 := by
  have h0 := omega_ne_zero_of_quad hω
  have h1 := omega_ne_one_of_quad h3 hω
  fin_cases t₁ <;> fin_cases t₂
  · exact absurd rfl ht
  · change ω ^ 0 - ω ^ 1 ≠ 0
    simp only [pow_zero, pow_one]
    exact sub_ne_zero.mpr h1.symm
  · change ω ^ 0 - ω ^ 2 ≠ 0
    rw [pow_zero]
    intro h
    apply h3
    linear_combination -((ω - 2) * hω + (ω - 1) * h)
  · change ω ^ 1 - ω ^ 0 ≠ 0
    simp only [pow_one, pow_zero]
    exact sub_ne_zero.mpr h1
  · exact absurd rfl ht
  · change ω ^ 1 - ω ^ 2 ≠ 0
    rw [pow_one]
    intro h
    have hfac : ω * (1 - ω) = 0 := by linear_combination h
    exact mul_ne_zero h0 (sub_ne_zero.mpr h1.symm) hfac
  · change ω ^ 2 - ω ^ 0 ≠ 0
    rw [pow_zero]
    intro h
    apply h3
    linear_combination -((ω - 2) * hω - (ω - 1) * h)
  · change ω ^ 2 - ω ^ 1 ≠ 0
    rw [pow_one]
    intro h
    have hfac : ω * (ω - 1) = 0 := by linear_combination h
    exact mul_ne_zero h0 (sub_ne_zero.mpr h1) hfac
  · exact absurd rfl ht

lemma two_mul_omega_pow_add_one_ne_zero {K : Type*} [Field K] (h3 : (3 : K) ≠ 0)
    {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (k : ℕ) :
    2 * ω ^ k + 1 ≠ 0 := by
  intro hz
  have hc : (ω ^ k) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, omega_cube_eq_one hω, one_pow]
  have h9 : (9 : K) = 0 := by
    calc (9 : K) = 8 * (ω ^ k) ^ 3 + 1 := by rw [hc]; ring
      _ = (2 * ω ^ k + 1) * (4 * (ω ^ k) ^ 2 - 2 * ω ^ k + 1) := by ring
      _ = 0 := by rw [hz, zero_mul]
  have h33 : (3 : K) * 3 = 0 := by linear_combination h9
  exact mul_ne_zero h3 h3 h33

lemma omega_pow_two_mul_mul_self {K : Type*} [CommRing K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    (t : Fin 3) :
    ω ^ (2 * t.val) * ω ^ t.val = 1 := by
  have hc := omega_cube_eq_one hω
  fin_cases t
  · simp
  · simpa [Fin.val_one] using (by linear_combination hc : ω ^ 2 * ω = 1)
  · change ω ^ 4 * ω ^ 2 = 1
    calc ω ^ 4 * ω ^ 2 = (ω ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hc, one_pow]

lemma omega_same_block_equiangular {K : Type*} [CommRing K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {t₁ t₂ : Fin 3} (ht : t₁ ≠ t₂) :
    (1 + ω ^ (2 * t₁.val) * ω ^ t₂.val) * (1 + ω ^ (2 * t₂.val) * ω ^ t₁.val) = 1 := by
  have hc2 : ω ^ 2 = -ω - 1 := by linear_combination hω
  have hc4 : ω ^ 4 = ω := by linear_combination (ω ^ 2 - ω) * hω
  have h22 : ω ^ 2 * ω ^ 2 = ω := by linear_combination (ω ^ 2 - ω) * hω
  fin_cases t₁ <;> fin_cases t₂
  · exact absurd rfl ht
  · change (1 + ω ^ 0 * ω ^ 1) * (1 + ω ^ 2 * ω ^ 0) = 1
    simp only [pow_zero, pow_one, one_mul, mul_one, hc2]
    linear_combination -hω
  · change (1 + ω ^ 0 * ω ^ 2) * (1 + ω ^ 4 * ω ^ 0) = 1
    simp only [pow_zero, one_mul, mul_one, hc4, hc2]
    linear_combination -hω
  · change (1 + ω ^ 2 * ω ^ 0) * (1 + ω ^ 0 * ω ^ 1) = 1
    simp only [pow_zero, pow_one, one_mul, mul_one, hc2]
    linear_combination -hω
  · exact absurd rfl ht
  · change (1 + ω ^ 2 * ω ^ 2) * (1 + ω ^ 4 * ω ^ 1) = 1
    rw [h22, hc4, pow_one]
    calc (1 + ω) * (1 + ω * ω) = 1 + ω + ω ^ 2 + ω ^ 3 := by ring
      _ = 1 := by rw [omega_cube_eq_one hω]; linear_combination hω
  · change (1 + ω ^ 4 * ω ^ 0) * (1 + ω ^ 0 * ω ^ 2) = 1
    simp only [pow_zero, one_mul, mul_one, hc4, hc2]
    linear_combination -hω
  · change (1 + ω ^ 4 * ω ^ 1) * (1 + ω ^ 2 * ω ^ 2) = 1
    rw [h22, hc4, pow_one]
    calc (1 + ω * ω) * (1 + ω) = 1 + ω + ω ^ 2 + ω ^ 3 := by ring
      _ = 1 := by rw [omega_cube_eq_one hω]; linear_combination hω
  · exact absurd rfl ht

lemma nonHesse_dot3_self {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (p : Idx9) :
    dot3 (nonHesseVecY ω p) (nonHesseVecX ω p) = 1 := by
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  rcases p with ⟨j, t⟩
  have hmul := omega_pow_two_mul_mul_self hω t
  fin_cases j
  · simp only [dot3, nonHesseVecY, nonHesseVecX, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    calc 0 * 0 + (2 : K)⁻¹ * 1 + (4 : K)⁻¹ * ω ^ (2 * t.val) * (2 * ω ^ t.val)
        = (2 : K)⁻¹ + (4 : K)⁻¹ * 2 * (ω ^ (2 * t.val) * ω ^ t.val) := by ring
      _ = 1 := by rw [hmul]; field_simp [h2, h4]; ring
  · simp only [dot3, nonHesseVecY, nonHesseVecX, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    calc (2 : K)⁻¹ * ω ^ (2 * t.val) * ω ^ t.val + 0 * 0 + (2 : K)⁻¹ * 1
        = (2 : K)⁻¹ * (ω ^ (2 * t.val) * ω ^ t.val) + (2 : K)⁻¹ := by ring
      _ = 1 := by rw [hmul]; field_simp [h2]; ring
  · simp only [dot3, nonHesseVecY, nonHesseVecX, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    calc (2 : K)⁻¹ * 1 + (2 : K)⁻¹ * ω ^ (2 * t.val) * ω ^ t.val + 0 * 0
        = (2 : K)⁻¹ + (2 : K)⁻¹ * (ω ^ (2 * t.val) * ω ^ t.val) := by ring
      _ = 1 := by rw [hmul]; field_simp [h2]; ring

lemma nonHesse_dot3_same_block {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (ω : K) (j t₁ t₂ : Fin 3) :
    dot3 (nonHesseVecY ω (j, t₁)) (nonHesseVecX ω (j, t₂)) =
      (2 : K)⁻¹ * (1 + ω ^ (2 * t₁.val) * ω ^ t₂.val) := by
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  fin_cases j
  · simp only [dot3, nonHesseVecY, nonHesseVecX, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    field_simp [h2, h4]; ring
  · simp only [dot3, nonHesseVecY, nonHesseVecX, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    ring
  · simp only [dot3, nonHesseVecY, nonHesseVecX, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    ring

lemma nonHesse_det_two_one_ne_zero {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {j j' t₁ t₂ u : Fin 3} (hjj' : j ≠ j') (ht : t₁ ≠ t₂) :
    (Matrix.of ![nonHesseVecX ω (j, t₁), nonHesseVecX ω (j, t₂), nonHesseVecX ω (j', u)]).det ≠ 0 := by
  have hω0 := pow_ne_zero u.val (omega_ne_zero_of_quad hω)
  have hsub21 := omega_pow_sub_ne_zero h3 hω ht.symm
  fin_cases j <;> fin_cases j'
  · exact absurd rfl hjj'
  · rw [Matrix.det_fin_three]
    simp only [nonHesseVecX, Matrix.of_apply, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val]
    intro hdet
    exact mul_ne_zero (mul_ne_zero h2 hω0) hsub21 (by linear_combination hdet)
  · rw [Matrix.det_fin_three]
    simp only [nonHesseVecX, Matrix.of_apply, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val]
    intro hdet
    exact mul_ne_zero h2 hsub21 (by linear_combination hdet)
  · rw [Matrix.det_fin_three]
    simp only [nonHesseVecX, Matrix.of_apply, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val]
    intro hdet
    exact hsub21 (by linear_combination hdet)
  · exact absurd rfl hjj'
  · rw [Matrix.det_fin_three]
    simp only [nonHesseVecX, Matrix.of_apply, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val]
    intro hdet
    exact mul_ne_zero hω0 hsub21 (by linear_combination hdet)
  · rw [Matrix.det_fin_three]
    simp only [nonHesseVecX, Matrix.of_apply, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val]
    intro hdet
    exact mul_ne_zero (mul_ne_zero h2 hω0) hsub21 (by linear_combination hdet)
  · rw [Matrix.det_fin_three]
    simp only [nonHesseVecX, Matrix.of_apply, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val]
    intro hdet
    exact hsub21 (by linear_combination hdet)
  · exact absurd rfl hjj'

/-- **Non-Hesse Equiangular Rank-`1` Idempotent Counterexample:**
Over every field `K` with `(2 : K) ≠ 0`, `(3 : K) ≠ 0`, and `ω ^ 2 + ω + 1 = 0`, the nine
matrices `Q_p = nonHesseIdempotent ω p` (`p ∈ Fin 3 × Fin 3`) at `(a, b, c) = (2, 1, 1)` satisfy:
1. Each `Q_p` is a rank-`1` idempotent (`Q_p * Q_p = Q_p`, `(Q_p).trace = 1`, `(Q_p).rank = 1`);
2. `Tr(Q_p Q_q) = 1` if `p = q` and `(4 : K)⁻¹` if `p ≠ q` (matching `equiangularGram9 K`), and
   `∑ p, Q_p = (3 : K) • 1`;
3. All `9` vectors `x_p = nonHesseVecX ω p` define pairwise distinct projective points
   (`p ≠ q → cross3 (x_p) (x_q) ≠ 0`);
4. Every transversal triple has `(Matrix.of ![x (0, t), x (1, u), x (2, v)]).det =
   2 * ω ^ (t.val + u.val + v.val) + 1 ≠ 0`;
5. The collinear `3`-element subsets of `Idx9` are *precisely* the `3` coordinate-line blocks
   `{(j, 0), (j, 1), (j, 2)}` (`j ∈ Fin 3`), giving `3` collinear triples instead of the `12`
   collinear triples of a Hesse `(9₄, 12₃)` configuration. -/
theorem nonHesse_equiangular_idempotents {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    (∀ p : Idx9,
      nonHesseIdempotent ω p * nonHesseIdempotent ω p = nonHesseIdempotent ω p ∧
      (nonHesseIdempotent ω p).trace = 1 ∧
      (nonHesseIdempotent ω p).rank = 1) ∧
    (∀ p q : Idx9,
      (nonHesseIdempotent ω p * nonHesseIdempotent ω q).trace =
        if p = q then 1 else (4 : K)⁻¹) ∧
    (∑ p : Idx9, nonHesseIdempotent ω p = (3 : K) • (1 : Matrix (Fin 3) (Fin 3) K)) ∧
    (∀ {p q : Idx9}, p ≠ q → cross3 (nonHesseVecX ω p) (nonHesseVecX ω q) ≠ 0) ∧
    (∀ t u v : Fin 3,
      (Matrix.of ![nonHesseVecX ω (0, t), nonHesseVecX ω (1, u), nonHesseVecX ω (2, v)]).det =
        2 * ω ^ (t.val + u.val + v.val) + 1 ∧
      (Matrix.of ![nonHesseVecX ω (0, t), nonHesseVecX ω (1, u), nonHesseVecX ω (2, v)]).det ≠ 0) ∧
    (∀ S : Finset Idx9,
      IsCollinearTriple (nonHesseVecX ω) S ↔ ∃ j : Fin 3, S = {(j, 0), (j, 1), (j, 2)}) ∧
    (Finset.univ.image (fun j : Fin 3 => ({(j, 0), (j, 1), (j, 2)} : Finset Idx9))).card = 3 := by
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have htr_formula : ∀ p q : Idx9,
      (nonHesseIdempotent ω p * nonHesseIdempotent ω q).trace =
        dot3 (nonHesseVecY ω p) (nonHesseVecX ω q) *
        dot3 (nonHesseVecY ω q) (nonHesseVecX ω p) := by
    intro p q
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three,
      nonHesseIdempotent, dot3]
    ring
  have hpart1 : ∀ p : Idx9,
      nonHesseIdempotent ω p * nonHesseIdempotent ω p = nonHesseIdempotent ω p ∧
      (nonHesseIdempotent ω p).trace = 1 ∧
      (nonHesseIdempotent ω p).rank = 1 := by
    intro p
    have hd := nonHesse_dot3_self h2 hω p
    have hidem : nonHesseIdempotent ω p * nonHesseIdempotent ω p = nonHesseIdempotent ω p := by
      ext i k
      rw [Matrix.mul_apply]
      calc ∑ m : Fin 3, nonHesseIdempotent ω p i m * nonHesseIdempotent ω p m k
          = nonHesseVecX ω p i * dot3 (nonHesseVecY ω p) (nonHesseVecX ω p) *
              nonHesseVecY ω p k := by
                rw [Fin.sum_univ_three]
                dsimp [nonHesseIdempotent, dot3]; ring
        _ = nonHesseIdempotent ω p i k := by rw [hd, mul_one]; rfl
    have htr1 : (nonHesseIdempotent ω p).trace = 1 := by
      calc (nonHesseIdempotent ω p).trace = dot3 (nonHesseVecY ω p) (nonHesseVecX ω p) := by
              simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_three, nonHesseIdempotent, dot3]
              ring
        _ = 1 := hd
    have hrk_le : (nonHesseIdempotent ω p).rank ≤ 1 :=
      matrix_rank_le_one_of_outer (nonHesseVecX ω p) (nonHesseVecY ω p)
    have hex_diag : ∃ m : Fin 3, nonHesseIdempotent ω p m m ≠ 0 := by
      by_contra hall
      push Not at hall
      have htr0 : (nonHesseIdempotent ω p).trace = 0 := by
        simp [Matrix.trace, Matrix.diag, hall]
      rw [htr1] at htr0
      exact one_ne_zero htr0
    rcases hex_diag with ⟨m, hm_ne⟩
    have hrk_ge : 1 ≤ (nonHesseIdempotent ω p).rank := by
      have hdet1 : ((nonHesseIdempotent ω p).submatrix (fun _ : Fin 1 => m)
          (fun _ : Fin 1 => m)).det ≠ 0 := by
        simpa [Matrix.det_fin_one] using hm_ne
      calc 1 = Fintype.card (Fin 1) := rfl
        _ = ((nonHesseIdempotent ω p).submatrix (fun _ : Fin 1 => m)
              (fun _ : Fin 1 => m)).rank :=
            (Matrix.rank_of_det_ne_zero hdet1).symm
        _ ≤ (nonHesseIdempotent ω p).rank :=
            Matrix.rank_submatrix_le (nonHesseIdempotent ω p) _ _
    exact ⟨hidem, htr1, by omega⟩
  have hpart2 : ∀ p q : Idx9,
      (nonHesseIdempotent ω p * nonHesseIdempotent ω q).trace =
        if p = q then 1 else (4 : K)⁻¹ := by
    intro p q
    by_cases hpq : p = q
    · subst hpq
      simp only [↓reduceIte, htr_formula, nonHesse_dot3_self h2 hω, mul_one]
    · simp only [hpq, ↓reduceIte]
      rcases p with ⟨j₁, t₁⟩
      rcases q with ⟨j₂, t₂⟩
      by_cases hj : j₁ = j₂
      · subst hj
        have ht : t₁ ≠ t₂ := fun h => hpq (Prod.ext rfl h)
        rw [htr_formula, nonHesse_dot3_same_block h2 ω j₁ t₁ t₂,
          nonHesse_dot3_same_block h2 ω j₁ t₂ t₁]
        have heq_one := omega_same_block_equiangular hω ht
        calc (2 : K)⁻¹ * (1 + ω ^ (2 * t₁.val) * ω ^ t₂.val) *
              ((2 : K)⁻¹ * (1 + ω ^ (2 * t₂.val) * ω ^ t₁.val))
            = (2 : K)⁻¹ * (2 : K)⁻¹ *
                ((1 + ω ^ (2 * t₁.val) * ω ^ t₂.val) * (1 + ω ^ (2 * t₂.val) * ω ^ t₁.val)) := by
                  ring
          _ = (4 : K)⁻¹ := by rw [heq_one, mul_one]; field_simp [h2, h4]; ring
      · have hcross_01 : ∀ t u : Fin 3,
            dot3 (nonHesseVecY ω (0, t)) (nonHesseVecX ω (1, u)) *
            dot3 (nonHesseVecY ω (1, u)) (nonHesseVecX ω (0, t)) = (4 : K)⁻¹ := by
          intro t u
          simp only [dot3, nonHesseVecY, nonHesseVecX, Fin.isValue,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
          calc (0 * ω ^ u.val + (2 : K)⁻¹ * 0 + (4 : K)⁻¹ * ω ^ (2 * t.val) * 1) *
                ((2 : K)⁻¹ * ω ^ (2 * u.val) * 0 + 0 * 1 + (2 : K)⁻¹ * (2 * ω ^ t.val))
              = (4 : K)⁻¹ * ((2 : K)⁻¹ * 2) * (ω ^ (2 * t.val) * ω ^ t.val) := by ring
            _ = (4 : K)⁻¹ := by
                  rw [omega_pow_two_mul_mul_self hω t]; field_simp [h2, h4]
        have hcross_12 : ∀ t u : Fin 3,
            dot3 (nonHesseVecY ω (1, t)) (nonHesseVecX ω (2, u)) *
            dot3 (nonHesseVecY ω (2, u)) (nonHesseVecX ω (1, t)) = (4 : K)⁻¹ := by
          intro t u
          simp only [dot3, nonHesseVecY, nonHesseVecX, Fin.isValue,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
          calc ((2 : K)⁻¹ * ω ^ (2 * t.val) * 1 + 0 * ω ^ u.val + (2 : K)⁻¹ * 0) *
                ((2 : K)⁻¹ * ω ^ t.val + (2 : K)⁻¹ * ω ^ (2 * u.val) * 0 + 0 * 1)
              = (2 : K)⁻¹ * (2 : K)⁻¹ * (ω ^ (2 * t.val) * ω ^ t.val) := by ring
            _ = (4 : K)⁻¹ := by
                  rw [omega_pow_two_mul_mul_self hω t]; field_simp [h2, h4]; ring
        have hcross_20 : ∀ t u : Fin 3,
            dot3 (nonHesseVecY ω (2, t)) (nonHesseVecX ω (0, u)) *
            dot3 (nonHesseVecY ω (0, u)) (nonHesseVecX ω (2, t)) = (4 : K)⁻¹ := by
          intro t u
          simp only [dot3, nonHesseVecY, nonHesseVecX, Fin.isValue,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
          calc ((2 : K)⁻¹ * 0 + (2 : K)⁻¹ * ω ^ (2 * t.val) * 1 + 0 * (2 * ω ^ u.val)) *
                (0 * 1 + (2 : K)⁻¹ * ω ^ t.val + (4 : K)⁻¹ * ω ^ (2 * u.val) * 0)
              = (2 : K)⁻¹ * (2 : K)⁻¹ * (ω ^ (2 * t.val) * ω ^ t.val) := by ring
            _ = (4 : K)⁻¹ := by
                  rw [omega_pow_two_mul_mul_self hω t]; field_simp [h2, h4]; ring
        rw [htr_formula]
        fin_cases j₁ <;> fin_cases j₂
        · exact absurd rfl hj
        · exact hcross_01 t₁ t₂
        · rw [mul_comm]; exact hcross_20 t₂ t₁
        · rw [mul_comm]; exact hcross_01 t₂ t₁
        · exact absurd rfl hj
        · exact hcross_12 t₁ t₂
        · exact hcross_20 t₁ t₂
        · rw [mul_comm]; exact hcross_12 t₂ t₁
        · exact absurd rfl hj
  have hpart3 : ∀ {p q : Idx9}, p ≠ q → cross3 (nonHesseVecX ω p) (nonHesseVecX ω q) ≠ 0 := by
    intro ⟨j₁, t₁⟩ ⟨j₂, t₂⟩ hpq hcr
    have hω0_1 := pow_ne_zero t₁.val (omega_ne_zero_of_quad hω)
    have hω0_2 := pow_ne_zero t₂.val (omega_ne_zero_of_quad hω)
    by_cases hj : j₁ = j₂
    · subst hj
      have ht : t₁ ≠ t₂ := fun h => hpq (Prod.ext rfl h)
      have hsub21 := omega_pow_sub_ne_zero h3 hω ht.symm
      fin_cases j₁
      · have hc0 := congrFun hcr 0
        simp only [cross3, nonHesseVecX, Fin.isValue, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val, Pi.zero_apply] at hc0
        exact mul_ne_zero h2 hsub21 (by linear_combination hc0)
      · have hc1 := congrFun hcr 1
        simp only [cross3, nonHesseVecX, Fin.isValue, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val, Pi.zero_apply] at hc1
        exact hsub21 (by linear_combination hc1)
      · have hc2 := congrFun hcr 2
        simp only [cross3, nonHesseVecX, Fin.isValue, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val, Pi.zero_apply] at hc2
        exact hsub21 (by linear_combination hc2)
    · fin_cases j₁ <;> fin_cases j₂
      · exact hj rfl
      · have hc2 := congrFun hcr 2
        simp only [cross3, nonHesseVecX, Fin.isValue, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val, Pi.zero_apply] at hc2
        exact neg_ne_zero.mpr hω0_2 (by linear_combination hc2)
      · have hc2 := congrFun hcr 2
        simp only [cross3, nonHesseVecX, Fin.isValue, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val, Pi.zero_apply] at hc2
        exact one_ne_zero (by linear_combination -hc2)
      · have hc2 := congrFun hcr 2
        simp only [cross3, nonHesseVecX, Fin.isValue, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val, Pi.zero_apply] at hc2
        exact hω0_1 (by linear_combination hc2)
      · exact hj rfl
      · have hc0 := congrFun hcr 0
        simp only [cross3, nonHesseVecX, Fin.isValue, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val, Pi.zero_apply] at hc0
        exact neg_ne_zero.mpr hω0_2 (by linear_combination hc0)
      · have hc2 := congrFun hcr 2
        simp only [cross3, nonHesseVecX, Fin.isValue, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val, Pi.zero_apply] at hc2
        exact one_ne_zero (by linear_combination hc2)
      · have hc0 := congrFun hcr 0
        simp only [cross3, nonHesseVecX, Fin.isValue, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val, Pi.zero_apply] at hc0
        exact hω0_1 (by linear_combination hc0)
      · exact hj rfl
  have hpart4 : ∀ t u v : Fin 3,
      (Matrix.of ![nonHesseVecX ω (0, t), nonHesseVecX ω (1, u), nonHesseVecX ω (2, v)]).det =
        2 * ω ^ (t.val + u.val + v.val) + 1 ∧
      (Matrix.of ![nonHesseVecX ω (0, t), nonHesseVecX ω (1, u), nonHesseVecX ω (2, v)]).det ≠ 0 := by
    intro t u v
    have hdet_eq :
        (Matrix.of ![nonHesseVecX ω (0, t), nonHesseVecX ω (1, u), nonHesseVecX ω (2, v)]).det =
        2 * ω ^ (t.val + u.val + v.val) + 1 := by
      rw [Matrix.det_fin_three]
      simp only [nonHesseVecX, Matrix.of_apply, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, pow_add]
      ring
    exact ⟨hdet_eq, hdet_eq ▸ two_mul_omega_pow_add_one_ne_zero h3 hω (t.val + u.val + v.val)⟩
  have hpart5 : ∀ S : Finset Idx9,
      IsCollinearTriple (nonHesseVecX ω) S ↔ ∃ j : Fin 3, S = {(j, 0), (j, 1), (j, 2)} := by
    intro S
    constructor
    · rintro ⟨hcard, hdet⟩
      rcases Finset.card_eq_three.mp hcard with ⟨⟨ja, ta⟩, ⟨jb, tb⟩, ⟨jc, tc⟩, hab, hac, hbc, rfl⟩
      have ha : (ja, ta) ∈ ({(ja, ta), (jb, tb), (jc, tc)} : Finset Idx9) := by simp
      have hb : (jb, tb) ∈ ({(ja, ta), (jb, tb), (jc, tc)} : Finset Idx9) := by simp
      have hc : (jc, tc) ∈ ({(ja, ta), (jb, tb), (jc, tc)} : Finset Idx9) := by simp
      have hsame : ja = jb ∧ ja = jc := by
        by_cases hab1 : ja = jb
        · subst hab1
          refine ⟨rfl, ?_⟩
          by_contra hac1
          have ht : ta ≠ tb := fun ht2 => hab (Prod.ext rfl ht2)
          exact nonHesse_det_two_one_ne_zero h2 h3 hω hac1 ht
            (hdet (ja, ta) ha (ja, tb) hb (jc, tc) hc)
        · by_cases hac1 : ja = jc
          · exfalso
            subst hac1
            have ht : ta ≠ tc := fun ht2 => hac (Prod.ext rfl ht2)
            exact nonHesse_det_two_one_ne_zero h2 h3 hω hab1 ht
              (hdet (ja, ta) ha (ja, tc) hc (jb, tb) hb)
          · by_cases hbc1 : jb = jc
            · exfalso
              subst hbc1
              have ht : tb ≠ tc := fun ht2 => hbc (Prod.ext rfl ht2)
              exact nonHesse_det_two_one_ne_zero h2 h3 hω (Ne.symm hab1) ht
                (hdet (jb, tb) hb (jb, tc) hc (ja, ta) ha)
            · exfalso
              fin_cases ja <;> fin_cases jb <;> fin_cases jc
              · exact hab1 rfl
              · exact hab1 rfl
              · exact hab1 rfl
              · exact hac1 rfl
              · exact hbc1 rfl
              · exact (hpart4 ta tb tc).2 (hdet (0, ta) ha (1, tb) hb (2, tc) hc)
              · exact hac1 rfl
              · exact (hpart4 ta tc tb).2 (hdet (0, ta) ha (1, tc) hc (2, tb) hb)
              · exact hbc1 rfl
              · exact hbc1 rfl
              · exact hac1 rfl
              · exact (hpart4 tb ta tc).2 (hdet (0, tb) hb (1, ta) ha (2, tc) hc)
              · exact hab1 rfl
              · exact hab1 rfl
              · exact hab1 rfl
              · exact (hpart4 tc ta tb).2 (hdet (0, tc) hc (1, ta) ha (2, tb) hb)
              · exact hac1 rfl
              · exact hbc1 rfl
              · exact hbc1 rfl
              · exact (hpart4 tb tc ta).2 (hdet (0, tb) hb (1, tc) hc (2, ta) ha)
              · exact hac1 rfl
              · exact (hpart4 tc tb ta).2 (hdet (0, tc) hc (1, tb) hb (2, ta) ha)
              · exact hbc1 rfl
              · exact hac1 rfl
              · exact hab1 rfl
              · exact hab1 rfl
              · exact hab1 rfl
      rcases hsame with ⟨rfl, rfl⟩
      refine ⟨ja, ?_⟩
      have hsub : ({(ja, ta), (ja, tb), (ja, tc)} : Finset Idx9) ⊆ {(ja, 0), (ja, 1), (ja, 2)} := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · fin_cases ta <;> simp
        · fin_cases tb <;> simp
        · fin_cases tc <;> simp
      have hcard_line : ({(ja, 0), (ja, 1), (ja, 2)} : Finset Idx9).card ≤
          ({(ja, ta), (ja, tb), (ja, tc)} : Finset Idx9).card := by
        rw [hcard]
        have hc3 : ({(ja, 0), (ja, 1), (ja, 2)} : Finset Idx9).card = 3 := by
          fin_cases ja <;> decide
        omega
      exact Finset.eq_of_subset_of_card_le hsub hcard_line
    · rintro ⟨j, rfl⟩
      refine ⟨by fin_cases j <;> decide, ?_⟩
      intro ⟨jp, tp⟩ hp ⟨jq, tq⟩ hq ⟨jr, tr⟩ hr
      have hp1 : jp = j := by
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hp
        rcases hp with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> exact h
      have hq1 : jq = j := by
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hq
        rcases hq with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> exact h
      have hr1 : jr = j := by
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hr
        rcases hr with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> exact h
      rw [hp1, hq1, hr1]
      fin_cases j <;>
        simp [Matrix.det_fin_three, nonHesseVecX]
  have hsum3 : ∑ p : Idx9, nonHesseIdempotent ω p = (3 : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    have hc2 : ω ^ 2 = -ω - 1 := by linear_combination hω
    have hc4 : ω ^ 4 = ω := by linear_combination (ω ^ 2 - ω) * hω
    ext i k
    rw [Matrix.sum_apply, Fintype.sum_prod_type]
    by_cases hik : i = k
    · subst hik
      fin_cases i <;>
      · simp [Fin.sum_univ_three, nonHesseIdempotent, nonHesseVecX, nonHesseVecY, hc4, hc2]
        field_simp [h2, h4]
        ring_nf
        simp only [hc2]
        ring
    · fin_cases i <;> fin_cases k
      · exact absurd rfl hik
      · simp [Fin.sum_univ_three, nonHesseIdempotent, nonHesseVecX, nonHesseVecY, hc4, hc2]
        ring
      · simp [Fin.sum_univ_three, nonHesseIdempotent, nonHesseVecX, nonHesseVecY, hc4, hc2]
        ring
      · simp [Fin.sum_univ_three, nonHesseIdempotent, nonHesseVecX, nonHesseVecY, hc4, hc2]
        ring
      · exact absurd rfl hik
      · simp [Fin.sum_univ_three, nonHesseIdempotent, nonHesseVecX, nonHesseVecY, hc4, hc2]
        ring
      · simp [Fin.sum_univ_three, nonHesseIdempotent, nonHesseVecX, nonHesseVecY, hc4, hc2]
        ring
      · simp [Fin.sum_univ_three, nonHesseIdempotent, nonHesseVecX, nonHesseVecY, hc4, hc2]
        ring
      · exact absurd rfl hik
  exact ⟨hpart1, hpart2, hsum3, hpart3, hpart4, hpart5, by decide⟩

end SemaevRCB
