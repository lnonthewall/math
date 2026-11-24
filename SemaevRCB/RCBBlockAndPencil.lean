module

public import SemaevRCB.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic

@[expose] public section

/-!
# Levi-Civita Block Form, Kronecker Pencil `Ψ_RCB`, and Completeness (Theorem 1.2)

Formalization of the Companion Theorem (Theorem 1.2 / Theorem `thm:companion-A` of Paper 1):
1. Exact polynomial cross-product identity for `(rcbX, rcbY, rcbZ)` over any `CommRing`.
2. `(1,2)`-congruence `T_RCB ≅_{sym12} symEps3` and `GL`-equivalence `T_RCB ≅ I₂ ⊗₁,₂ ε₃` over
   any field `K` with `char K ≠ 2, 3` and `b ≠ 0`.
3. Kronecker canonical form `L₁ ⊕ L₁ᵀ ⊕ L₁ ⊕ L₁ᵀ`, constant projective pencil rank `4`,
   double-quotient substitution rank lower bound `≥ 8`, explicit `8`-term rank decomposition,
   flattening formal border-rank lower bound `≥ 6`, and explicit `6`-term polynomial degeneration
   for the complexified two-slice pencil `Ψ_RCB`.
4. Projective Veronese rank-`6` theorem for `|A| ≥ 7` points on `E_b(K)` via degree-`6` univariate
   polynomial divisibility and parity, and discrete block rank/border-rank preservation (including
   `|C| ≥ 2` preservation for `Ψ_RCB|_{A × B × C}` when `-1` is not a square in `K`).
5. Bosma–Lenstra base-locus characterization `RCB(P₁, P₂) = 0 ↔ P₁ - P₂ ∈ E_b[2] \ {O}`,
   unconditional completeness iff `b` is not a cube in `K`, complexified scalar relation exactness,
   and kernel-verified `ZMod 67` (`b = 1`) subgroup counterexample witness.
-/

namespace SemaevRCB

open Matrix Polynomial BigOperators

/-! ## Section 1: Multilinear Equivalences, Congruences, and Retraction Preservation -/

lemma mapTensor_one {K I J L : Type*} [CommRing K]
    [Fintype I] [Fintype J] [Fintype L]
    [DecidableEq I] [DecidableEq J] [DecidableEq L]
    (T : Tensor3 K I J L) :
    mapTensor (1 : Matrix I I K) (1 : Matrix J J K) (1 : Matrix L L K) T = T := by
  funext i' j' l'
  simp [mapTensor, Matrix.one_apply]

lemma mapTensor_mapTensor {K I I' I'' J J' J'' L L' L'' : Type*} [CommSemiring K]
    [Fintype I] [Fintype I'] [Fintype J] [Fintype J'] [Fintype L] [Fintype L']
    (A₂ : Matrix I'' I' K) (B₂ : Matrix J'' J' K) (C₂ : Matrix L'' L' K)
    (A₁ : Matrix I' I K) (B₁ : Matrix J' J K) (C₁ : Matrix L' L K)
    (T : Tensor3 K I J L) :
    mapTensor A₂ B₂ C₂ (mapTensor A₁ B₁ C₁ T) =
      mapTensor (A₂ * A₁) (B₂ * B₁) (C₂ * C₁) T := by
  funext i'' j'' l''
  have hL : mapTensor A₂ B₂ C₂ (mapTensor A₁ B₁ C₁ T) i'' j'' l'' =
      ∑ x : (I' × J' × L') × (I × J × L),
        A₂ i'' x.1.1 * B₂ j'' x.1.2.1 * C₂ l'' x.1.2.2 *
          A₁ x.1.1 x.2.1 * B₁ x.1.2.1 x.2.2.1 * C₁ x.1.2.2 x.2.2.2 *
          T x.2.1 x.2.2.1 x.2.2.2 := by
    simp only [mapTensor, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ =>
      Finset.sum_congr rfl fun l' _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  have hR : mapTensor (A₂ * A₁) (B₂ * B₁) (C₂ * C₁) T i'' j'' l'' =
      ∑ y : (I × J × L) × (L' × J' × I'),
        A₂ i'' y.2.2.2 * B₂ j'' y.2.2.1 * C₂ l'' y.2.1 *
          A₁ y.2.2.2 y.1.1 * B₁ y.2.2.1 y.1.2.1 * C₁ y.2.1 y.1.2.2 *
          T y.1.1 y.1.2.1 y.1.2.2 := by
    simp only [mapTensor, Matrix.mul_apply, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ =>
      Finset.sum_congr rfl fun j' _ => Finset.sum_congr rfl fun i' _ => by ring
  rw [hL, hR]
  let e : ((I' × J' × L') × (I × J × L)) ≃ ((I × J × L) × (L' × J' × I')) :=
    { toFun := fun ⟨⟨i', j', l'⟩, p⟩ => ⟨p, ⟨l', j', i'⟩⟩
      invFun := fun ⟨p, ⟨l', j', i'⟩⟩ => ⟨⟨i', j', l'⟩, p⟩
      left_inv := fun ⟨⟨_, _, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, ⟨_, _, _⟩⟩ => rfl }
  exact Fintype.sum_equiv e _ _ fun _ => rfl

lemma TensorEquiv.refl {K I J L : Type*} [CommRing K]
    [Fintype I] [Fintype J] [Fintype L]
    [DecidableEq I] [DecidableEq J] [DecidableEq L]
    (T : Tensor3 K I J L) : TensorEquiv T T :=
  ⟨1, 1, 1, 1, 1, 1,
    Matrix.mul_one (1 : Matrix I I K), Matrix.mul_one (1 : Matrix I I K),
    Matrix.mul_one (1 : Matrix J J K), Matrix.mul_one (1 : Matrix J J K),
    Matrix.mul_one (1 : Matrix L L K), Matrix.mul_one (1 : Matrix L L K),
    mapTensor_one T⟩

lemma TensorEquiv.symm {K I I' J J' L L' : Type*} [CommRing K]
    [Fintype I] [Fintype I'] [Fintype J] [Fintype J'] [Fintype L] [Fintype L']
    [DecidableEq I] [DecidableEq I'] [DecidableEq J] [DecidableEq J']
    [DecidableEq L] [DecidableEq L']
    {T : Tensor3 K I J L} {T' : Tensor3 K I' J' L'} (h : TensorEquiv T T') :
    TensorEquiv T' T := by
  rcases h with ⟨A, Ai, B, Bi, C, Ci, hAAi, hAiA, hBBi, hBiB, hCCi, hCiC, hmap⟩
  refine ⟨Ai, A, Bi, B, Ci, C, hAiA, hAAi, hBiB, hBBi, hCiC, hCCi, ?_⟩
  rw [← hmap, mapTensor_mapTensor, hAiA, hBiB, hCiC, mapTensor_one]

lemma TensorEquiv.trans {K I₁ I₂ I₃ J₁ J₂ J₃ L₁ L₂ L₃ : Type*} [CommRing K]
    [Fintype I₁] [Fintype I₂] [Fintype I₃]
    [Fintype J₁] [Fintype J₂] [Fintype J₃]
    [Fintype L₁] [Fintype L₂] [Fintype L₃]
    [DecidableEq I₁] [DecidableEq I₂] [DecidableEq I₃]
    [DecidableEq J₁] [DecidableEq J₂] [DecidableEq J₃]
    [DecidableEq L₁] [DecidableEq L₂] [DecidableEq L₃]
    {T₁ : Tensor3 K I₁ J₁ L₁} {T₂ : Tensor3 K I₂ J₂ L₂} {T₃ : Tensor3 K I₃ J₃ L₃}
    (h₁₂ : TensorEquiv T₁ T₂) (h₂₃ : TensorEquiv T₂ T₃) :
    TensorEquiv T₁ T₃ := by
  rcases h₁₂ with ⟨A₁, Ai₁, B₁, Bi₁, C₁, Ci₁, hA₁, hAi₁, hB₁, hBi₁, hC₁, hCi₁, hm₁⟩
  rcases h₂₃ with ⟨A₂, Ai₂, B₂, Bi₂, C₂, Ci₂, hA₂, hAi₂, hB₂, hBi₂, hC₂, hCi₂, hm₂⟩
  refine ⟨A₂ * A₁, Ai₁ * Ai₂, B₂ * B₁, Bi₁ * Bi₂, C₂ * C₁, Ci₁ * Ci₂,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc (A₂ * A₁) * (Ai₁ * Ai₂) = A₂ * (A₁ * Ai₁) * Ai₂ := by simp [Matrix.mul_assoc]
      _ = 1 := by rw [hA₁, Matrix.mul_one, hA₂]
  · calc (Ai₁ * Ai₂) * (A₂ * A₁) = Ai₁ * (Ai₂ * A₂) * A₁ := by simp [Matrix.mul_assoc]
      _ = 1 := by rw [hAi₂, Matrix.mul_one, hAi₁]
  · calc (B₂ * B₁) * (Bi₁ * Bi₂) = B₂ * (B₁ * Bi₁) * Bi₂ := by simp [Matrix.mul_assoc]
      _ = 1 := by rw [hB₁, Matrix.mul_one, hB₂]
  · calc (Bi₁ * Bi₂) * (B₂ * B₁) = Bi₁ * (Bi₂ * B₂) * B₁ := by simp [Matrix.mul_assoc]
      _ = 1 := by rw [hBi₂, Matrix.mul_one, hBi₁]
  · calc (C₂ * C₁) * (Ci₁ * Ci₂) = C₂ * (C₁ * Ci₁) * Ci₂ := by simp [Matrix.mul_assoc]
      _ = 1 := by rw [hC₁, Matrix.mul_one, hC₂]
  · calc (Ci₁ * Ci₂) * (C₂ * C₁) = Ci₁ * (Ci₂ * C₂) * C₁ := by simp [Matrix.mul_assoc]
      _ = 1 := by rw [hCi₂, Matrix.mul_one, hCi₁]
  · rw [← mapTensor_mapTensor, hm₁, hm₂]

lemma TensorSym12Congruent.symm {K I I' L L' : Type*} [CommRing K]
    [Fintype I] [Fintype I'] [Fintype L] [Fintype L']
    [DecidableEq I] [DecidableEq I'] [DecidableEq L] [DecidableEq L']
    {T : Tensor3 K I I L} {T' : Tensor3 K I' I' L'} (h : TensorSym12Congruent T T') :
    TensorSym12Congruent T' T := by
  rcases h with ⟨A, Ai, C, Ci, hAAi, hAiA, hCCi, hCiC, hmap⟩
  refine ⟨Ai, A, Ci, C, hAiA, hAAi, hCiC, hCCi, ?_⟩
  rw [← hmap, mapTensor_mapTensor, hAiA, hCiC, mapTensor_one]

lemma TensorSym12Congruent.toTensorEquiv {K I I' L L' : Type*} [CommRing K]
    [Fintype I] [Fintype I'] [Fintype L] [Fintype L']
    [DecidableEq I] [DecidableEq I'] [DecidableEq L] [DecidableEq L']
    {T : Tensor3 K I I L} {T' : Tensor3 K I' I' L'} (h : TensorSym12Congruent T T') :
    TensorEquiv T T' := by
  rcases h with ⟨A, Ai, C, Ci, hAAi, hAiA, hCCi, hCiC, hmap⟩
  exact ⟨A, Ai, A, Ai, C, Ci, hAAi, hAiA, hAAi, hAiA, hCCi, hCiC, hmap⟩

lemma hasTensorRankLe_mapTensor_iff_of_leftInv
    {K I I' J J' L L' : Type*} [CommRing K]
    [Fintype I] [Fintype I'] [Fintype J] [Fintype J'] [Fintype L] [Fintype L']
    [DecidableEq I] [DecidableEq J] [DecidableEq L]
    {A : Matrix I' I K} {Ai : Matrix I I' K} (hA : Ai * A = 1)
    {B : Matrix J' J K} {Bi : Matrix J J' K} (hB : Bi * B = 1)
    {C : Matrix L' L K} {Ci : Matrix L L' K} (hC : Ci * C = 1)
    (T : Tensor3 K I J L) (r : ℕ) :
    HasTensorRankLe (mapTensor A B C T) r ↔ HasTensorRankLe T r := by
  constructor
  · intro hr
    have hback := hr.mapTensor Ai Bi Ci
    rwa [mapTensor_mapTensor, hA, hB, hC, mapTensor_one] at hback
  · exact fun hr => hr.mapTensor A B C

lemma hasFormalBorderRankLe_mapTensor_iff_of_leftInv
    {K I I' J J' L L' : Type*} [CommRing K]
    [Fintype I] [Fintype I'] [Fintype J] [Fintype J'] [Fintype L] [Fintype L']
    [DecidableEq I] [DecidableEq J] [DecidableEq L]
    {A : Matrix I' I K} {Ai : Matrix I I' K} (hA : Ai * A = 1)
    {B : Matrix J' J K} {Bi : Matrix J J' K} (hB : Bi * B = 1)
    {C : Matrix L' L K} {Ci : Matrix L L' K} (hC : Ci * C = 1)
    (T : Tensor3 K I J L) (r : ℕ) :
    HasFormalBorderRankLe (mapTensor A B C T) r ↔ HasFormalBorderRankLe T r := by
  constructor
  · intro hr
    have hback := hr.mapTensor Ai Bi Ci
    rwa [mapTensor_mapTensor, hA, hB, hC, mapTensor_one] at hback
  · exact fun hr => hr.mapTensor A B C

lemma hasSym12RankLe_mapTensor_iff_of_leftInv
    {K I I' L L' : Type*} [CommRing K]
    [Fintype I] [Fintype I'] [Fintype L] [Fintype L']
    [DecidableEq I] [DecidableEq L]
    {A : Matrix I' I K} {Ai : Matrix I I' K} (hA : Ai * A = 1)
    {C : Matrix L' L K} {Ci : Matrix L L' K} (hC : Ci * C = 1)
    (T : Tensor3 K I I L) (r : ℕ) :
    HasSym12RankLe (mapTensor A A C T) r ↔ HasSym12RankLe T r := by
  constructor
  · intro hr
    have hback := hr.mapSym12 Ai Ci
    rwa [mapTensor_mapTensor, hA, hC, mapTensor_one] at hback
  · exact fun hr => hr.mapSym12 A C

lemma hasSym12FormalBorderRankLe_mapTensor_iff_of_leftInv
    {K I I' L L' : Type*} [CommRing K]
    [Fintype I] [Fintype I'] [Fintype L] [Fintype L']
    [DecidableEq I] [DecidableEq L]
    {A : Matrix I' I K} {Ai : Matrix I I' K} (hA : Ai * A = 1)
    {C : Matrix L' L K} {Ci : Matrix L L' K} (hC : Ci * C = 1)
    (T : Tensor3 K I I L) (r : ℕ) :
    HasSym12FormalBorderRankLe (mapTensor A A C T) r ↔ HasSym12FormalBorderRankLe T r := by
  constructor
  · intro hr
    have hback := hr.mapSym12 Ai Ci
    rwa [mapTensor_mapTensor, hA, hC, mapTensor_one] at hback
  · exact fun hr => hr.mapSym12 A C

lemma TensorEquiv.hasTensorRankLe_iff {K I I' J J' L L' : Type*} [CommRing K]
    [Fintype I] [Fintype I'] [Fintype J] [Fintype J'] [Fintype L] [Fintype L']
    [DecidableEq I] [DecidableEq I'] [DecidableEq J] [DecidableEq J']
    [DecidableEq L] [DecidableEq L']
    {T : Tensor3 K I J L} {T' : Tensor3 K I' J' L'} (h : TensorEquiv T T') (r : ℕ) :
    HasTensorRankLe T r ↔ HasTensorRankLe T' r := by
  rcases h with ⟨A, Ai, B, Bi, C, Ci, _, hAiA, _, hBiB, _, hCiC, rfl⟩
  exact (hasTensorRankLe_mapTensor_iff_of_leftInv hAiA hBiB hCiC T r).symm

lemma TensorEquiv.hasFormalBorderRankLe_iff {K I I' J J' L L' : Type*} [CommRing K]
    [Fintype I] [Fintype I'] [Fintype J] [Fintype J'] [Fintype L] [Fintype L']
    [DecidableEq I] [DecidableEq I'] [DecidableEq J] [DecidableEq J']
    [DecidableEq L] [DecidableEq L']
    {T : Tensor3 K I J L} {T' : Tensor3 K I' J' L'} (h : TensorEquiv T T') (r : ℕ) :
    HasFormalBorderRankLe T r ↔ HasFormalBorderRankLe T' r := by
  rcases h with ⟨A, Ai, B, Bi, C, Ci, _, hAiA, _, hBiB, _, hCiC, rfl⟩
  exact (hasFormalBorderRankLe_mapTensor_iff_of_leftInv hAiA hBiB hCiC T r).symm

lemma TensorSym12Congruent.hasSym12RankLe_iff {K I I' L L' : Type*} [CommRing K]
    [Fintype I] [Fintype I'] [Fintype L] [Fintype L']
    [DecidableEq I] [DecidableEq I'] [DecidableEq L] [DecidableEq L']
    {T : Tensor3 K I I L} {T' : Tensor3 K I' I' L'} (h : TensorSym12Congruent T T') (r : ℕ) :
    HasSym12RankLe T r ↔ HasSym12RankLe T' r := by
  rcases h with ⟨A, Ai, C, Ci, _, hAiA, _, hCiC, rfl⟩
  exact (hasSym12RankLe_mapTensor_iff_of_leftInv hAiA hCiC T r).symm

lemma TensorSym12Congruent.hasSym12FormalBorderRankLe_iff {K I I' L L' : Type*} [CommRing K]
    [Fintype I] [Fintype I'] [Fintype L] [Fintype L']
    [DecidableEq I] [DecidableEq I'] [DecidableEq L] [DecidableEq L']
    {T : Tensor3 K I I L} {T' : Tensor3 K I' I' L'} (h : TensorSym12Congruent T T') (r : ℕ) :
    HasSym12FormalBorderRankLe T r ↔ HasSym12FormalBorderRankLe T' r := by
  rcases h with ⟨A, Ai, C, Ci, _, hAiA, _, hCiC, rfl⟩
  exact (hasSym12FormalBorderRankLe_mapTensor_iff_of_leftInv hAiA hCiC T r).symm

/-! ## Section 2: Polynomial Cross-Product Identity & Levi-Civita Block Form (Theorem 1.2(1)) -/

/-- First quadratic vector `u(P) = (6 X², -2 Y Z, Y² - 3b Z²)` in Theorem 1.2(1). -/
def rcbU {K : Type*} [CommRing K] (b : K) (P : Fin 3 → K) : Fin 3 → K :=
  ![6 * P 0 ^ 2, -2 * P 1 * P 2, P 1 ^ 2 - 3 * b * P 2 ^ 2]

/-- Second quadratic vector `v(P) = (Y² + 3b Z², X Y, -3b X Z)` in Theorem 1.2(1). -/
def rcbV {K : Type*} [CommRing K] (b : K) (P : Fin 3 → K) : Fin 3 → K :=
  ![P 1 ^ 2 + 3 * b * P 2 ^ 2, P 0 * P 1, -3 * b * P 0 * P 2]

/-- Bundled RCB evaluation vector `(X_+, Y_+, Z_+)` on `K³ × K³`. -/
def rcbEval {K : Type*} [CommRing K] (b : K) (P₁ P₂ : Fin 3 → K) : Fin 3 → K :=
  ![rcbX b P₁ P₂, rcbY b P₁ P₂, rcbZ b P₁ P₂]

/-- **Theorem 1.2(1) (Exact polynomial cross-product identity):**
Over any commutative ring `K`, `(-X_+, 2Y_+, 2Z_+) = u(P₁) × v(P₂) + u(P₂) × v(P₁)`. -/
theorem rcb_cross_product_identity {K : Type*} [CommRing K] (b : K) (P₁ P₂ : Fin 3 → K) :
    ![-rcbX b P₁ P₂, 2 * rcbY b P₁ P₂, 2 * rcbZ b P₁ P₂] =
      cross3 (rcbU b P₁) (rcbV b P₂) + cross3 (rcbU b P₂) (rcbV b P₁) := by
  funext k
  fin_cases k <;>
    simp [rcbX, rcbY, rcbZ, rcbU, rcbV, cross3] <;>
    ring

/-- Mode-1 swap-sign matrix `S = [[0, -I₃], [I₃, 0]]` sending `symEps3` to `I2_eps3`. -/
def symToDiagMat (K : Type*) [CommRing K] :
    Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) K :=
  fun p q =>
    if p.1 = 0 ∧ q.1 = 1 ∧ p.2 = q.2 then -1
    else if p.1 = 1 ∧ q.1 = 0 ∧ p.2 = q.2 then 1
    else 0

lemma symToDiagMat_mul_neg (K : Type*) [CommRing K] :
    symToDiagMat K * (-symToDiagMat K) = 1 := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp only [Matrix.mul_apply, Matrix.neg_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    symToDiagMat, Matrix.one_apply, Prod.mk.injEq, Fin.isValue]
  by_cases hij : i = j <;> fin_cases a <;> fin_cases b <;> simp [hij]

lemma neg_mul_symToDiagMat (K : Type*) [CommRing K] :
    (-symToDiagMat K) * symToDiagMat K = 1 := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp only [Matrix.mul_apply, Matrix.neg_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    symToDiagMat, Matrix.one_apply, Prod.mk.injEq, Fin.isValue]
  by_cases hij : i = j <;> fin_cases a <;> fin_cases b <;> simp [hij]

lemma mapTensor_symToDiagMat_symEps3 (K : Type*) [CommRing K] :
    mapTensor (symToDiagMat K) (1 : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) K)
      (1 : Matrix (Fin 3) (Fin 3) K) (symEps3 K) = I2_eps3 K := by
  funext ⟨a, i⟩ ⟨b, j⟩ k
  unfold mapTensor
  simp only [Matrix.one_apply]
  have hcollapse :
      (∑ p : Fin 2 × Fin 3, ∑ q : Fin 2 × Fin 3, ∑ l : Fin 3,
        symToDiagMat K (a, i) p * (if (b, j) = q then (1 : K) else 0) *
          (if k = l then (1 : K) else 0) * symEps3 K p q l) =
      ∑ p : Fin 2 × Fin 3, symToDiagMat K (a, i) p * symEps3 K p (b, j) k := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_eq_single (b, j)]
    · rw [Finset.sum_eq_single k]
      · simp
      · intro l _ hlk; simp [Ne.symm hlk]
      · intro hk; exact absurd (Finset.mem_univ k) hk
    · intro q _ hq; simp [Ne.symm hq]
    · intro hb; exact absurd (Finset.mem_univ (b, j)) hb
  rw [hcollapse, Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases a <;> fin_cases b <;> simp [symToDiagMat, symEps3, I2_eps3]

/-- `symEps3 K` is `GL`-equivalent to `I2_eps3 K` over any commutative ring `K`. -/
theorem symEps3_equiv_I2_eps3 (K : Type*) [CommRing K] :
    TensorEquiv (symEps3 K) (I2_eps3 K) :=
  ⟨symToDiagMat K, -symToDiagMat K, 1, 1, 1, 1,
    symToDiagMat_mul_neg K, neg_mul_symToDiagMat K,
    Matrix.mul_one (1 : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) K),
    Matrix.mul_one (1 : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) K),
    Matrix.mul_one (1 : Matrix (Fin 3) (Fin 3) K),
    Matrix.mul_one (1 : Matrix (Fin 3) (Fin 3) K),
    mapTensor_symToDiagMat_symEps3 K⟩

/-- Monomial-to-`(u, v)` coefficient matrix `M_uv : Matrix (Fin 2 × Fin 3) (Fin 6) K`
relative to `veronese2 = (X², Y², Z², XY, YZ, XZ)`. -/
def rcbUVFromMonomialMat (K : Type*) [CommRing K] (b : K) :
    Matrix (Fin 2 × Fin 3) (Fin 6) K :=
  fun p =>
    ![![![6, 0, 0, 0, 0, 0],
        ![0, 0, 0, 0, -2, 0],
        ![0, 1, -3 * b, 0, 0, 0]],
      ![![0, 1, 3 * b, 0, 0, 0],
        ![0, 0, 0, 1, 0, 0],
        ![0, 0, 0, 0, 0, -3 * b]]] p.1 p.2

/-- Inverse `(u, v)`-to-monomial matrix `M_uv⁻¹ : Matrix (Fin 6) (Fin 2 × Fin 3) K`. -/
def rcbMonomialFromUVMat (K : Type*) [Field K] (b : K) :
    Matrix (Fin 6) (Fin 2 × Fin 3) K :=
  fun m p =>
    (![![![((6 : K)⁻¹), 0, 0], ![0, 0, 0]],
       ![![0, 0, (2 : K)⁻¹], ![(2 : K)⁻¹, 0, 0]],
       ![![0, 0, -(6 : K)⁻¹ * b⁻¹], ![(6 : K)⁻¹ * b⁻¹, 0, 0]],
       ![![0, 0, 0], ![0, 1, 0]],
       ![![0, -(2 : K)⁻¹, 0], ![0, 0, 0]],
       ![![0, 0, 0], ![0, 0, -(3 : K)⁻¹ * b⁻¹]]] m) p.1 p.2

/-- Output scaling matrix `diag(-1, 2, 2)` mapping `(X_+, Y_+, Z_+)` to `(-X_+, 2Y_+, 2Z_+)`. -/
def rcbOutToSymMat (K : Type*) [CommRing K] : Matrix (Fin 3) (Fin 3) K :=
  Matrix.diagonal ![-1, 2, 2]

/-- Inverse output scaling matrix `diag(-1, 1/2, 1/2)`. -/
def rcbSymToOutMat (K : Type*) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  Matrix.diagonal ![-1, (2 : K)⁻¹, (2 : K)⁻¹]

lemma rcbUVFromMonomial_mul_inv {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {b : K} (hb : b ≠ 0) :
    rcbUVFromMonomialMat K b * rcbMonomialFromUVMat K b = 1 := by
  have h6 : (6 : K) ≠ 0 := by
    have : (6 : K) = 2 * 3 := by norm_num
    rw [this]; exact mul_ne_zero h2 h3
  ext ⟨a, i⟩ ⟨c, j⟩
  rw [Matrix.mul_apply]
  fin_cases a <;> fin_cases c <;> fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_six, rcbUVFromMonomialMat, rcbMonomialFromUVMat] <;>
    field_simp [h2, h3, h6, hb] <;>
    ring

lemma rcbMonomialFromUV_mul_inv {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {b : K} (hb : b ≠ 0) :
    rcbMonomialFromUVMat K b * rcbUVFromMonomialMat K b = 1 := by
  have h6 : (6 : K) ≠ 0 := by
    have : (6 : K) = 2 * 3 := by norm_num
    rw [this]; exact mul_ne_zero h2 h3
  ext m n
  rw [Matrix.mul_apply]
  fin_cases m <;> fin_cases n <;>
    simp [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three,
      rcbUVFromMonomialMat, rcbMonomialFromUVMat] <;>
    field_simp [h2, h3, h6, hb] <;>
    ring

lemma rcbOutToSym_mul_inv {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) :
    rcbOutToSymMat K * rcbSymToOutMat K = 1 := by
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp [rcbOutToSymMat, rcbSymToOutMat, h2]

lemma rcbSymToOut_mul_inv {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) :
    rcbSymToOutMat K * rcbOutToSymMat K = 1 := by
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp [rcbOutToSymMat, rcbSymToOutMat, h2]

lemma sum_symEps3_zero {K : Type*} [CommRing K] (f g : Fin 2 × Fin 3 → K) :
    (∑ p : Fin 2 × Fin 3, ∑ q : Fin 2 × Fin 3, f p * g q * symEps3 K p q 0) =
      f (0, 1) * g (1, 2) - f (0, 2) * g (1, 1) - f (1, 1) * g (0, 2) + f (1, 2) * g (0, 1) := by
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three, symEps3, eps3]
  ring

lemma sum_symEps3_one {K : Type*} [CommRing K] (f g : Fin 2 × Fin 3 → K) :
    (∑ p : Fin 2 × Fin 3, ∑ q : Fin 2 × Fin 3, f p * g q * symEps3 K p q 1) =
      -f (0, 0) * g (1, 2) + f (0, 2) * g (1, 0) + f (1, 0) * g (0, 2) - f (1, 2) * g (0, 0) := by
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three, symEps3, eps3]
  ring

lemma sum_symEps3_two {K : Type*} [CommRing K] (f g : Fin 2 × Fin 3 → K) :
    (∑ p : Fin 2 × Fin 3, ∑ q : Fin 2 × Fin 3, f p * g q * symEps3 K p q 2) =
      f (0, 0) * g (1, 1) - f (0, 1) * g (1, 0) - f (1, 0) * g (0, 1) + f (1, 1) * g (0, 0) := by
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three, symEps3, eps3]
  ring

lemma mapTensor_UV_symEps3_eq_TRCB {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) (b : K) :
    mapTensor (rcbUVFromMonomialMat K b).transpose (rcbUVFromMonomialMat K b).transpose
      (rcbSymToOutMat K) (symEps3 K) = T_RCB K b := by
  funext m n k
  have hcol3 :
      (∑ p : Fin 2 × Fin 3, ∑ q : Fin 2 × Fin 3, ∑ l : Fin 3,
        (rcbUVFromMonomialMat K b).transpose m p * (rcbUVFromMonomialMat K b).transpose n q *
          rcbSymToOutMat K k l * symEps3 K p q l) =
      ![-1, (2 : K)⁻¹, (2 : K)⁻¹] k *
        ∑ p : Fin 2 × Fin 3, ∑ q : Fin 2 × Fin 3,
          rcbUVFromMonomialMat K b p m * rcbUVFromMonomialMat K b q n * symEps3 K p q k := by
    simp only [rcbSymToOutMat, Matrix.transpose_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_eq_single k]
    · simp; ring
    · intro l _ hlk; simp [Ne.symm hlk]
    · intro hk; exact absurd (Finset.mem_univ k) hk
  unfold mapTensor
  rw [hcol3]
  fin_cases k
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
      sum_symEps3_zero (fun p => rcbUVFromMonomialMat K b p m)
        (fun q => rcbUVFromMonomialMat K b q n)]
    fin_cases m <;> fin_cases n <;> simp [rcbUVFromMonomialMat, T_RCB] <;> ring
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
      sum_symEps3_one (fun p => rcbUVFromMonomialMat K b p m)
        (fun q => rcbUVFromMonomialMat K b q n)]
    fin_cases m <;> fin_cases n <;> simp [rcbUVFromMonomialMat, T_RCB] <;>
      field_simp [h2] <;> ring
  · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val,
      sum_symEps3_two (fun p => rcbUVFromMonomialMat K b p m)
        (fun q => rcbUVFromMonomialMat K b q n)]
    fin_cases m <;> fin_cases n <;> simp [rcbUVFromMonomialMat, T_RCB] <;>
      field_simp [h2] <;> ring

/-- **Theorem 1.2(1) (`(1,2)`-congruence `T_RCB ≅_{sym12} symEps3`):**
Over any field `K` with `char K ≠ 2, 3` and `b ≠ 0`, `T_RCB K b` is `(1,2)`-congruent to `symEps3 K`. -/
theorem T_RCB_sym12Congruent_symEps3 {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {b : K} (hb : b ≠ 0) :
    TensorSym12Congruent (T_RCB K b) (symEps3 K) := by
  have hsym : TensorSym12Congruent (symEps3 K) (T_RCB K b) := by
    refine ⟨(rcbUVFromMonomialMat K b).transpose, (rcbMonomialFromUVMat K b).transpose,
      rcbSymToOutMat K, rcbOutToSymMat K, ?_, ?_,
      rcbSymToOut_mul_inv h2, rcbOutToSym_mul_inv h2, mapTensor_UV_symEps3_eq_TRCB h2 b⟩
    · rw [← Matrix.transpose_mul, rcbMonomialFromUV_mul_inv h2 h3 hb, Matrix.transpose_one]
    · rw [← Matrix.transpose_mul, rcbUVFromMonomial_mul_inv h2 h3 hb, Matrix.transpose_one]
  exact hsym.symm

/-- **Theorem 1.1 / 1.2(1) (`GL`-equivalence `T_RCB ≅ I₂ ⊗₁,₂ ε₃`):**
Over any field `K` with `char K ≠ 2, 3` and `b ≠ 0`, `T_RCB K b` is `GL`-equivalent to `I2_eps3 K`. -/
theorem T_RCB_equiv_I2_eps3 {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {b : K} (hb : b ≠ 0) :
    TensorEquiv (T_RCB K b) (I2_eps3 K) :=
  (T_RCB_sym12Congruent_symEps3 h2 h3 hb).toTensorEquiv.trans (symEps3_equiv_I2_eps3 K)

/-! ## Section 3: Complexified Two-Slice Pencil `Ψ_RCB` & Kronecker Form (Theorem 1.2(2)) -/

/-- Complexified two-slice matrix pencil `Ψ_RCB = (M_X + i M_Y, M_Z) ∈ L⁶ ⊗ L⁶ ⊗ L²`
over any ring `L` equipped with `imUnit` (`i² = -1`). -/
def Psi_RCB (L : Type*) [CommRing L] (b imUnit : L) : Tensor3 L (Fin 6) (Fin 6) (Fin 2) :=
  fun p q k =>
    match k.val with
    | 0 => T_RCB L b p q 0 + imUnit * T_RCB L b p q 1
    | _ => T_RCB L b p q 2

/-- Single `3 × 3 × 2` Kronecker block `L₁ ⊕ L₁ᵀ` with slices
`K₁ = e₀ ⊗ e₀ + e₁ ⊗ e₂` and `K₂ = e₀ ⊗ e₁ + e₂ ⊗ e₂`. -/
def kroneckerL1Pair (L : Type*) [CommRing L] : Tensor3 L (Fin 3) (Fin 3) (Fin 2) :=
  fun i j k =>
    match k.val, i.val, j.val with
    | 0, 0, 0 => 1
    | 0, 1, 2 => 1
    | 1, 0, 1 => 1
    | 1, 2, 2 => 1
    | _, _, _ => 0

/-- Doubled `6 × 6 × 2` Kronecker canonical form `L₁ ⊕ L₁ᵀ ⊕ L₁ ⊕ L₁ᵀ = I₂ ⊗₁,₂ (L₁ ⊕ L₁ᵀ)`. -/
def kroneckerDoubleL1Pair (L : Type*) [CommRing L] :
    Tensor3 L (Fin 2 × Fin 3) (Fin 2 × Fin 3) (Fin 2) :=
  fun p q k => if p.1 = q.1 then kroneckerL1Pair L p.2 q.2 k else 0

/-- Domain basis `(k₂, 2k₁, v₀)` of determinant `2` for the `3 × 3` skew pencil `(S₁, S₂)`. -/
def pencilDomMat (L : Type*) [CommRing L] (imUnit : L) : Matrix (Fin 3) (Fin 3) L :=
  ![![0, 2, 0], ![0, -imUnit, 1], ![1, 0, 0]]

/-- Inverse of `pencilDomMat`. -/
def pencilDomInvMat (L : Type*) [Field L] (imUnit : L) : Matrix (Fin 3) (Fin 3) L :=
  ![![0, 0, 1], ![(2 : L)⁻¹, 0, 0], ![imUnit * (2 : L)⁻¹, 1, 0]]

/-- Codomain basis `(w₂, w₃, w₁)` of determinant `-1/2` for the `3 × 3` skew pencil `(S₁, S₂)`. -/
def pencilCodMat (L : Type*) [Field L] (imUnit : L) : Matrix (Fin 3) (Fin 3) L :=
  ![![-imUnit * (2 : L)⁻¹, 0, (2 : L)⁻¹], ![-1, 0, 0], ![0, 1, 0]]

/-- Inverse `Q_cod⁻¹` of `pencilCodMat`. -/
def pencilCodInvMat (L : Type*) [CommRing L] (imUnit : L) : Matrix (Fin 3) (Fin 3) L :=
  ![![0, -1, 0], ![0, 0, 1], ![2, -imUnit, 0]]

lemma det_pencilDomMat {L : Type*} [CommRing L] (imUnit : L) :
    (pencilDomMat L imUnit).det = 2 := by
  rw [Matrix.det_fin_three]
  simp [pencilDomMat]

lemma det_pencilCodMat {L : Type*} [Field L] (imUnit : L) :
    (pencilCodMat L imUnit).det = -(2 : L)⁻¹ := by
  rw [Matrix.det_fin_three]
  simp [pencilCodMat]

lemma pencilCodInv_mul_Cod {L : Type*} [Field L] (h2 : (2 : L) ≠ 0) (imUnit : L) :
    pencilCodInvMat L imUnit * pencilCodMat L imUnit = 1 := by
  ext r s
  rw [Matrix.mul_apply]
  fin_cases r <;> fin_cases s <;>
    simp [Fin.sum_univ_three, pencilCodInvMat, pencilCodMat, h2]
  field_simp [h2]
  ring

lemma pencilCod_mul_CodInv {L : Type*} [Field L] (h2 : (2 : L) ≠ 0) (imUnit : L) :
    pencilCodMat L imUnit * pencilCodInvMat L imUnit = 1 := by
  ext r s
  rw [Matrix.mul_apply]
  fin_cases r <;> fin_cases s <;>
    simp [Fin.sum_univ_three, pencilCodInvMat, pencilCodMat, h2]
  field_simp [h2]
  ring

lemma pencilDom_mul_DomInv {L : Type*} [Field L] (h2 : (2 : L) ≠ 0) (imUnit : L) :
    pencilDomMat L imUnit * pencilDomInvMat L imUnit = 1 := by
  ext r s
  rw [Matrix.mul_apply]
  fin_cases r <;> fin_cases s <;>
    simp [Fin.sum_univ_three, pencilDomMat, pencilDomInvMat, h2]

lemma pencilDomInv_mul_Dom {L : Type*} [Field L] (h2 : (2 : L) ≠ 0) (imUnit : L) :
    pencilDomInvMat L imUnit * pencilDomMat L imUnit = 1 := by
  ext r s
  rw [Matrix.mul_apply]
  fin_cases r <;> fin_cases s <;>
    simp [Fin.sum_univ_three, pencilDomMat, pencilDomInvMat, h2]

/-- Single `3 × 3 × 2` skew pencil `(S₁, S₂)` with `S₁ = -E₀ + (i/2) E₁` and `S₂ = (1/2) E₂`. -/
def skewSinglePencil (L : Type*) [Field L] (imUnit : L) : Tensor3 L (Fin 3) (Fin 3) (Fin 2) :=
  fun i j k =>
    match k.val with
    | 0 => -eps3 L i j 0 + imUnit * (2 : L)⁻¹ * eps3 L i j 1
    | _ => (2 : L)⁻¹ * eps3 L i j 2

lemma mapTensor_skewSingle_eq_kroneckerL1Pair {L : Type*} [Field L]
    (h2 : (2 : L) ≠ 0) (imUnit : L) :
    mapTensor (pencilCodInvMat L imUnit) (pencilDomMat L imUnit).transpose
      (1 : Matrix (Fin 2) (Fin 2) L) (skewSinglePencil L imUnit) = kroneckerL1Pair L := by
  funext r s k
  unfold mapTensor
  simp only [Matrix.transpose_apply, Matrix.one_apply]
  fin_cases r <;> fin_cases s <;> fin_cases k <;>
    simp [Fin.sum_univ_three, pencilCodInvMat, pencilDomMat,
      skewSinglePencil, kroneckerL1Pair, eps3, h2] <;>
    field_simp [h2] <;>
    ring

/-- Intermediate `6 × 6 × 2` skew-block pencil `I₂ ⊗₁,₂ (S₁, S₂)`. -/
def skewDoublePencil (L : Type*) [Field L] (imUnit : L) :
    Tensor3 L (Fin 2 × Fin 3) (Fin 2 × Fin 3) (Fin 2) :=
  fun p q k => if p.1 = q.1 then skewSinglePencil L imUnit p.2 q.2 k else 0

/-- Block-diagonal lift `I₂ ⊗ M` of a `3 × 3` matrix `M`. -/
def blockDiag2x3 {L : Type*} [Zero L] (M : Matrix (Fin 3) (Fin 3) L) :
    Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) L :=
  fun p q => if p.1 = q.1 then M p.2 q.2 else 0

lemma blockDiag2x3_mul {L : Type*} [Semiring L] (M N : Matrix (Fin 3) (Fin 3) L) :
    blockDiag2x3 M * blockDiag2x3 N = blockDiag2x3 (M * N) := by
  ext ⟨a, r⟩ ⟨c, s⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, blockDiag2x3]
  by_cases hac : a = c
  · subst hac
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hba; simp [Ne.symm hba]
    · intro ha; exact absurd (Finset.mem_univ a) ha
  · simp only [hac, ↓reduceIte]
    refine Finset.sum_eq_zero fun b _ => ?_
    by_cases hab : a = b
    · subst hab; simp [hac]
    · simp [hab]

lemma blockDiag2x3_one (L : Type*) [Semiring L] :
    blockDiag2x3 (1 : Matrix (Fin 3) (Fin 3) L) = 1 := by
  ext ⟨a, r⟩ ⟨c, s⟩
  simp only [blockDiag2x3, Matrix.one_apply, Prod.mk.injEq]
  by_cases hac : a = c
  · subst hac; simp
  · simp [hac]

theorem skewDoublePencil_equiv_kroneckerDouble_mode12 {L : Type*} [Field L]
    (h2 : (2 : L) ≠ 0) (imUnit : L) :
    ∃ (A Ai B Bi : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) L),
      A * Ai = 1 ∧ Ai * A = 1 ∧ B * Bi = 1 ∧ Bi * B = 1 ∧
      mapTensor A B (1 : Matrix (Fin 2) (Fin 2) L) (skewDoublePencil L imUnit) =
        kroneckerDoubleL1Pair L := by
  refine ⟨blockDiag2x3 (pencilCodInvMat L imUnit), blockDiag2x3 (pencilCodMat L imUnit),
    blockDiag2x3 (pencilDomMat L imUnit).transpose,
    blockDiag2x3 (pencilDomInvMat L imUnit).transpose, ?_, ?_, ?_, ?_, ?_⟩
  · rw [blockDiag2x3_mul, pencilCodInv_mul_Cod h2, blockDiag2x3_one]
  · rw [blockDiag2x3_mul, pencilCod_mul_CodInv h2, blockDiag2x3_one]
  · rw [blockDiag2x3_mul, ← Matrix.transpose_mul, pencilDomInv_mul_Dom h2,
      Matrix.transpose_one, blockDiag2x3_one]
  · rw [blockDiag2x3_mul, ← Matrix.transpose_mul, pencilDom_mul_DomInv h2,
      Matrix.transpose_one, blockDiag2x3_one]
  · funext ⟨a, r⟩ ⟨c, s⟩ k
    have hsingle := congrFun (congrFun (congrFun
      (mapTensor_skewSingle_eq_kroneckerL1Pair h2 imUnit) r) s) k
    simp only [mapTensor, Fintype.sum_prod_type, blockDiag2x3, skewDoublePencil,
      kroneckerDoubleL1Pair] at hsingle ⊢
    by_cases hac : a = c
    · subst hac
      simp only [↓reduceIte]
      rw [← hsingle]
      rw [Finset.sum_eq_single a]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_eq_single a]
        · simp
        · intro b _ hba; simp [Ne.symm hba]
        · intro ha; exact absurd (Finset.mem_univ a) ha
      · intro b _ hba; simp [Ne.symm hba]
      · intro ha; exact absurd (Finset.mem_univ a) ha
    · simp only [hac, ↓reduceIte]
      refine Finset.sum_eq_zero fun b₁ _ => ?_
      by_cases hab₁ : a = b₁
      · subst hab₁
        refine Finset.sum_eq_zero fun i _ => ?_
        refine Finset.sum_eq_zero fun b₂ _ => ?_
        by_cases hcb₂ : c = b₂
        · subst hcb₂; simp [hac]
        · simp [hcb₂]
      · simp [hab₁]

/-- Mode-3 contraction matrix `[[1, i, 0], [0, 0, 1]]` forming `Ψ_RCB = (M_X + i M_Y, M_Z)`. -/
def psiProjMat (L : Type*) [CommRing L] (imUnit : L) : Matrix (Fin 2) (Fin 3) L :=
  ![![1, imUnit, 0], ![0, 0, 1]]

lemma Psi_RCB_eq_mapTensor {L : Type*} [CommRing L] (b imUnit : L) :
    Psi_RCB L b imUnit = mapTensor 1 1 (psiProjMat L imUnit) (T_RCB L b) := by
  funext p q k
  have hcollapse :
      (∑ i : Fin 6, ∑ j : Fin 6, ∑ l : Fin 3,
        (if p = i then (1 : L) else 0) * (if q = j then (1 : L) else 0) *
          psiProjMat L imUnit k l * T_RCB L b i j l) =
      ∑ l : Fin 3, psiProjMat L imUnit k l * T_RCB L b p q l := by
    rw [Finset.sum_eq_single p]
    · rw [Finset.sum_eq_single q]
      · simp
      · intro j _ hj; simp [Ne.symm hj]
      · intro hq; exact absurd (Finset.mem_univ q) hq
    · intro i _ hi; simp [Ne.symm hi]
    · intro hp; exact absurd (Finset.mem_univ p) hp
  change Psi_RCB L b imUnit p q k =
    ∑ i, ∑ j, ∑ l, (1 : Matrix (Fin 6) (Fin 6) L) p i *
      (1 : Matrix (Fin 6) (Fin 6) L) q j * psiProjMat L imUnit k l * T_RCB L b i j l
  simp only [Matrix.one_apply]
  rw [hcollapse]
  fin_cases k <;> simp [Psi_RCB, Fin.sum_univ_three, psiProjMat]

/-- Mode-1&2 `GL₆ × GL₆` equivalence from `Ψ_RCB` to `kroneckerDoubleL1Pair` (mode 3 = `1`). -/
theorem Psi_RCB_equiv_kroneckerDouble_mode12 {L : Type*} [Field L]
    (h2 : (2 : L) ≠ 0) (h3 : (3 : L) ≠ 0) {b imUnit : L} (hb : b ≠ 0) (_hi : imUnit ^ 2 = -1) :
    ∃ (A : Matrix (Fin 2 × Fin 3) (Fin 6) L) (Ai : Matrix (Fin 6) (Fin 2 × Fin 3) L)
      (B : Matrix (Fin 2 × Fin 3) (Fin 6) L) (Bi : Matrix (Fin 6) (Fin 2 × Fin 3) L),
      A * Ai = 1 ∧ Ai * A = 1 ∧ B * Bi = 1 ∧ Bi * B = 1 ∧
      mapTensor A B (1 : Matrix (Fin 2) (Fin 2) L) (Psi_RCB L b imUnit) =
        kroneckerDoubleL1Pair L := by
  let M := (rcbMonomialFromUVMat L b).transpose
  let Mi := (rcbUVFromMonomialMat L b).transpose
  let S := symToDiagMat L
  let Si := -symToDiagMat L
  have hMMi : M * Mi = 1 := by
    dsimp [M, Mi]
    rw [← Matrix.transpose_mul, rcbUVFromMonomial_mul_inv h2 h3 hb, Matrix.transpose_one]
  have hMiM : Mi * M = 1 := by
    dsimp [M, Mi]
    rw [← Matrix.transpose_mul, rcbMonomialFromUV_mul_inv h2 h3 hb, Matrix.transpose_one]
  have hSSi : S * Si = 1 := symToDiagMat_mul_neg L
  have hSiS : Si * S = 1 := neg_mul_symToDiagMat L
  have hPsi_skew : mapTensor (S * M) M (1 : Matrix (Fin 2) (Fin 2) L) (Psi_RCB L b imUnit) =
      skewDoublePencil L imUnit := by
    have hTRCB : T_RCB L b = mapTensor Mi Mi (rcbSymToOutMat L) (symEps3 L) :=
      (mapTensor_UV_symEps3_eq_TRCB h2 b).symm
    calc mapTensor (S * M) M 1 (Psi_RCB L b imUnit)
        = mapTensor (S * M) M (psiProjMat L imUnit) (T_RCB L b) := by
            rw [Psi_RCB_eq_mapTensor, mapTensor_mapTensor, Matrix.mul_one, Matrix.mul_one,
              Matrix.one_mul]
      _ = mapTensor (S * (M * Mi)) (M * Mi) (psiProjMat L imUnit * rcbSymToOutMat L)
            (symEps3 L) := by
            rw [hTRCB, mapTensor_mapTensor, Matrix.mul_assoc]
      _ = mapTensor (1 : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) L)
            (1 : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) L)
            (psiProjMat L imUnit * rcbSymToOutMat L)
            (mapTensor S (1 : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) L)
              (1 : Matrix (Fin 3) (Fin 3) L) (symEps3 L)) := by
            rw [hMMi, Matrix.mul_one, mapTensor_mapTensor, Matrix.one_mul, Matrix.mul_one,
              Matrix.mul_one]
      _ = mapTensor (1 : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) L)
            (1 : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) L)
            (psiProjMat L imUnit * rcbSymToOutMat L) (I2_eps3 L) := by
            rw [mapTensor_symToDiagMat_symEps3]
      _ = skewDoublePencil L imUnit := by
            have hC : psiProjMat L imUnit * rcbSymToOutMat L =
                Matrix.of ![![-1, imUnit * (2 : L)⁻¹, 0], ![0, 0, (2 : L)⁻¹]] := by
              ext r s
              rw [Matrix.mul_apply]
              fin_cases r <;> fin_cases s <;>
                simp [Fin.sum_univ_three, psiProjMat, rcbSymToOutMat]
            rw [hC]
            funext ⟨a, i⟩ ⟨c, j⟩ k
            unfold mapTensor
            simp only [Matrix.one_apply, Matrix.of_apply]
            rw [Finset.sum_eq_single (a, i)]
            · rw [Finset.sum_eq_single (c, j)]
              · simp only [↓reduceIte, one_mul, I2_eps3, skewDoublePencil]
                by_cases hac : a = c
                · subst hac
                  fin_cases i <;> fin_cases j <;> fin_cases k <;>
                    simp [Fin.sum_univ_three, skewSinglePencil, eps3]
                · simp [hac]
              · intro q _ hq; simp [Ne.symm hq]
              · intro hc; exact absurd (Finset.mem_univ (c, j)) hc
            · intro p _ hp; simp [Ne.symm hp]
            · intro ha; exact absurd (Finset.mem_univ (a, i)) ha
  rcases skewDoublePencil_equiv_kroneckerDouble_mode12 h2 imUnit with
    ⟨A₂, Ai₂, B₂, Bi₂, hA₂, hAi₂, hB₂, hBi₂, hm₂⟩
  refine ⟨A₂ * (S * M), (Mi * Si) * Ai₂, B₂ * M, Mi * Bi₂, ?_, ?_, ?_, ?_, ?_⟩
  · calc (A₂ * (S * M)) * ((Mi * Si) * Ai₂)
        = A₂ * (S * (M * Mi) * Si) * Ai₂ := by simp [Matrix.mul_assoc]
      _ = 1 := by rw [hMMi, Matrix.mul_one, hSSi, Matrix.mul_one, hA₂]
  · calc ((Mi * Si) * Ai₂) * (A₂ * (S * M))
        = Mi * (Si * (Ai₂ * A₂) * S) * M := by simp [Matrix.mul_assoc]
      _ = 1 := by rw [hAi₂, Matrix.mul_one, hSiS, Matrix.mul_one, hMiM]
  · calc (B₂ * M) * (Mi * Bi₂) = B₂ * (M * Mi) * Bi₂ := by simp [Matrix.mul_assoc]
      _ = 1 := by rw [hMMi, Matrix.mul_one, hB₂]
  · calc (Mi * Bi₂) * (B₂ * M) = Mi * (Bi₂ * B₂) * M := by simp [Matrix.mul_assoc]
      _ = 1 := by rw [hBi₂, Matrix.mul_one, hMiM]
  · rw [← hm₂, ← hPsi_skew, mapTensor_mapTensor, Matrix.mul_one]

/-- **Theorem 1.2(2) (Kronecker canonical form of `Ψ_RCB`):**
Over any field `L` with `char L ≠ 2, 3`, `b ≠ 0`, and `imUnit² = -1`,
`Ψ_RCB` is `GL`-equivalent over `L` to `L₁ ⊕ L₁ᵀ ⊕ L₁ ⊕ L₁ᵀ`. -/
theorem Psi_RCB_equiv_kroneckerDouble {L : Type*} [Field L]
    (h2 : (2 : L) ≠ 0) (h3 : (3 : L) ≠ 0) {b imUnit : L} (hb : b ≠ 0) (hi : imUnit ^ 2 = -1) :
    TensorEquiv (Psi_RCB L b imUnit) (kroneckerDoubleL1Pair L) := by
  rcases Psi_RCB_equiv_kroneckerDouble_mode12 h2 h3 hb hi with
    ⟨A, Ai, B, Bi, hA, hAi, hB, hBi, hm⟩
  exact ⟨A, Ai, B, Bi, 1, 1, hA, hAi, hB, hBi,
    Matrix.mul_one (1 : Matrix (Fin 2) (Fin 2) L),
    Matrix.mul_one (1 : Matrix (Fin 2) (Fin 2) L), hm⟩

/-! ### Section 3b: Constant Rank 4, Double-Quotient Rank 8, Border Rank 6, and `K(i)` -/

/-- Projective slice combination `s M₀ + t M₁` of a `2`-slice tensor `T`. -/
def pencilSlice {L I J : Type*} [CommRing L] (T : Tensor3 L I J (Fin 2)) (s t : L) :
    Matrix I J L :=
  fun i j => s * T i j 0 + t * T i j 1

lemma matrix_rank_mul_left_le {F m' m n : Type*} [Field F] [Fintype m'] [Fintype m] [Fintype n]
    (A : Matrix m' m F) (M : Matrix m n F) : (A * M).rank ≤ M.rank := by
  have hsub : LinearMap.range (A * M).mulVecLin ≤
      (LinearMap.range M.mulVecLin).map A.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    refine ⟨M.mulVecLin v, LinearMap.mem_range_self _ v, ?_⟩
    simp [Matrix.mulVec_mulVec]
  exact le_trans (Submodule.finrank_mono hsub) (Submodule.finrank_map_le _ _)

lemma matrix_rank_mul_right_le {F m n n' : Type*} [Field F] [Fintype m] [Fintype n] [Fintype n']
    (M : Matrix m n F) (B : Matrix n n' F) : (M * B).rank ≤ M.rank := by
  have hsub : LinearMap.range (M * B).mulVecLin ≤ LinearMap.range M.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    refine ⟨B.mulVecLin v, ?_⟩
    simp [Matrix.mulVec_mulVec]
  exact Submodule.finrank_mono hsub

lemma matrix_rank_le_card_col {F m n : Type*} [Field F] [Fintype m] [Fintype n]
    (M : Matrix m n F) : M.rank ≤ Fintype.card n := by
  change Module.finrank F (LinearMap.range M.mulVecLin) ≤ Fintype.card n
  simpa [Module.finrank_pi] using LinearMap.finrank_range_le M.mulVecLin

lemma matrix_rank_le_one_of_outer {F m n : Type*} [Field F] [Fintype m] [Fintype n]
    (f : m → F) (g : n → F) :
    (Matrix.of fun p q => f p * g q).rank ≤ 1 := by
  let A : Matrix m (Fin 1) F := fun p _ => f p
  let B : Matrix (Fin 1) n F := fun _ q => g q
  have hAB : (Matrix.of fun p q => f p * g q) = A * B := by
    ext p q
    rw [Matrix.mul_apply]
    simp [A, B]
  rw [hAB]
  exact le_trans (matrix_rank_mul_right_le A B)
    (by simpa using matrix_rank_le_card_col A)

/-- Constant rank `4` of `s K₁ + t K₂` for `(s, t) ≠ (0, 0)` on `L₁ ⊕ L₁ᵀ ⊕ L₁ ⊕ L₁ᵀ`. -/
theorem kroneckerDoubleL1Pair_pencil_rank_eq_four {L : Type*} [Field L] {s t : L}
    (hst : s ≠ 0 ∨ t ≠ 0) :
    (pencilSlice (kroneckerDoubleL1Pair L) s t).rank = 4 := by
  let M := pencilSlice (kroneckerDoubleL1Pair L) s t
  rcases hst with hs | ht
  · apply le_antisymm
    · let U₄ : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 2) L :=
        fun ⟨a, i⟩ ⟨b, r⟩ =>
          if a = b then (![![1, 0], ![0, 1], ![0, t * s⁻¹]] i r) else 0
      let V₄ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 3) L :=
        fun ⟨b, r⟩ ⟨c, j⟩ =>
          if b = c then (![![s, t, 0], ![0, 0, s]] r j) else 0
      have hM : M = U₄ * V₄ := by
        ext ⟨a, i⟩ ⟨c, j⟩
        rw [Matrix.mul_apply]
        fin_cases a <;> fin_cases c <;> fin_cases i <;> fin_cases j <;>
          simp [M, U₄, V₄, Fintype.sum_prod_type, Fin.sum_univ_two, pencilSlice,
            kroneckerDoubleL1Pair, kroneckerL1Pair, hs]
      change M.rank ≤ 4
      rw [hM]
      exact le_trans (matrix_rank_mul_right_le U₄ V₄)
        (by simpa using matrix_rank_le_card_col U₄)
    · let rowSub : Fin 2 × Fin 2 → Fin 2 × Fin 3 :=
        fun ⟨a, i⟩ => (a, if i = 0 then 0 else 1)
      let colSub : Fin 2 × Fin 2 → Fin 2 × Fin 3 :=
        fun ⟨a, j⟩ => (a, if j = 0 then 0 else 2)
      have hsub : M.submatrix rowSub colSub = s • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) L) := by
        ext ⟨a, i⟩ ⟨c, j⟩
        fin_cases a <;> fin_cases c <;> fin_cases i <;> fin_cases j <;>
          simp [M, rowSub, colSub, pencilSlice, kroneckerDoubleL1Pair, kroneckerL1Pair]
      have hdet : (M.submatrix rowSub colSub).det ≠ 0 := by
        rw [hsub, Matrix.det_smul, Matrix.det_one, mul_one]
        exact pow_ne_zero _ hs
      have h4 : 4 = (M.submatrix rowSub colSub).rank := by
        rw [Matrix.rank_of_det_ne_zero hdet]; simp
      rw [h4]
      exact Matrix.rank_submatrix_le M rowSub colSub
  · apply le_antisymm
    · let U₄ : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 2) L :=
        fun ⟨a, i⟩ ⟨b, r⟩ =>
          if a = b then (![![1, 0], ![0, s * t⁻¹], ![0, 1]] i r) else 0
      let V₄ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 3) L :=
        fun ⟨b, r⟩ ⟨c, j⟩ =>
          if b = c then (![![s, t, 0], ![0, 0, t]] r j) else 0
      have hM : M = U₄ * V₄ := by
        ext ⟨a, i⟩ ⟨c, j⟩
        rw [Matrix.mul_apply]
        fin_cases a <;> fin_cases c <;> fin_cases i <;> fin_cases j <;>
          simp [M, U₄, V₄, Fintype.sum_prod_type, Fin.sum_univ_two, pencilSlice,
            kroneckerDoubleL1Pair, kroneckerL1Pair, ht]
      change M.rank ≤ 4
      rw [hM]
      exact le_trans (matrix_rank_mul_right_le U₄ V₄)
        (by simpa using matrix_rank_le_card_col U₄)
    · let rowSub : Fin 2 × Fin 2 → Fin 2 × Fin 3 :=
        fun ⟨a, i⟩ => (a, if i = 0 then 0 else 2)
      let colSub : Fin 2 × Fin 2 → Fin 2 × Fin 3 :=
        fun ⟨a, j⟩ => (a, if j = 0 then 1 else 2)
      have hsub : M.submatrix rowSub colSub = t • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) L) := by
        ext ⟨a, i⟩ ⟨c, j⟩
        fin_cases a <;> fin_cases c <;> fin_cases i <;> fin_cases j <;>
          simp [M, rowSub, colSub, pencilSlice, kroneckerDoubleL1Pair, kroneckerL1Pair]
      have hdet : (M.submatrix rowSub colSub).det ≠ 0 := by
        rw [hsub, Matrix.det_smul, Matrix.det_one, mul_one]
        exact pow_ne_zero _ ht
      have h4 : 4 = (M.submatrix rowSub colSub).rank := by
        rw [Matrix.rank_of_det_ne_zero hdet]; simp
      rw [h4]
      exact Matrix.rank_submatrix_le M rowSub colSub

/-- **Theorem 1.2(2) (Constant rank `4` of `Ψ_RCB` on `L² \ {(0, 0)}`):**
For all `(s, t) ≠ (0, 0)`, `s(M_X + i M_Y) + t M_Z` has matrix rank `4`. -/
theorem Psi_RCB_pencil_rank_eq_four {L : Type*} [Field L]
    (h2 : (2 : L) ≠ 0) (h3 : (3 : L) ≠ 0) {b imUnit : L} (hb : b ≠ 0) (hi : imUnit ^ 2 = -1)
    {s t : L} (hst : (s, t) ≠ (0, 0)) :
    (pencilSlice (Psi_RCB L b imUnit) s t).rank = 4 := by
  have hor : s ≠ 0 ∨ t ≠ 0 := by
    by_cases hs : s = 0
    · right
      intro ht
      exact hst (Prod.ext hs ht)
    · exact Or.inl hs
  rcases Psi_RCB_equiv_kroneckerDouble_mode12 h2 h3 hb hi with
    ⟨A, Ai, B, Bi, _, hAi, _, hBi, hm⟩
  let M_psi := pencilSlice (Psi_RCB L b imUnit) s t
  let M_kron := pencilSlice (kroneckerDoubleL1Pair L) s t
  have hrel : A * M_psi * B.transpose = M_kron := by
    ext p q
    have hm0 := congrFun (congrFun (congrFun hm p) q) 0
    have hm1 := congrFun (congrFun (congrFun hm p) q) 1
    simp only [M_kron, pencilSlice, ← hm0, ← hm1, mapTensor, Fin.sum_univ_two,
      Matrix.one_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, mul_one, mul_zero,
      zero_mul, add_zero, zero_add]
    simp only [M_psi, pencilSlice, Matrix.mul_apply, Matrix.transpose_apply,
      Finset.mul_sum, Finset.sum_mul, mul_add, add_mul, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hback : M_psi = Ai * M_kron * Bi.transpose := by
    calc M_psi = (Ai * A) * M_psi * (Bi * B).transpose := by
            rw [hAi, hBi, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
      _ = Ai * (A * M_psi * B.transpose) * Bi.transpose := by
            rw [Matrix.transpose_mul]; simp [Matrix.mul_assoc]
      _ = Ai * M_kron * Bi.transpose := by rw [hrel]
  have hle1 : M_kron.rank ≤ M_psi.rank := by
    rw [← hrel]
    exact le_trans (matrix_rank_mul_right_le _ _) (matrix_rank_mul_left_le _ _)
  have hle2 : M_psi.rank ≤ M_kron.rank := by
    conv_lhs => rw [hback]
    exact le_trans (matrix_rank_mul_right_le _ _) (matrix_rank_mul_left_le _ _)
  rw [le_antisymm hle2 hle1]
  exact kroneckerDoubleL1Pair_pencil_rank_eq_four hor

lemma exists_pair_det2_ne_zero_of_id_sum {L α : Type*} [Field L]
    (S : Finset α) (x y : α → Fin 2 → L)
    (hid : ∀ a b : Fin 2, (if a = b then (1 : L) else 0) = ∑ m ∈ S, x m a * y m b) :
    ∃ m₁ ∈ S, ∃ m₂ ∈ S, m₁ ≠ m₂ ∧ x m₁ 0 * x m₂ 1 - x m₁ 1 * x m₂ 0 ≠ 0 := by
  by_contra hno
  have hall : ∀ m₁ ∈ S, ∀ m₂ ∈ S, x m₁ 0 * x m₂ 1 = x m₁ 1 * x m₂ 0 := by
    intro m₁ hm₁ m₂ hm₂
    by_cases h12 : m₁ = m₂
    · subst h12; ring
    · by_contra hneq
      exact hno ⟨m₁, hm₁, m₂, hm₂, h12, sub_ne_zero.mpr hneq⟩
  have h00 : (∑ m ∈ S, x m 0 * y m 0) ≠ 0 := by
    rw [← hid 0 0]; simp
  obtain ⟨m₁, hm₁, hxm₁⟩ := Finset.exists_ne_zero_of_sum_ne_zero h00
  have hx1_ne : x m₁ 0 ≠ 0 := fun h0 => hxm₁ (by simp [h0])
  let c : L := x m₁ 1 * (x m₁ 0)⁻¹
  have hrel : ∀ n ∈ S, x n 1 = c * x n 0 := by
    intro n hn
    have hmul := hall m₁ hm₁ n hn
    calc x n 1 = (x m₁ 0 * x n 1) * (x m₁ 0)⁻¹ := by field_simp [hx1_ne]
      _ = c * x n 0 := by rw [hmul]; dsimp [c]; ring
  have h11 : (1 : L) = ∑ n ∈ S, x n 1 * y n 1 := by simpa using hid 1 1
  have h01 : (0 : L) = ∑ n ∈ S, x n 0 * y n 1 := by simpa using hid 0 1
  have h1_eq_0 : (1 : L) = 0 := by
    calc (1 : L) = ∑ n ∈ S, (c * x n 0) * y n 1 := by
            rw [h11]; refine Finset.sum_congr rfl fun n hn => by rw [hrel n hn]
      _ = c * ∑ n ∈ S, x n 0 * y n 1 := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun n _ => by ring
      _ = 0 := by rw [← h01, mul_zero]
  exact one_ne_zero h1_eq_0

/-- Linear elimination of two coordinates `p₀, p₁ : I` using a `2 × 2` nonsingular pair. -/
def elimPair {L I : Type*} [Field L] (p₀ p₁ : I) (u₁ u₂ : I → L) (f : I → L) : I → L :=
  fun p =>
    f p -
      (u₂ p₁ * f p₀ - u₂ p₀ * f p₁) * (u₁ p₀ * u₂ p₁ - u₁ p₁ * u₂ p₀)⁻¹ * u₁ p -
      (-u₁ p₁ * f p₀ + u₁ p₀ * f p₁) * (u₁ p₀ * u₂ p₁ - u₁ p₁ * u₂ p₀)⁻¹ * u₂ p

lemma elimPair_of_zero {L I : Type*} [Field L] (p₀ p₁ : I) (u₁ u₂ f : I → L)
    (h0 : f p₀ = 0) (h1 : f p₁ = 0) (p : I) :
    elimPair p₀ p₁ u₁ u₂ f p = f p := by
  simp [elimPair, h0, h1]

lemma elimPair_first {L I : Type*} [Field L] (p₀ p₁ : I) (u₁ u₂ : I → L)
    (hΔ : u₁ p₀ * u₂ p₁ - u₁ p₁ * u₂ p₀ ≠ 0) (p : I) :
    elimPair p₀ p₁ u₁ u₂ u₁ p = 0 := by
  unfold elimPair
  calc u₁ p - (u₂ p₁ * u₁ p₀ - u₂ p₀ * u₁ p₁) * (u₁ p₀ * u₂ p₁ - u₁ p₁ * u₂ p₀)⁻¹ * u₁ p -
        (-u₁ p₁ * u₁ p₀ + u₁ p₀ * u₁ p₁) * (u₁ p₀ * u₂ p₁ - u₁ p₁ * u₂ p₀)⁻¹ * u₂ p
      = u₁ p * (1 - (u₁ p₀ * u₂ p₁ - u₁ p₁ * u₂ p₀) * (u₁ p₀ * u₂ p₁ - u₁ p₁ * u₂ p₀)⁻¹) := by
          ring
    _ = 0 := by rw [mul_inv_cancel₀ hΔ, sub_self, mul_zero]

lemma elimPair_second {L I : Type*} [Field L] (p₀ p₁ : I) (u₁ u₂ : I → L)
    (hΔ : u₁ p₀ * u₂ p₁ - u₁ p₁ * u₂ p₀ ≠ 0) (p : I) :
    elimPair p₀ p₁ u₁ u₂ u₂ p = 0 := by
  unfold elimPair
  calc u₂ p - (u₂ p₁ * u₂ p₀ - u₂ p₀ * u₂ p₁) * (u₁ p₀ * u₂ p₁ - u₁ p₁ * u₂ p₀)⁻¹ * u₁ p -
        (-u₁ p₁ * u₂ p₀ + u₁ p₀ * u₂ p₁) * (u₁ p₀ * u₂ p₁ - u₁ p₁ * u₂ p₀)⁻¹ * u₂ p
      = u₂ p * (1 - (u₁ p₀ * u₂ p₁ - u₁ p₁ * u₂ p₀) * (u₁ p₀ * u₂ p₁ - u₁ p₁ * u₂ p₀)⁻¹) := by
          ring
    _ = 0 := by rw [mul_inv_cancel₀ hΔ, sub_self, mul_zero]

lemma elimPair_sum_mul {L I α : Type*} [Field L] (p₀ p₁ : I) (u₁ u₂ : I → L)
    (S : Finset α) (g : α → I → L) (c : α → L) (p : I) :
    elimPair p₀ p₁ u₁ u₂ (fun x => ∑ m ∈ S, g m x * c m) p =
      ∑ m ∈ S, elimPair p₀ p₁ u₁ u₂ (g m) p * c m := by
  unfold elimPair
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => by ring

/-- **Double-quotient substitution lower bound (`rank ≥ 8`):**
Over EVERY field `L` (of arbitrary characteristic), `L₁ ⊕ L₁ᵀ ⊕ L₁ ⊕ L₁ᵀ` has tensor rank at least `8`. -/
theorem kroneckerDoubleL1Pair_rank_ge_eight {L : Type*} [Field L] {r : ℕ}
    (hr : HasTensorRankLe (kroneckerDoubleL1Pair L) r) : 8 ≤ r := by
  classical
  rcases hr with ⟨u, v, w, hT⟩
  have hidA : ∀ a b : Fin 2, (if a = b then (1 : L) else 0) =
      ∑ m : Fin r, u m (a, 2) * (v m (b, 2) * w m 1) := by
    intro a b
    have h := hT (a, 2) (b, 2) 1
    have hval : kroneckerDoubleL1Pair L (a, 2) (b, 2) 1 = if a = b then 1 else 0 := by
      fin_cases a <;> fin_cases b <;> rfl
    rw [← hval, h]
    exact Finset.sum_congr rfl fun m _ => by ring
  obtain ⟨m₁, _, m₂, _, hm₁₂, hΔu⟩ :=
    exists_pair_det2_ne_zero_of_id_sum Finset.univ
      (fun m a => u m (a, 2)) (fun m b => v m (b, 2) * w m 1) hidA
  let u' : Fin r → Fin 2 × Fin 3 → L :=
    fun m => elimPair (0, 2) (1, 2) (u m₁) (u m₂) (u m)
  let S₁ : Finset (Fin r) := (Finset.univ.erase m₁).erase m₂
  have hm₂_mem : m₂ ∈ (Finset.univ : Finset (Fin r)).erase m₁ :=
    Finset.mem_erase.mpr ⟨hm₁₂.symm, Finset.mem_univ m₂⟩
  have hr2 : 2 ≤ r := by
    have h0a : 0 < (Finset.univ : Finset (Fin r)).card :=
      Finset.card_pos.mpr ⟨m₁, Finset.mem_univ m₁⟩
    have h0b : 0 < ((Finset.univ : Finset (Fin r)).erase m₁).card :=
      Finset.card_pos.mpr ⟨m₂, hm₂_mem⟩
    have h1 := Finset.card_erase_of_mem (Finset.mem_univ m₁)
    simp only [Finset.card_univ, Fintype.card_fin] at h0a h1
    omega
  have hcardS₁ : S₁.card = r - 2 := by
    dsimp [S₁]
    rw [Finset.card_erase_of_mem hm₂_mem, Finset.card_erase_of_mem (Finset.mem_univ m₁),
      Finset.card_univ, Fintype.card_fin]
    omega
  have hsum_to_S₁ : ∀ (c : Fin r → L) (p : Fin 2 × Fin 3),
      ∑ m : Fin r, u' m p * c m = ∑ m ∈ S₁, u' m p * c m := by
    intro c p
    rw [← Finset.sum_subset (Finset.subset_univ S₁)]
    intro m _ hm
    have hm_eq : m = m₁ ∨ m = m₂ := by
      simp only [S₁, Finset.mem_erase, Finset.mem_univ, and_true, not_and_or, not_not] at hm
      tauto
    rcases hm_eq with rfl | rfl
    · simp [u', elimPair_first _ _ _ _ hΔu]
    · simp [u', elimPair_second _ _ _ _ hΔu]
  have hA_S₁ : ∀ p q : Fin 2 × Fin 3,
      kroneckerDoubleL1Pair L p q 0 = ∑ m ∈ S₁, u' m p * v m q * w m 0 := by
    intro p q
    have h0 : kroneckerDoubleL1Pair L (0, 2) q 0 = 0 := by
      rcases q with ⟨b, j⟩; fin_cases b <;> fin_cases j <;> rfl
    have h1 : kroneckerDoubleL1Pair L (1, 2) q 0 = 0 := by
      rcases q with ⟨b, j⟩; fin_cases b <;> fin_cases j <;> rfl
    calc kroneckerDoubleL1Pair L p q 0
        = elimPair (0, 2) (1, 2) (u m₁) (u m₂) (fun x => kroneckerDoubleL1Pair L x q 0) p :=
            (elimPair_of_zero (0, 2) (1, 2) (u m₁) (u m₂)
              (fun x => kroneckerDoubleL1Pair L x q 0) h0 h1 p).symm
      _ = elimPair (0, 2) (1, 2) (u m₁) (u m₂)
            (fun x => ∑ m : Fin r, u m x * (v m q * w m 0)) p := by
            congr 1; funext x; rw [hT x q 0]
            exact Finset.sum_congr rfl fun m _ => by ring
      _ = ∑ m : Fin r, u' m p * (v m q * w m 0) :=
            elimPair_sum_mul _ _ _ _ Finset.univ u (fun m => v m q * w m 0) p
      _ = ∑ m ∈ S₁, u' m p * v m q * w m 0 := by
            rw [hsum_to_S₁]; exact Finset.sum_congr rfl fun m _ => by ring
  have hidB : ∀ b a : Fin 2, (if b = a then (1 : L) else 0) =
      ∑ m ∈ S₁, v m (b, 1) * (u' m (a, 0) * w m 1) := by
    intro b a
    have h0 : kroneckerDoubleL1Pair L (0, 2) (b, 1) 1 = 0 := by fin_cases b <;> rfl
    have h1 : kroneckerDoubleL1Pair L (1, 2) (b, 1) 1 = 0 := by fin_cases b <;> rfl
    have hval : kroneckerDoubleL1Pair L (a, 0) (b, 1) 1 = if b = a then 1 else 0 := by
      fin_cases a <;> fin_cases b <;> rfl
    calc (if b = a then (1 : L) else 0)
        = kroneckerDoubleL1Pair L (a, 0) (b, 1) 1 := hval.symm
      _ = elimPair (0, 2) (1, 2) (u m₁) (u m₂)
            (fun x => kroneckerDoubleL1Pair L x (b, 1) 1) (a, 0) :=
            (elimPair_of_zero (0, 2) (1, 2) (u m₁) (u m₂)
              (fun x => kroneckerDoubleL1Pair L x (b, 1) 1) h0 h1 (a, 0)).symm
      _ = elimPair (0, 2) (1, 2) (u m₁) (u m₂)
            (fun x => ∑ m : Fin r, u m x * (v m (b, 1) * w m 1)) (a, 0) := by
            congr 1; funext x; rw [hT x (b, 1) 1]
            exact Finset.sum_congr rfl fun m _ => by ring
      _ = ∑ m : Fin r, u' m (a, 0) * (v m (b, 1) * w m 1) :=
            elimPair_sum_mul _ _ _ _ Finset.univ u (fun m => v m (b, 1) * w m 1) (a, 0)
      _ = ∑ m ∈ S₁, v m (b, 1) * (u' m (a, 0) * w m 1) := by
            rw [hsum_to_S₁]; exact Finset.sum_congr rfl fun m _ => by ring
  obtain ⟨m₃, hm₃, m₄, hm₄, hm₃₄, hΔv⟩ :=
    exists_pair_det2_ne_zero_of_id_sum S₁
      (fun m b => v m (b, 1)) (fun m a => u' m (a, 0) * w m 1) hidB
  let v' : Fin r → Fin 2 × Fin 3 → L :=
    fun m => elimPair (0, 1) (1, 1) (v m₃) (v m₄) (v m)
  let S₂ : Finset (Fin r) := (S₁.erase m₃).erase m₄
  have hm₄_mem : m₄ ∈ S₁.erase m₃ := Finset.mem_erase.mpr ⟨hm₃₄.symm, hm₄⟩
  have hS₁_ge2 : 2 ≤ S₁.card := by
    have h0a : 0 < S₁.card := Finset.card_pos.mpr ⟨m₃, hm₃⟩
    have h0b : 0 < (S₁.erase m₃).card := Finset.card_pos.mpr ⟨m₄, hm₄_mem⟩
    have h1 := Finset.card_erase_of_mem hm₃
    omega
  have hr4 : 4 ≤ r := by omega
  have hcardS₂ : S₂.card = r - 4 := by
    dsimp [S₂]
    rw [Finset.card_erase_of_mem hm₄_mem, Finset.card_erase_of_mem hm₃, hcardS₁]
    omega
  have hA_S₂ : ∀ p q : Fin 2 × Fin 3,
      kroneckerDoubleL1Pair L p q 0 = ∑ m ∈ S₂, u' m p * v' m q * w m 0 := by
    intro p q
    have h0 : kroneckerDoubleL1Pair L p (0, 1) 0 = 0 := by
      rcases p with ⟨a, i⟩; fin_cases a <;> fin_cases i <;> rfl
    have h1 : kroneckerDoubleL1Pair L p (1, 1) 0 = 0 := by
      rcases p with ⟨a, i⟩; fin_cases a <;> fin_cases i <;> rfl
    calc kroneckerDoubleL1Pair L p q 0
        = elimPair (0, 1) (1, 1) (v m₃) (v m₄) (fun y => kroneckerDoubleL1Pair L p y 0) q :=
            (elimPair_of_zero (0, 1) (1, 1) (v m₃) (v m₄)
              (fun y => kroneckerDoubleL1Pair L p y 0) h0 h1 q).symm
      _ = elimPair (0, 1) (1, 1) (v m₃) (v m₄)
            (fun y => ∑ m ∈ S₁, v m y * (u' m p * w m 0)) q := by
            congr 1; funext y; rw [hA_S₁ p y]
            exact Finset.sum_congr rfl fun m _ => by ring
      _ = ∑ m ∈ S₁, v' m q * (u' m p * w m 0) :=
            elimPair_sum_mul _ _ _ _ S₁ v (fun m => u' m p * w m 0) q
      _ = ∑ m ∈ S₂, u' m p * v' m q * w m 0 := by
            have hsub : S₂ ⊆ S₁ :=
              Finset.Subset.trans (Finset.erase_subset _ _) (Finset.erase_subset _ _)
            rw [← Finset.sum_subset hsub]
            · exact Finset.sum_congr rfl fun m _ => by ring
            · intro m _ hmnot
              have hm_eq : m = m₃ ∨ m = m₄ := by
                simp only [S₂, Finset.mem_erase, not_and_or, not_not] at hmnot
                tauto
              rcases hm_eq with rfl | rfl
              · simp [v', elimPair_first _ _ _ _ hΔv]
              · simp [v', elimPair_second _ _ _ _ hΔv]
  let M_A : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) L :=
    fun p q => kroneckerDoubleL1Pair L p q 0
  let rowSub : Fin 2 × Fin 2 → Fin 2 × Fin 3 :=
    fun ⟨a, i⟩ => (a, if i = 0 then 0 else 1)
  let colSub : Fin 2 × Fin 2 → Fin 2 × Fin 3 :=
    fun ⟨a, j⟩ => (a, if j = 0 then 0 else 2)
  have hsub_one : M_A.submatrix rowSub colSub = 1 := by
    ext ⟨a, i⟩ ⟨b, j⟩
    fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;> rfl
  have hdet_ne : (M_A.submatrix rowSub colSub).det ≠ 0 := by
    rw [hsub_one, Matrix.det_one]; exact one_ne_zero
  let eS₂ : Fin S₂.card ≃ S₂ := S₂.equivFin.symm
  let R_mat : Fin S₂.card → Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) L :=
    fun t p q => (u' (eS₂ t).1 p * w (eS₂ t).1 0) * v' (eS₂ t).1 q
  have hMA_sum : M_A = ∑ t : Fin S₂.card, R_mat t := by
    ext p q
    change kroneckerDoubleL1Pair L p q 0 = (∑ t : Fin S₂.card, R_mat t) p q
    rw [Matrix.sum_apply, hA_S₂ p q, ← Finset.sum_attach S₂, ← Finset.univ_eq_attach]
    refine (Fintype.sum_equiv eS₂.symm (fun x : S₂ => u' x.1 p * v' x.1 q * w x.1 0)
      (fun t : Fin S₂.card => R_mat t p q) fun x => ?_)
    dsimp [R_mat]
    simp only [Equiv.apply_symm_apply]
    ring
  have hcard4 : 4 ≤ 1 * S₂.card := by
    simpa using matrix_card_le_sum_rank M_A rowSub colSub hdet_ne R_mat hMA_sum 1
      (fun t => matrix_rank_le_one_of_outer _ _)
  omega

/-- **Theorem 1.2(2) (Rank lower bound `≥ 8` for `Ψ_RCB`):**
Over every field `L` with `char L ≠ 2, 3`, `b ≠ 0`, and `imUnit² = -1`,
every rank decomposition of `Ψ_RCB` has at least `8` terms (`¬ HasTensorRankLe Ψ_RCB 7`). -/
theorem Psi_RCB_rank_ge_eight {L : Type*} [Field L]
    (h2 : (2 : L) ≠ 0) (h3 : (3 : L) ≠ 0) {b imUnit : L} (hb : b ≠ 0) (hi : imUnit ^ 2 = -1)
    {r : ℕ} (hr : HasTensorRankLe (Psi_RCB L b imUnit) r) : 8 ≤ r := by
  have heq := Psi_RCB_equiv_kroneckerDouble h2 h3 hb hi
  exact kroneckerDoubleL1Pair_rank_ge_eight ((heq.hasTensorRankLe_iff r).mp hr)

theorem Psi_RCB_not_hasTensorRankLe_seven {L : Type*} [Field L]
    (h2 : (2 : L) ≠ 0) (h3 : (3 : L) ≠ 0) {b imUnit : L} (hb : b ≠ 0) (hi : imUnit ^ 2 = -1) :
    ¬ HasTensorRankLe (Psi_RCB L b imUnit) 7 := by
  intro hr
  have h8 := Psi_RCB_rank_ge_eight h2 h3 hb hi hr
  omega

/-- Explicit `8`-term rank decomposition of `kroneckerDoubleL1Pair L` over any commutative ring `L`. -/
theorem kroneckerDoubleL1Pair_hasTensorRankLe_eight (L : Type*) [CommRing L] :
    HasTensorRankLe (kroneckerDoubleL1Pair L) 8 := by
  let terms : Fin 8 → (Fin 2 × Fin 3) × (Fin 2 × Fin 3) × Fin 2 :=
    ![((0, 0), (0, 0), 0), ((0, 1), (0, 2), 0), ((0, 0), (0, 1), 1), ((0, 2), (0, 2), 1),
      ((1, 0), (1, 0), 0), ((1, 1), (1, 2), 0), ((1, 0), (1, 1), 1), ((1, 2), (1, 2), 1)]
  refine ⟨fun t p => if p = (terms t).1 then 1 else 0,
    fun t q => if q = (terms t).2.1 then 1 else 0,
    fun t k => if k = (terms t).2.2 then 1 else 0, ?_⟩
  rintro ⟨a, i⟩ ⟨c, j⟩ k
  fin_cases a <;> fin_cases c <;> fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [Fin.sum_univ_eight, terms, kroneckerDoubleL1Pair, kroneckerL1Pair]

/-- **Theorem 1.2(2) (Explicit `8`-term upper bound for `Ψ_RCB`):**
Over every field `L` with `char L ≠ 2, 3`, `b ≠ 0`, and `imUnit² = -1`, `HasTensorRankLe Ψ_RCB 8`. -/
theorem Psi_RCB_hasTensorRankLe_eight {L : Type*} [Field L]
    (h2 : (2 : L) ≠ 0) (h3 : (3 : L) ≠ 0) {b imUnit : L} (hb : b ≠ 0) (hi : imUnit ^ 2 = -1) :
    HasTensorRankLe (Psi_RCB L b imUnit) 8 :=
  ((Psi_RCB_equiv_kroneckerDouble h2 h3 hb hi).hasTensorRankLe_iff 8).mpr
    (kroneckerDoubleL1Pair_hasTensorRankLe_eight L)

/-- Mode-1 flattening coefficient array for `kroneckerDoubleL1Pair`. -/
def mode1FlatteningCoeff (L : Type*) [CommRing L] :
    (Fin 2 × Fin 3) → ((Fin 2 × Fin 3) × Fin 2) →
      (Fin 2 × Fin 3) → (Fin 2 × Fin 3) → Fin 2 → L :=
  fun p qk i j l => if p = i ∧ qk.1 = j ∧ qk.2 = l then 1 else 0

/-- **Mode-1 flattening formal border-rank lower bound (`brk ≥ 6`):**
Over EVERY field `L`, `kroneckerDoubleL1Pair L` has formal border rank at least `6`. -/
theorem kroneckerDoubleL1Pair_borderRank_ge_six {L : Type*} [Field L] {r : ℕ}
    (hr : HasFormalBorderRankLe (kroneckerDoubleL1Pair L) r) : 6 ≤ r := by
  have hκ : ∀ (u : Fin 2 × Fin 3 → RatFunc L) (v : Fin 2 × Fin 3 → RatFunc L)
      (w : Fin 2 → RatFunc L),
      (linearFlattening (algebraMap L (RatFunc L)) (mode1FlatteningCoeff L)
        (rankOneTensor u v w)).rank ≤ 1 := by
    intro u v w
    have heq : linearFlattening (algebraMap L (RatFunc L)) (mode1FlatteningCoeff L)
        (rankOneTensor u v w) =
        Matrix.of (fun p (qk : (Fin 2 × Fin 3) × Fin 2) => u p * (v qk.1 * w qk.2)) := by
      ext p ⟨q, k⟩
      simp only [linearFlattening, mode1FlatteningCoeff, rankOneTensor, Matrix.of_apply]
      rw [Finset.sum_eq_single p]
      · rw [Finset.sum_eq_single q]
        · rw [Finset.sum_eq_single k]
          · simp [mul_assoc]
          · intro l _ hlk; simp [Ne.symm hlk]
          · intro hk; exact absurd (Finset.mem_univ k) hk
        · intro j _ hjq; simp [Ne.symm hjq]
        · intro hq; exact absurd (Finset.mem_univ q) hq
      · intro i _ hip; simp [Ne.symm hip]
      · intro hp; exact absurd (Finset.mem_univ p) hp
    rw [heq]
    exact matrix_rank_le_one_of_outer _ _
  let colSub : Fin 2 × Fin 3 → (Fin 2 × Fin 3) × Fin 2 :=
    fun ⟨a, i⟩ =>
      match i.val with
      | 0 => ((a, 0), 0)
      | 1 => ((a, 2), 0)
      | _ => ((a, 2), 1)
  have hsub : (linearFlattening (RingHom.id L) (mode1FlatteningCoeff L)
      (kroneckerDoubleL1Pair L)).submatrix id colSub = 1 := by
    ext ⟨a, i⟩ ⟨c, j⟩
    simp only [Matrix.submatrix_apply, id_eq, linearFlattening, mode1FlatteningCoeff,
      RingHom.id_apply, Matrix.one_apply, Prod.mk.injEq]
    rw [Finset.sum_eq_single (a, i)]
    · rw [Finset.sum_eq_single (colSub (c, j)).1]
      · rw [Finset.sum_eq_single (colSub (c, j)).2]
        · fin_cases a <;> fin_cases c <;> fin_cases i <;> fin_cases j <;>
            simp [colSub, kroneckerDoubleL1Pair, kroneckerL1Pair]
        · intro l _ hlk; simp [Ne.symm hlk]
        · intro hk; exact absurd (Finset.mem_univ _) hk
      · intro q _ hq; simp [Ne.symm hq]
      · intro hq; exact absurd (Finset.mem_univ _) hq
    · intro p _ hp; simp [Ne.symm hp]
    · intro hp; exact absurd (Finset.mem_univ _) hp
  have hdet : ((linearFlattening (RingHom.id L) (mode1FlatteningCoeff L)
      (kroneckerDoubleL1Pair L)).submatrix id colSub).det ≠ 0 := by
    rw [hsub, Matrix.det_one]; exact one_ne_zero
  have hbound := formalBorderRank_flattening_lower_bound (mode1FlatteningCoeff L) 1 hκ
    id colSub hdet hr
  simpa using hbound

theorem Psi_RCB_borderRank_ge_six {L : Type*} [Field L]
    (h2 : (2 : L) ≠ 0) (h3 : (3 : L) ≠ 0) {b imUnit : L} (hb : b ≠ 0) (hi : imUnit ^ 2 = -1)
    {r : ℕ} (hr : HasFormalBorderRankLe (Psi_RCB L b imUnit) r) : 6 ≤ r := by
  have heq := Psi_RCB_equiv_kroneckerDouble h2 h3 hb hi
  exact kroneckerDoubleL1Pair_borderRank_ge_six ((heq.hasFormalBorderRankLe_iff r).mp hr)

theorem Psi_RCB_not_hasFormalBorderRankLe_five {L : Type*} [Field L]
    (h2 : (2 : L) ≠ 0) (h3 : (3 : L) ≠ 0) {b imUnit : L} (hb : b ≠ 0) (hi : imUnit ^ 2 = -1) :
    ¬ HasFormalBorderRankLe (Psi_RCB L b imUnit) 5 := by
  intro hr
  have h6 := Psi_RCB_borderRank_ge_six h2 h3 hb hi hr
  omega

/-- Explicit `3`-term polynomial degeneration of `L₁ ⊕ L₁ᵀ` over any commutative ring `L`. -/
theorem kroneckerL1Pair_hasFormalBorderRankLe_three (L : Type*) [CommRing L] :
    HasFormalBorderRankLe (kroneckerL1Pair L) 3 := by
  let U : Fin 3 → Fin 3 → L[X] :=
    ![![1, 0, X], ![1, X, 0], ![-1, 0, 0]]
  let V : Fin 3 → Fin 3 → L[X] :=
    ![![0, X, 1], ![X, 0, 1], ![0, 0, 1]]
  let W : Fin 3 → Fin 2 → L[X] :=
    ![![0, 1], ![1, 0], ![1, 1]]
  let E : Fin 3 → Fin 3 → Fin 2 → L[X] :=
    fun i j k =>
      match k.val, i.val, j.val with
      | 0, 1, 0 => 1
      | 1, 2, 1 => 1
      | _, _, _ => 0
  refine ⟨1, U, V, W, E, fun i j k => ?_⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [Fin.sum_univ_three, U, V, W, E, kroneckerL1Pair] <;>
    ring

/-- Explicit `6`-term polynomial degeneration of `kroneckerDoubleL1Pair L`. -/
theorem kroneckerDoubleL1Pair_hasFormalBorderRankLe_six (L : Type*) [CommRing L] :
    HasFormalBorderRankLe (kroneckerDoubleL1Pair L) 6 := by
  rcases kroneckerL1Pair_hasFormalBorderRankLe_three L with ⟨d, U, V, W, E, h3⟩
  let split6 : Fin 6 → Fin 2 × Fin 3 :=
    fun t => if ht : t.val < 3 then (0, ⟨t.val, ht⟩) else (1, ⟨t.val - 3, by omega⟩)
  refine ⟨d,
    fun t p => if p.1 = (split6 t).1 then U (split6 t).2 p.2 else 0,
    fun t q => if q.1 = (split6 t).1 then V (split6 t).2 q.2 else 0,
    fun t k => W (split6 t).2 k,
    fun p q k => if p.1 = q.1 then E p.2 q.2 k else 0,
    ?_⟩
  rintro ⟨a, i⟩ ⟨c, j⟩ k
  fin_cases a <;> fin_cases c
  · simpa [Fin.sum_univ_six, Fin.sum_univ_three, split6, kroneckerDoubleL1Pair] using h3 i j k
  · simp [Fin.sum_univ_six, split6, kroneckerDoubleL1Pair]
  · simp [Fin.sum_univ_six, split6, kroneckerDoubleL1Pair]
  · simpa [Fin.sum_univ_six, Fin.sum_univ_three, split6, kroneckerDoubleL1Pair] using h3 i j k

/-- **Theorem 1.2(2) (Explicit `6`-term formal border-rank upper bound for `Ψ_RCB`):**
Over every field `L` with `char L ≠ 2, 3`, `b ≠ 0`, and `imUnit² = -1`,
`HasFormalBorderRankLe Ψ_RCB 6`. -/
theorem Psi_RCB_hasFormalBorderRankLe_six {L : Type*} [Field L]
    (h2 : (2 : L) ≠ 0) (h3 : (3 : L) ≠ 0) {b imUnit : L} (hb : b ≠ 0) (hi : imUnit ^ 2 = -1) :
    HasFormalBorderRankLe (Psi_RCB L b imUnit) 6 :=
  ((Psi_RCB_equiv_kroneckerDouble h2 h3 hb hi).hasFormalBorderRankLe_iff 6).mpr
    (kroneckerDoubleL1Pair_hasFormalBorderRankLe_six L)

/-- Quadratic extension `K(i) = K[X]/(X² + 1)` when `-1` is not a square in `K`. -/
abbrev QuadExtNegOne (K : Type*) [CommRing K] := AdjoinRoot (X ^ 2 + 1 : K[X])

lemma irreducible_X_sq_add_one {K : Type*} [Field K] (hnsq : ¬ IsSquare (-1 : K)) :
    Irreducible (X ^ 2 + 1 : K[X]) := by
  have hdeg : (X ^ 2 + 1 : K[X]).natDegree = 2 := by compute_degree!
  have hp_ne : (X ^ 2 + 1 : K[X]) ≠ 0 := by
    intro h0
    have hd := congrArg Polynomial.natDegree h0
    simp [hdeg] at hd
  refine ⟨?_, ?_⟩
  · intro hu
    have hd := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  · intro f g hfg
    have hf0 : f ≠ 0 := fun h0 => hp_ne (by simp [hfg, h0])
    have hg0 : g ≠ 0 := fun h0 => hp_ne (by simp [hfg, h0])
    have hsum : 2 = f.natDegree + g.natDegree := by
      rw [← hdeg, hfg, Polynomial.natDegree_mul hf0 hg0]
    by_cases hf_deg : f.natDegree = 0
    · left
      rw [Polynomial.eq_C_of_natDegree_eq_zero hf_deg] at hf0 ⊢
      exact isUnit_C.mpr (IsUnit.mk0 _ (fun hc0 => hf0 (by simp [hc0])))
    · by_cases hg_deg : g.natDegree = 0
      · right
        rw [Polynomial.eq_C_of_natDegree_eq_zero hg_deg] at hg0 ⊢
        exact isUnit_C.mpr (IsUnit.mk0 _ (fun hc0 => hg0 (by simp [hc0])))
      · exfalso
        have hf1 : f.natDegree = 1 := by omega
        have ha1 : f.coeff 1 ≠ 0 := by
          rw [← hf1]; exact Polynomial.leadingCoeff_ne_zero.mpr hf0
        have hf_eq : f = C (f.coeff 1) * X + C (f.coeff 0) := by
          ext n
          rcases n with _ | _ | n
          · simp
          · simp
          · have hgt : f.natDegree < n + 2 := by omega
            simp [Polynomial.coeff_eq_zero_of_natDegree_lt hgt]
        let r : K := -(f.coeff 0) * (f.coeff 1)⁻¹
        have hf_root : f.eval r = 0 := by
          rw [hf_eq]
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X, r]
          field_simp [ha1]
          ring
        have hp_root : (X ^ 2 + 1 : K[X]).eval r = 0 := by
          rw [hfg, Polynomial.eval_mul, hf_root, zero_mul]
        simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
          Polynomial.eval_one] at hp_root
        exact hnsq ⟨r, by linear_combination -hp_root⟩

/-- Specialization of Theorem 1.2(2) to `K(i) = AdjoinRoot (X² + 1)` and `AlgebraicClosure K`
whenever `-1` is not a square in `K`. -/
theorem Psi_RCB_over_QuadExtNegOne_and_AlgClosure {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {b : K} (hb : b ≠ 0)
    (hnsq : ¬ IsSquare (-1 : K)) :
    letI : Fact (Irreducible (X ^ 2 + 1 : K[X])) := ⟨irreducible_X_sq_add_one hnsq⟩
    let iK : QuadExtNegOne K := AdjoinRoot.root (X ^ 2 + 1 : K[X])
    let bK : QuadExtNegOne K := algebraMap K (QuadExtNegOne K) b
    HasTensorRankLe (Psi_RCB (QuadExtNegOne K) bK iK) 8 ∧
    ¬ HasTensorRankLe (Psi_RCB (QuadExtNegOne K) bK iK) 7 ∧
    HasFormalBorderRankLe (Psi_RCB (QuadExtNegOne K) bK iK) 6 ∧
    ¬ HasFormalBorderRankLe (Psi_RCB (QuadExtNegOne K) bK iK) 5 ∧
    (∃ iAlg : AlgebraicClosure K, iAlg ^ 2 = -1 ∧
      HasTensorRankLe (Psi_RCB (AlgebraicClosure K) (algebraMap K _ b) iAlg) 8 ∧
      ¬ HasTensorRankLe (Psi_RCB (AlgebraicClosure K) (algebraMap K _ b) iAlg) 7 ∧
      HasFormalBorderRankLe (Psi_RCB (AlgebraicClosure K) (algebraMap K _ b) iAlg) 6 ∧
      ¬ HasFormalBorderRankLe (Psi_RCB (AlgebraicClosure K) (algebraMap K _ b) iAlg) 5) := by
  let _ : Fact (Irreducible (X ^ 2 + 1 : K[X])) := ⟨irreducible_X_sq_add_one hnsq⟩
  intro iK bK
  have hiK : iK ^ 2 = -1 := by
    have hr := AdjoinRoot.eval₂_root (X ^ 2 + 1 : K[X])
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_one] at hr
    linear_combination hr
  have h2K : (2 : QuadExtNegOne K) ≠ 0 := by
    intro h0
    apply h2
    apply (algebraMap K (QuadExtNegOne K)).injective
    rw [map_ofNat, map_zero, h0]
  have h3K : (3 : QuadExtNegOne K) ≠ 0 := by
    intro h0
    apply h3
    apply (algebraMap K (QuadExtNegOne K)).injective
    rw [map_ofNat, map_zero, h0]
  have hbK : bK ≠ 0 := by
    intro h0
    apply hb
    apply (algebraMap K (QuadExtNegOne K)).injective
    rw [map_zero, ← h0]
  refine ⟨Psi_RCB_hasTensorRankLe_eight h2K h3K hbK hiK,
    Psi_RCB_not_hasTensorRankLe_seven h2K h3K hbK hiK,
    Psi_RCB_hasFormalBorderRankLe_six h2K h3K hbK hiK,
    Psi_RCB_not_hasFormalBorderRankLe_five h2K h3K hbK hiK, ?_⟩
  obtain ⟨iAlg, hiAlg_mul⟩ := IsAlgClosed.isSquare (-1 : AlgebraicClosure K)
  have hiAlg : iAlg ^ 2 = -1 := by rw [sq, ← hiAlg_mul]
  have h2A : (2 : AlgebraicClosure K) ≠ 0 := by
    intro h0
    apply h2
    apply (algebraMap K (AlgebraicClosure K)).injective
    rw [map_ofNat, map_zero, h0]
  have h3A : (3 : AlgebraicClosure K) ≠ 0 := by
    intro h0
    apply h3
    apply (algebraMap K (AlgebraicClosure K)).injective
    rw [map_ofNat, map_zero, h0]
  have hbA : (algebraMap K (AlgebraicClosure K) b) ≠ 0 := by
    intro h0
    apply hb
    apply (algebraMap K (AlgebraicClosure K)).injective
    rw [map_zero, h0]
  exact ⟨iAlg, hiAlg,
    Psi_RCB_hasTensorRankLe_eight h2A h3A hbA hiAlg,
    Psi_RCB_not_hasTensorRankLe_seven h2A h3A hbA hiAlg,
    Psi_RCB_hasFormalBorderRankLe_six h2A h3A hbA hiAlg,
    Psi_RCB_not_hasFormalBorderRankLe_five h2A h3A hbA hiAlg⟩

/-! ## Section 4: Discrete Block Preservation & Projective Veronese Rank 6 (Theorem 1.2(3)) -/

/-- Gaussian pivot left-inverse construction: any `A × n` matrix over a field `K` with trivial
right kernel admits an `n × A` left inverse `L * V = 1`. -/
lemma exists_leftInv_of_injective_mulVec {K A : Type*} [Field K] [Fintype A] [DecidableEq A] :
    ∀ {n : ℕ} (V : Matrix A (Fin n) K),
      (∀ c : Fin n → K, (∀ a : A, ∑ j : Fin n, V a j * c j = 0) → c = 0) →
      ∃ L : Matrix (Fin n) A K, L * V = 1
  | 0, _, _ =>
    ⟨0, by ext i j; exact Fin.elim0 i⟩
  | n + 1, V, hinj => by
    let e0 : Fin (n + 1) → K := fun j => if j = 0 then 1 else 0
    have hc0_ne : e0 ≠ 0 := by
      intro h0
      have := congrFun h0 0
      simp [e0] at this
    have hex_a : ∃ a₀ : A, V a₀ 0 ≠ 0 := by
      by_contra hall
      apply hc0_ne
      apply hinj
      intro a
      have ha0 : V a 0 = 0 := by
        by_contra hne
        exact hall ⟨a, hne⟩
      rw [Fin.sum_univ_succ]
      simp [e0, ha0]
    obtain ⟨a₀, hp⟩ := hex_a
    let p := V a₀ 0
    let P_elim : Matrix A A K :=
      fun a b => (if a = b then 1 else 0) - (if b = a₀ then V a 0 * p⁻¹ else 0)
    let V' : Matrix A (Fin n) K := fun a j => (P_elim * V) a j.succ
    have hPV_entry : ∀ (a : A) (k : Fin (n + 1)),
        (P_elim * V) a k = V a k - V a 0 * p⁻¹ * V a₀ k := by
      intro a k
      rw [Matrix.mul_apply]
      simp only [P_elim, sub_mul, ite_mul, one_mul, zero_mul,
        Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte]
    have hPV0 : ∀ a : A, (P_elim * V) a 0 = 0 := by
      intro a
      rw [hPV_entry]
      calc V a 0 - V a 0 * p⁻¹ * V a₀ 0 = V a 0 * (1 - p * p⁻¹) := by dsimp [p]; ring
        _ = 0 := by rw [mul_inv_cancel₀ hp, sub_self, mul_zero]
    have hinj' : ∀ d : Fin n → K, (∀ a : A, ∑ j : Fin n, V' a j * d j = 0) → d = 0 := by
      intro d hd
      let c0 : K := -p⁻¹ * ∑ j : Fin n, V a₀ j.succ * d j
      let c : Fin (n + 1) → K := Fin.cons c0 d
      have hc : ∀ a : A, ∑ j : Fin (n + 1), V a j * c j = 0 := by
        intro a
        have hd_a : ∑ j : Fin n, (V a j.succ - V a 0 * p⁻¹ * V a₀ j.succ) * d j = 0 := by
          simpa only [V', hPV_entry] using hd a
        rw [Fin.sum_univ_succ]
        simp only [c, Fin.cons_zero, Fin.cons_succ, c0]
        have hcomb : V a 0 * (-p⁻¹ * ∑ j : Fin n, V a₀ j.succ * d j) +
            ∑ j : Fin n, V a j.succ * d j =
            ∑ j : Fin n, (V a j.succ - V a 0 * p⁻¹ * V a₀ j.succ) * d j := by
          simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
          have hneg : ∑ x : Fin n, V a 0 * (-p⁻¹ * (V a₀ x.succ * d x)) =
              -(∑ x : Fin n, V a 0 * p⁻¹ * V a₀ x.succ * d x) := by
            rw [← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl fun x _ => by ring
          rw [hneg]
          ring
        rw [hcomb, hd_a]
      have hc_eq := hinj c hc
      funext j
      simpa [c] using congrFun hc_eq j.succ
    obtain ⟨L', hL'⟩ := exists_leftInv_of_injective_mulVec V' hinj'
    let L_tail : Matrix (Fin n) A K := L' * P_elim
    have hL_tail_0 : ∀ i : Fin n, (L_tail * V) i 0 = 0 := by
      intro i
      have hassoc : (L_tail * V) i 0 = (L' * (P_elim * V)) i 0 := by simp [L_tail, Matrix.mul_assoc]
      rw [hassoc, Matrix.mul_apply]
      simp [hPV0]
    have hL_tail_succ : ∀ i j : Fin n, (L_tail * V) i j.succ = if i = j then 1 else 0 := by
      intro i j
      have hassoc : (L_tail * V) i j.succ = (L' * V') i j := by
        have hmul : (L_tail * V) i j.succ = (L' * (P_elim * V)) i j.succ := by
          simp [L_tail, Matrix.mul_assoc]
        rw [hmul, Matrix.mul_apply, Matrix.mul_apply]
      rw [hassoc, hL', Matrix.one_apply]
    let L₀ : A → K := fun b =>
      (if b = a₀ then p⁻¹ else 0) - ∑ r : Fin n, p⁻¹ * V a₀ r.succ * L_tail r b
    let L : Matrix (Fin (n + 1)) A K := fun i b => Fin.cases (L₀ b) (fun i' => L_tail i' b) i
    refine ⟨L, ?_⟩
    ext i k
    refine Fin.cases ?_ (fun i' => ?_) i
    · refine Fin.cases ?_ (fun k' => ?_) k
      · rw [Matrix.mul_apply, Matrix.one_apply]
        dsimp only [L, Fin.cases_zero, L₀]
        simp only [sub_mul, Finset.sum_sub_distrib,
          ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        have hsum0 : (∑ x : A, (∑ r : Fin n, p⁻¹ * V a₀ r.succ * L_tail r x) * V x 0) = 0 := by
          simp_rw [Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_eq_zero fun r _ => ?_
          have hr0 := hL_tail_0 r
          rw [Matrix.mul_apply] at hr0
          calc (∑ x : A, p⁻¹ * V a₀ r.succ * L_tail r x * V x 0)
              = p⁻¹ * V a₀ r.succ * ∑ x : A, L_tail r x * V x 0 := by
                  rw [Finset.mul_sum]
                  exact Finset.sum_congr rfl fun x _ => by ring
            _ = 0 := by rw [hr0, mul_zero]
        rw [hsum0, sub_zero]
        exact inv_mul_cancel₀ hp
      · rw [Matrix.mul_apply, Matrix.one_apply]
        have h0ne : (0 : Fin (n + 1)) ≠ k'.succ := (Fin.succ_ne_zero k').symm
        dsimp only [L, Fin.cases_zero, L₀]
        simp only [sub_mul, Finset.sum_sub_distrib,
          ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, h0ne]
        have hsum_k : (∑ x : A, (∑ r : Fin n, p⁻¹ * V a₀ r.succ * L_tail r x) * V x k'.succ) =
            p⁻¹ * V a₀ k'.succ := by
          simp_rw [Finset.sum_mul]
          rw [Finset.sum_comm]
          calc ∑ r : Fin n, ∑ x : A, p⁻¹ * V a₀ r.succ * L_tail r x * V x k'.succ
              = ∑ r : Fin n, p⁻¹ * V a₀ r.succ * (L_tail * V) r k'.succ := by
                  refine Finset.sum_congr rfl fun r _ => ?_
                  rw [Matrix.mul_apply, Finset.mul_sum]
                  exact Finset.sum_congr rfl fun x _ => by ring
            _ = p⁻¹ * V a₀ k'.succ := by
                  simp [hL_tail_succ]
        rw [hsum_k, sub_self]
    · refine Fin.cases ?_ (fun k' => ?_) k
      · rw [Matrix.mul_apply, Matrix.one_apply]
        have hs0 : i'.succ ≠ 0 := Fin.succ_ne_zero i'
        dsimp only [L, Fin.cases_succ]
        simp only [hs0, ↓reduceIte]
        simpa [Matrix.mul_apply] using hL_tail_0 i'
      · rw [Matrix.mul_apply, Matrix.one_apply]
        dsimp only [L, Fin.cases_succ]
        simp only [Fin.succ_inj]
        simpa [Matrix.mul_apply] using hL_tail_succ i' k'

/-- Homogeneous projective curve point `P = (X, Y, Z) ∈ K³ \ {0}` on `E_b : Y² Z = X³ + b Z³`. -/
def IsProjCurvePoint {K : Type*} [CommRing K] (b : K) (P : Fin 3 → K) : Prop :=
  P ≠ 0 ∧ P 1 ^ 2 * P 2 = P 0 ^ 3 + b * P 2 ^ 3

/-- Projective equivalence of homogeneous triples (`P = c • Q` for `c ≠ 0`). -/
def ProjEquiv {K : Type*} [CommRing K] (P Q : Fin 3 → K) : Prop :=
  ∃ c : K, c ≠ 0 ∧ P = c • Q

lemma veronese2_smul {K : Type*} [CommRing K] (c : K) (P : Fin 3 → K) :
    veronese2 (c • P) = (c ^ 2) • veronese2 P := by
  funext m
  fin_cases m <;> simp [veronese2] <;> ring

lemma IsProjCurvePoint.z_eq_zero {K : Type*} [Field K] {b : K} {P : Fin 3 → K}
    (hP : IsProjCurvePoint b P) (hz : P 2 = 0) :
    P 0 = 0 ∧ P 1 ≠ 0 ∧ ProjEquiv P ![0, 1, 0] := by
  rcases hP with ⟨hne, heq⟩
  rw [hz] at heq
  have hx3 : P 0 ^ 3 = 0 := by linear_combination -heq
  have hx : P 0 = 0 := by simpa using hx3
  have hy : P 1 ≠ 0 := by
    intro hy0
    apply hne
    funext i
    fin_cases i <;> simp [hx, hy0, hz]
  refine ⟨hx, hy, ⟨P 1, hy, ?_⟩⟩
  funext i
  fin_cases i <;> simp [hx, hz]

lemma IsProjCurvePoint.affine_norm {K : Type*} [Field K] {b : K} {P : Fin 3 → K}
    (hP : IsProjCurvePoint b P) (hz : P 2 ≠ 0) :
    (P 1 * (P 2)⁻¹) ^ 2 = (P 0 * (P 2)⁻¹) ^ 3 + b ∧
    P = P 2 • ![P 0 * (P 2)⁻¹, P 1 * (P 2)⁻¹, 1] := by
  rcases hP with ⟨_, heq⟩
  refine ⟨?_, ?_⟩
  · simp only [← div_eq_mul_inv]
    field_simp [hz]
    linear_combination heq
  · funext i
    fin_cases i <;> simp [← div_eq_mul_inv, mul_div_cancel₀ _ hz]

/-- Degree-parity vanishing lemma: `A² = (X³ + b) B²` in `K[X]` forces `A = 0` and `B = 0`. -/
lemma sq_eq_cubic_mul_sq_imp_zero {K : Type*} [Field K] (b : K) (A B : K[X])
    (heq : A ^ 2 = (X ^ 3 + C b) * B ^ 2) : A = 0 ∧ B = 0 := by
  have hc3 : (X ^ 3 + C b : K[X]).coeff 3 = 1 := by simp
  have hX3_ne : (X ^ 3 + C b : K[X]) ≠ 0 := by
    intro h0; have := congrArg (fun p => p.coeff 3) h0; simp at this
  have hdX3 : (X ^ 3 + C b : K[X]).natDegree = 3 := by
    apply le_antisymm
    · compute_degree!
    · exact Polynomial.le_natDegree_of_ne_zero (by rw [hc3]; exact one_ne_zero)
  have hB0 : B = 0 := by
    by_contra hB
    have hB2 : B ^ 2 ≠ 0 := pow_ne_zero 2 hB
    have hrhs_ne : (X ^ 3 + C b) * B ^ 2 ≠ 0 := mul_ne_zero hX3_ne hB2
    have hA2_ne : A ^ 2 ≠ 0 := by rw [heq]; exact hrhs_ne
    have hA : A ≠ 0 := fun h0 => hA2_ne (by simp [h0])
    have hdL : (A ^ 2).natDegree = 2 * A.natDegree := by
      rw [sq, Polynomial.natDegree_mul hA hA]; omega
    have hdR : ((X ^ 3 + C b) * B ^ 2).natDegree = 3 + 2 * B.natDegree := by
      rw [Polynomial.natDegree_mul hX3_ne hB2, sq, Polynomial.natDegree_mul hB hB, hdX3]; omega
    have hdeg := congrArg Polynomial.natDegree heq
    omega
  refine ⟨?_, hB0⟩
  rw [hB0] at heq
  simpa using heq

lemma isCoprime_X_sub_C_pow {K : Type*} [Field K] {x₁ x₂ : K} (hne : x₁ ≠ x₂) (m₁ m₂ : ℕ) :
    IsCoprime ((X - C x₁ : K[X]) ^ m₁) ((X - C x₂ : K[X]) ^ m₂) := by
  apply IsCoprime.pow
  have hsub : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr hne.symm
  refine ⟨C ((x₂ - x₁)⁻¹), -C ((x₂ - x₁)⁻¹), ?_⟩
  have hlin : C ((x₂ - x₁)⁻¹) * (X - C x₁) + -C ((x₂ - x₁)⁻¹) * (X - C x₂) =
      C ((x₂ - x₁)⁻¹ * (x₂ - x₁)) := by
    ext n
    rcases n with _ | _ | n
    · simp; ring
    · simp
    · simp
  rw [hlin, inv_mul_cancel₀ hsub, map_one]

lemma monic_and_natDegree_prod_X_sub_C_pow {K : Type*} [Field K] [DecidableEq K]
    (T : Finset K) (f : K → ℕ) :
    (∏ x ∈ T, (X - C x : K[X]) ^ f x).Monic ∧
    (∏ x ∈ T, (X - C x : K[X]) ^ f x).natDegree = ∑ x ∈ T, f x := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rcases ih with ⟨hmon_s, hdeg_s⟩
    have hmon_a : ((X - C a : K[X]) ^ f a).Monic := (Polynomial.monic_X_sub_C a).pow (f a)
    have hdeg_a : ((X - C a : K[X]) ^ f a).natDegree = f a := by
      rw [(Polynomial.monic_X_sub_C a).natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    refine ⟨hmon_a.mul hmon_s, ?_⟩
    rw [Polynomial.natDegree_mul hmon_a.ne_zero hmon_s.ne_zero, hdeg_a, hdeg_s]

lemma card_affine_zeros_le_natDegree {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (b : K) (A B : K[X]) (S : Finset (K × K))
    (hcurve : ∀ p ∈ S, p.2 ^ 2 = p.1 ^ 3 + b)
    (hzero : ∀ p ∈ S, A.eval p.1 + p.2 * B.eval p.1 = 0)
    (hR : A ^ 2 - (X ^ 3 + C b) * B ^ 2 ≠ 0) :
    S.card ≤ (A ^ 2 - (X ^ 3 + C b) * B ^ 2).natDegree := by
  classical
  let R : K[X] := A ^ 2 - (X ^ 3 + C b) * B ^ 2
  let X_set : Finset K := S.image Prod.fst
  let fib : K → Finset (K × K) := fun x => S.filter (fun p => p.1 = x)
  have hS_biUnion : S = X_set.biUnion fib := by
    ext p
    constructor
    · intro hp
      exact Finset.mem_biUnion.mpr
        ⟨p.1, Finset.mem_image_of_mem Prod.fst hp, Finset.mem_filter.mpr ⟨hp, rfl⟩⟩
    · intro hp
      rcases Finset.mem_biUnion.mp hp with ⟨_, _, hpf⟩
      exact (Finset.mem_filter.mp hpf).1
  have hcard_sum : S.card = ∑ x ∈ X_set, (fib x).card := by
    conv_lhs => rw [hS_biUnion]
    refine Finset.card_biUnion fun x₁ _ x₂ _ hne => Finset.disjoint_left.mpr ?_
    intro p hp₁ hp₂
    simp only [fib, Finset.mem_filter] at hp₁ hp₂
    exact hne (hp₁.2.symm.trans hp₂.2)
  have hfib_le2 : ∀ x ∈ X_set, (fib x).card ≤ 2 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨p₀, hp₀, rfl⟩
    have hsub : fib p₀.1 ⊆ ({(p₀.1, p₀.2), (p₀.1, -p₀.2)} : Finset (K × K)) := by
      intro p hp
      simp only [fib, Finset.mem_filter] at hp
      have hsq : (p.2 - p₀.2) * (p.2 + p₀.2) = 0 := by
        calc (p.2 - p₀.2) * (p.2 + p₀.2) = p.2 ^ 2 - p₀.2 ^ 2 := by ring
          _ = (p.1 ^ 3 + b) - (p₀.1 ^ 3 + b) := by rw [hcurve p hp.1, hcurve p₀ hp₀]
          _ = 0 := by rw [hp.2, sub_self]
      rcases mul_eq_zero.mp hsq with h1 | h2'
      · have hy : p.2 = p₀.2 := sub_eq_zero.mp h1
        have hp_eq : p = (p₀.1, p₀.2) := Prod.ext hp.2 hy
        simp [hp_eq]
      · have hy : p.2 = -p₀.2 := eq_neg_of_add_eq_zero_left h2'
        have hp_eq : p = (p₀.1, -p₀.2) := Prod.ext hp.2 hy
        simp [hp_eq]
    exact le_trans (Finset.card_le_card hsub) (Finset.card_insert_le _ _)
  have hdvd_each : ∀ x ∈ X_set, (X - C x : K[X]) ^ (fib x).card ∣ R := by
    intro x hx
    have hle := hfib_le2 x hx
    rcases Finset.mem_image.mp hx with ⟨p₀, hp₀, hp₀x⟩
    have hp₀_fib : p₀ ∈ fib x := Finset.mem_filter.mpr ⟨hp₀, hp₀x⟩
    have hpos : 0 < (fib x).card := Finset.card_pos.mpr ⟨p₀, hp₀_fib⟩
    have hcases : (fib x).card = 1 ∨ (fib x).card = 2 := by omega
    rcases hcases with hc1 | hc2
    · rw [hc1, pow_one, Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]
      dsimp [R]
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_mul,
        Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
      rw [← hp₀x, ← hcurve p₀ hp₀]
      linear_combination (A.eval p₀.1 - p₀.2 * B.eval p₀.1) * (hzero p₀ hp₀)
    · rw [hc2]
      have hgt1 : 1 < (fib x).card := by omega
      obtain ⟨p₁, hp₁, p₂, hp₂, hp₁₂⟩ := Finset.one_lt_card.mp hgt1
      simp only [fib, Finset.mem_filter] at hp₁ hp₂
      have hy_ne : p₁.2 ≠ p₂.2 := fun hy => hp₁₂ (Prod.ext (hp₁.2.trans hp₂.2.symm) hy)
      have hsq : (p₁.2 - p₂.2) * (p₁.2 + p₂.2) = 0 := by
        calc (p₁.2 - p₂.2) * (p₁.2 + p₂.2) = p₁.2 ^ 2 - p₂.2 ^ 2 := by ring
          _ = (p₁.1 ^ 3 + b) - (p₂.1 ^ 3 + b) := by rw [hcurve p₁ hp₁.1, hcurve p₂ hp₂.1]
          _ = 0 := by rw [hp₁.2, hp₂.2, sub_self]
      have hsum_y : p₁.2 + p₂.2 = 0 :=
        (mul_eq_zero.mp hsq).resolve_left (sub_ne_zero.mpr hy_ne)
      have hy2 : p₂.2 = -p₁.2 := eq_neg_of_add_eq_zero_right hsum_y
      have hy1_ne : p₁.2 ≠ 0 := by
        intro h0; apply hy_ne; rw [hy2, h0, neg_zero]
      have hz1 := hzero p₁ hp₁.1
      have hz2 := hzero p₂ hp₂.1
      rw [hp₁.2] at hz1
      rw [hp₂.2, hy2] at hz2
      have h2Ax : 2 * A.eval x = 0 := by linear_combination hz1 + hz2
      have hAx : A.eval x = 0 := (mul_eq_zero.mp h2Ax).resolve_left h2
      have h2yBx : (2 * p₁.2) * B.eval x = 0 := by linear_combination hz1 - hz2
      have hBx : B.eval x = 0 :=
        (mul_eq_zero.mp h2yBx).resolve_left (mul_ne_zero h2 hy1_ne)
      have hdvdA : (X - C x) ^ 2 ∣ A ^ 2 :=
        pow_dvd_pow_of_dvd (Polynomial.dvd_iff_isRoot.mpr hAx) 2
      have hdvdB : (X - C x) ^ 2 ∣ B ^ 2 :=
        pow_dvd_pow_of_dvd (Polynomial.dvd_iff_isRoot.mpr hBx) 2
      exact dvd_sub hdvdA (dvd_mul_of_dvd_right hdvdB _)
  have hdvd_prod : (∏ x ∈ X_set, (X - C x : K[X]) ^ (fib x).card) ∣ R := by
    refine Finset.prod_dvd_of_coprime ?_ hdvd_each
    intro x₁ _ x₂ _ hne
    exact isCoprime_X_sub_C_pow hne _ _
  have hdeg_prod := (monic_and_natDegree_prod_X_sub_C_pow X_set (fun x => (fib x).card)).2
  rw [hcard_sum, ← hdeg_prod]
  exact Polynomial.natDegree_le_of_dvd hdvd_prod hR

/-- **Theorem 1.2(3) (Projective Veronese rank-`6` / Bézout quadratic vanishing theorem on `E_b`):**
If `|A| ≥ 7` and `rep : A → K³` represents pairwise projectively distinct points of `E_b(K)`,
any quadratic form `∑ m, c m * veronese2 (rep a) m = 0` vanishing on all `a : A` is identically `0`. -/
theorem veronese2_vanishing_eq_zero_of_card_ge_seven {K A : Type*} [Field K]
    [Fintype A] [DecidableEq A]
    (h2 : (2 : K) ≠ 0) (b : K) (hcard : 7 ≤ Fintype.card A)
    (rep : A → Fin 3 → K)
    (hcurve : ∀ a : A, IsProjCurvePoint b (rep a))
    (hdistinct : ∀ a₁ a₂ : A, ProjEquiv (rep a₁) (rep a₂) → a₁ = a₂)
    (c : Fin 6 → K)
    (hvanish : ∀ a : A, ∑ m : Fin 6, c m * veronese2 (rep a) m = 0) :
    c = 0 := by
  classical
  let A_poly : K[X] := C (c 1) * X ^ 3 + C (c 0) * X ^ 2 + C (c 5) * X + C (c 1 * b + c 2)
  let B_poly : K[X] := C (c 3) * X + C (c 4)
  let affMap : A → K × K := fun a => (rep a 0 * (rep a 2)⁻¹, rep a 1 * (rep a 2)⁻¹)
  have haff_inj : ∀ a₁ a₂ : A, rep a₁ 2 ≠ 0 → rep a₂ 2 ≠ 0 → affMap a₁ = affMap a₂ → a₁ = a₂ := by
    intro a₁ a₂ hz₁ hz₂ heq
    have hx := congrArg Prod.fst heq
    have hy := congrArg Prod.snd heq
    dsimp [affMap] at hx hy
    apply hdistinct
    refine ⟨rep a₁ 2 * (rep a₂ 2)⁻¹, mul_ne_zero hz₁ (inv_ne_zero hz₂), ?_⟩
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, smul_eq_mul]
      calc rep a₁ 0 = (rep a₁ 0 * (rep a₁ 2)⁻¹) * rep a₁ 2 := by
              rw [mul_assoc, inv_mul_cancel₀ hz₁, mul_one]
        _ = rep a₁ 2 * (rep a₂ 2)⁻¹ * rep a₂ 0 := by rw [hx]; ring
    · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
      calc rep a₁ 1 = (rep a₁ 1 * (rep a₁ 2)⁻¹) * rep a₁ 2 := by
              rw [mul_assoc, inv_mul_cancel₀ hz₁, mul_one]
        _ = rep a₁ 2 * (rep a₂ 2)⁻¹ * rep a₂ 1 := by rw [hy]; ring
    · simp only [Fin.reduceFinMk, Fin.isValue, Pi.smul_apply, smul_eq_mul]
      rw [mul_assoc, inv_mul_cancel₀ hz₂, mul_one]
  have haff_zero : ∀ a : A, rep a 2 ≠ 0 →
      A_poly.eval (affMap a).1 + (affMap a).2 * B_poly.eval (affMap a).1 = 0 := by
    intro a hz
    rcases (hcurve a).affine_norm hz with ⟨hcy, hnorm⟩
    have hv := hvanish a
    rw [hnorm, veronese2_smul] at hv
    have hv' : (rep a 2) ^ 2 *
        (A_poly.eval (affMap a).1 + (affMap a).2 * B_poly.eval (affMap a).1) = 0 := by
      calc (rep a 2) ^ 2 * (A_poly.eval (affMap a).1 + (affMap a).2 * B_poly.eval (affMap a).1)
          = ∑ m : Fin 6, c m * ((rep a 2 ^ 2) • veronese2 ![ (affMap a).1, (affMap a).2, 1 ] m) := by
              dsimp [A_poly, B_poly]
              simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
                Polynomial.eval_C, Polynomial.eval_X, Fin.sum_univ_six, veronese2,
                Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
              linear_combination (rep a 2) ^ 2 * c 1 * (-hcy)
        _ = 0 := hv
    exact (mul_eq_zero.mp hv').resolve_left (pow_ne_zero 2 hz)
  have hR_zero : A_poly ^ 2 - (X ^ 3 + C b) * B_poly ^ 2 = 0 := by
    by_cases hinf : ∃ a₀ : A, rep a₀ 2 = 0
    · rcases hinf with ⟨a₀, hz₀⟩
      rcases (hcurve a₀).z_eq_zero hz₀ with ⟨hx₀, hy₀, hproj₀⟩
      have hc1 : c 1 = 0 := by
        have hv₀ := hvanish a₀
        simp [Fin.sum_univ_six, veronese2, hx₀, hz₀] at hv₀
        rcases hv₀ with hc1 | hy0'
        · exact hc1
        · exact absurd hy0' hy₀
      let A' : Finset A := Finset.univ.erase a₀
      have hz_ne : ∀ a ∈ A', rep a 2 ≠ 0 := by
        intro a ha hz
        have ha_ne : a ≠ a₀ := (Finset.mem_erase.mp ha).1
        rcases (hcurve a).z_eq_zero hz with ⟨_, _, c_a, hc_a, hpa⟩
        rcases hproj₀ with ⟨c_0, hc_0, hp0⟩
        apply ha_ne
        apply hdistinct
        refine ⟨c_a * c_0⁻¹, mul_ne_zero hc_a (inv_ne_zero hc_0), ?_⟩
        rw [hpa, hp0, smul_smul, mul_assoc, inv_mul_cancel₀ hc_0, mul_one]
      let S : Finset (K × K) := A'.image affMap
      have hScard : 6 ≤ S.card := by
        have hinjOn : Set.InjOn affMap A' := fun a₁ ha₁ a₂ ha₂ heq =>
          haff_inj a₁ a₂ (hz_ne a₁ ha₁) (hz_ne a₂ ha₂) heq
        rw [Finset.card_image_of_injOn hinjOn]
        have h1 : A'.card + 1 = Fintype.card A := by
          dsimp [A']
          simpa using Finset.card_erase_add_one (Finset.mem_univ a₀)
        omega
      have hdegR : (A_poly ^ 2 - (X ^ 3 + C b) * B_poly ^ 2).natDegree ≤ 5 := by
        have hA_eq : A_poly = C (c 0) * X ^ 2 + C (c 5) * X + C (c 2) := by
          dsimp [A_poly]; simp [hc1]
        rw [hA_eq]
        dsimp [B_poly]
        compute_degree!
      by_contra hR_ne
      have hle := card_affine_zeros_le_natDegree h2 b A_poly B_poly S
        (fun p hp => by
          rcases Finset.mem_image.mp hp with ⟨a, ha, rfl⟩
          exact ((hcurve a).affine_norm (hz_ne a ha)).1)
        (fun p hp => by
          rcases Finset.mem_image.mp hp with ⟨a, ha, rfl⟩
          exact haff_zero a (hz_ne a ha))
        hR_ne
      exact absurd (le_trans hScard (le_trans hle hdegR)) (by omega)
    · have hz_ne : ∀ a : A, rep a 2 ≠ 0 := fun a hz => hinf ⟨a, hz⟩
      let S : Finset (K × K) := Finset.univ.image affMap
      have hScard : 7 ≤ S.card := by
        have hinjOn : Set.InjOn affMap (Finset.univ : Finset A) := fun a₁ _ a₂ _ heq =>
          haff_inj a₁ a₂ (hz_ne a₁) (hz_ne a₂) heq
        rw [Finset.card_image_of_injOn hinjOn, Finset.card_univ]
        exact hcard
      have hdegR : (A_poly ^ 2 - (X ^ 3 + C b) * B_poly ^ 2).natDegree ≤ 6 := by
        dsimp [A_poly, B_poly]
        compute_degree!
      by_contra hR_ne
      have hle := card_affine_zeros_le_natDegree h2 b A_poly B_poly S
        (fun p hp => by
          rcases Finset.mem_image.mp hp with ⟨a, _, rfl⟩
          exact ((hcurve a).affine_norm (hz_ne a)).1)
        (fun p hp => by
          rcases Finset.mem_image.mp hp with ⟨a, _, rfl⟩
          exact haff_zero a (hz_ne a))
        hR_ne
      exact absurd (le_trans hScard (le_trans hle hdegR)) (by omega)
  obtain ⟨hA0, hB0⟩ := sq_eq_cubic_mul_sq_imp_zero b A_poly B_poly (sub_eq_zero.mp hR_zero)
  have hc1 : c 1 = 0 := by
    have := congrArg (fun p => p.coeff 3) hA0
    simpa [A_poly] using this
  have hc0 : c 0 = 0 := by
    have := congrArg (fun p => p.coeff 2) hA0
    simpa [A_poly] using this
  have hc5 : c 5 = 0 := by
    have := congrArg (fun p => p.coeff 1) hA0
    simpa [A_poly] using this
  have hc2 : c 2 = 0 := by
    have := congrArg (fun p => p.coeff 0) hA0
    simpa [A_poly, hc1] using this
  have hc3 : c 3 = 0 := by
    have := congrArg (fun p => p.coeff 1) hB0
    simpa [B_poly] using this
  have hc4 : c 4 = 0 := by
    have := congrArg (fun p => p.coeff 0) hB0
    simpa [B_poly] using this
  funext m
  fin_cases m <;> assumption

/-- Veronese evaluation matrix `ev_A : A × Fin 6` sending `a ↦ veronese2 (rep a)`. -/
def veroneseEvalMat {K A : Type*} [CommRing K] (rep : A → Fin 3 → K) : Matrix A (Fin 6) K :=
  fun a m => veronese2 (rep a) m

/-- Left-invertibility (full rank `6`) of `veroneseEvalMat` whenever `|A| ≥ 7` on `E_b(K)`. -/
theorem veroneseEvalMat_exists_leftInv {K A : Type*} [Field K] [Fintype A] [DecidableEq A]
    (h2 : (2 : K) ≠ 0) (b : K) (hcard : 7 ≤ Fintype.card A)
    (rep : A → Fin 3 → K)
    (hcurve : ∀ a : A, IsProjCurvePoint b (rep a))
    (hdistinct : ∀ a₁ a₂ : A, ProjEquiv (rep a₁) (rep a₂) → a₁ = a₂) :
    ∃ L_A : Matrix (Fin 6) A K, L_A * veroneseEvalMat rep = 1 := by
  apply exists_leftInv_of_injective_mulVec
  intro c hc
  refine veronese2_vanishing_eq_zero_of_card_ge_seven h2 b hcard rep hcurve hdistinct c ?_
  intro a
  simpa [veroneseEvalMat, mul_comm] using hc a

/-- Discrete evaluation tensor `T_RCB|_{A × B} ∈ K^A ⊗ K^B ⊗ K³`. -/
def T_RCB_restricted {K A B : Type*} [CommRing K] (b : K)
    (repA : A → Fin 3 → K) (repB : B → Fin 3 → K) : Tensor3 K A B (Fin 3) :=
  mapTensor (veroneseEvalMat repA) (veroneseEvalMat repB) (1 : Matrix (Fin 3) (Fin 3) K)
    (T_RCB K b)

/-- **Theorem 1.2(3) (Discrete block preservation for `T_RCB|_{A × B}` and `T_RCB|_{A × A}`):**
Whenever `|A|, |B| ≥ 7` on `E_b(K)`, `T_RCB|_{A × B}` preserves exact tensor rank and formal border
rank (and for `A = B` with shared representatives, `(1,2)`-symmetric rank and formal border rank). -/
theorem T_RCB_restricted_preserves_ranks {K A B : Type*} [Field K]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (h2 : (2 : K) ≠ 0) (b : K)
    (hcardA : 7 ≤ Fintype.card A) (hcardB : 7 ≤ Fintype.card B)
    (repA : A → Fin 3 → K) (repB : B → Fin 3 → K)
    (hcurveA : ∀ a : A, IsProjCurvePoint b (repA a))
    (hdistinctA : ∀ a₁ a₂ : A, ProjEquiv (repA a₁) (repA a₂) → a₁ = a₂)
    (hcurveB : ∀ b' : B, IsProjCurvePoint b (repB b'))
    (hdistinctB : ∀ b₁ b₂ : B, ProjEquiv (repB b₁) (repB b₂) → b₁ = b₂) (r : ℕ) :
    (HasTensorRankLe (T_RCB_restricted b repA repB) r ↔ HasTensorRankLe (T_RCB K b) r) ∧
    (HasFormalBorderRankLe (T_RCB_restricted b repA repB) r ↔ HasFormalBorderRankLe (T_RCB K b) r) ∧
    (HasSym12RankLe (T_RCB_restricted b repA repA) r ↔ HasSym12RankLe (T_RCB K b) r) ∧
    (HasSym12FormalBorderRankLe (T_RCB_restricted b repA repA) r ↔
      HasSym12FormalBorderRankLe (T_RCB K b) r) := by
  obtain ⟨LA, hLA⟩ := veroneseEvalMat_exists_leftInv h2 b hcardA repA hcurveA hdistinctA
  obtain ⟨LB, hLB⟩ := veroneseEvalMat_exists_leftInv h2 b hcardB repB hcurveB hdistinctB
  have h1 : (1 : Matrix (Fin 3) (Fin 3) K) * 1 = 1 := Matrix.mul_one 1
  exact ⟨hasTensorRankLe_mapTensor_iff_of_leftInv hLA hLB h1 (T_RCB K b) r,
    hasFormalBorderRankLe_mapTensor_iff_of_leftInv hLA hLB h1 (T_RCB K b) r,
    hasSym12RankLe_mapTensor_iff_of_leftInv hLA h1 (T_RCB K b) r,
    hasSym12FormalBorderRankLe_mapTensor_iff_of_leftInv hLA h1 (T_RCB K b) r⟩

/-- Mode-3 functional `ℓ(P₃) = (Z₃, -(X₃ - i Y₃))` for `Ψ_RCB|_{A × B × C}`. -/
def psiMode3Mat {K L C : Type*} [CommRing K] [CommRing L]
    (φ : K →+* L) (imUnit : L) (repC : C → Fin 3 → K) : Matrix C (Fin 2) L :=
  fun c k =>
    match k.val with
    | 0 => φ (repC c 2)
    | _ => -(φ (repC c 0) - imUnit * φ (repC c 1))

/-- Discrete evaluation tensor `Ψ_RCB|_{A × B × C} ∈ L^{A × B × C}`. -/
def Psi_RCB_restricted {K L A B C : Type*} [CommRing K] [CommRing L]
    (φ : K →+* L) (b : K) (imUnit : L)
    (repA : A → Fin 3 → K) (repB : B → Fin 3 → K) (repC : C → Fin 3 → K) :
    Tensor3 L A B C :=
  mapTensor ((veroneseEvalMat repA).map φ) ((veroneseEvalMat repB).map φ)
    (psiMode3Mat φ imUnit repC) (Psi_RCB L (φ b) imUnit)

/-- **Theorem 1.2(3) (`|C| ≥ 2` discrete preservation for `Ψ_RCB|_{A × B × C}`):**
When `-1` is not a square in `K`, over any field extension `φ : K →+* L` containing `imUnit`
with `imUnit² = -1` (including `K(i)` and `AlgebraicClosure K`), `Ψ_RCB|_{A × B × C}` preserves
exact tensor rank `8` and formal border rank `6` for every `|A|, |B| ≥ 7` and `|C| ≥ 2`. -/
theorem Psi_RCB_restricted_preserves_ranks {K L A B C : Type*} [Field K] [Field L]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {b : K} (hb : b ≠ 0)
    (hnsq : ¬ IsSquare (-1 : K))
    (φ : K →+* L) {imUnit : L} (hi : imUnit ^ 2 = -1)
    (hcardA : 7 ≤ Fintype.card A) (hcardB : 7 ≤ Fintype.card B) (hcardC : 2 ≤ Fintype.card C)
    (repA : A → Fin 3 → K) (repB : B → Fin 3 → K) (repC : C → Fin 3 → K)
    (hcurveA : ∀ a : A, IsProjCurvePoint b (repA a))
    (hdistinctA : ∀ a₁ a₂ : A, ProjEquiv (repA a₁) (repA a₂) → a₁ = a₂)
    (hcurveB : ∀ b' : B, IsProjCurvePoint b (repB b'))
    (hdistinctB : ∀ b₁ b₂ : B, ProjEquiv (repB b₁) (repB b₂) → b₁ = b₂)
    (hcurveC : ∀ c : C, IsProjCurvePoint b (repC c))
    (hdistinctC : ∀ c₁ c₂ : C, ProjEquiv (repC c₁) (repC c₂) → c₁ = c₂) :
    HasTensorRankLe (Psi_RCB_restricted φ b imUnit repA repB repC) 8 ∧
    ¬ HasTensorRankLe (Psi_RCB_restricted φ b imUnit repA repB repC) 7 ∧
    HasFormalBorderRankLe (Psi_RCB_restricted φ b imUnit repA repB repC) 6 ∧
    ¬ HasFormalBorderRankLe (Psi_RCB_restricted φ b imUnit repA repB repC) 5 := by
  have hlin_indep : ∀ x y : K, φ x + imUnit * φ y = 0 → x = 0 ∧ y = 0 := by
    intro x y hxy
    by_cases hy : y = 0
    · subst hy
      simp only [map_zero, mul_zero, add_zero] at hxy
      exact ⟨φ.injective (by rw [hxy, map_zero]), rfl⟩
    · exfalso
      have him : imUnit = φ (-x * y⁻¹) := by
        have hφy : φ y ≠ 0 := fun h0 => hy (φ.injective (by rw [h0, map_zero]))
        calc imUnit = (-φ x) * (φ y)⁻¹ := by
                have heq : imUnit * φ y = -φ x := by linear_combination hxy
                rw [← heq, mul_assoc, mul_inv_cancel₀ hφy, mul_one]
          _ = φ (-x * y⁻¹) := by simp [map_mul, map_inv₀]
      have hsqL : φ ((-x * y⁻¹) * (-x * y⁻¹)) = φ (-1) := by
        rw [map_mul, ← him, ← sq, hi, map_neg, map_one]
      exact hnsq ⟨-x * y⁻¹, (φ.injective hsqL).symm⟩
  obtain ⟨LA, hLA⟩ := veroneseEvalMat_exists_leftInv h2 b hcardA repA hcurveA hdistinctA
  obtain ⟨LB, hLB⟩ := veroneseEvalMat_exists_leftInv h2 b hcardB repB hcurveB hdistinctB
  have hLA_φ : LA.map φ * (veroneseEvalMat repA).map φ = 1 := by
    rw [← Matrix.map_mul, hLA]
    ext i j; simp [Matrix.one_apply]
  have hLB_φ : LB.map φ * (veroneseEvalMat repB).map φ = 1 := by
    rw [← Matrix.map_mul, hLB]
    ext i j; simp [Matrix.one_apply]
  obtain ⟨LC, hLC⟩ : ∃ LC : Matrix (Fin 2) C L, LC * psiMode3Mat φ imUnit repC = 1 := by
    apply exists_leftInv_of_injective_mulVec
    intro d hd
    have hgt1 : 1 < Fintype.card C := by omega
    obtain ⟨c₁, c₂, hc₁₂⟩ := Fintype.one_lt_card_iff.mp hgt1
    let M₂ : Matrix (Fin 2) (Fin 2) L :=
      fun r k => psiMode3Mat φ imUnit repC (if r = 0 then c₁ else c₂) k
    have hdet_ne : M₂ 0 0 * M₂ 1 1 - M₂ 0 1 * M₂ 1 0 ≠ 0 := by
      intro hdet0
      have hcomb : φ (-(repC c₁ 2 * repC c₂ 0 - repC c₂ 2 * repC c₁ 0)) +
          imUnit * φ (repC c₁ 2 * repC c₂ 1 - repC c₂ 2 * repC c₁ 1) = 0 := by
        dsimp [M₂, psiMode3Mat] at hdet0
        simp only [Fin.isValue, map_neg, map_sub, map_mul] at hdet0 ⊢
        linear_combination hdet0
      obtain ⟨hx_rel, hy_rel⟩ := hlin_indep _ _ hcomb
      have hzx : repC c₁ 2 * repC c₂ 0 = repC c₂ 2 * repC c₁ 0 := by linear_combination -hx_rel
      have hzy : repC c₁ 2 * repC c₂ 1 = repC c₂ 2 * repC c₁ 1 := by linear_combination hy_rel
      apply hc₁₂
      apply hdistinctC
      by_cases hz₁ : repC c₁ 2 = 0
      · rcases (hcurveC c₁).z_eq_zero hz₁ with ⟨_, hy₁, c_1, hc_1, hp1⟩
        rw [hz₁, zero_mul] at hzy
        have hz₂ : repC c₂ 2 = 0 := (mul_eq_zero.mp hzy.symm).resolve_right hy₁
        rcases (hcurveC c₂).z_eq_zero hz₂ with ⟨_, _, c_2, hc_2, hp2⟩
        refine ⟨c_1 * c_2⁻¹, mul_ne_zero hc_1 (inv_ne_zero hc_2), ?_⟩
        rw [hp1, hp2, smul_smul, mul_assoc, inv_mul_cancel₀ hc_2, mul_one]
      · have hz₂ : repC c₂ 2 ≠ 0 := by
          intro hz₂0
          rw [hz₂0, zero_mul] at hzx hzy
          have hx₂ : repC c₂ 0 = 0 := (mul_eq_zero.mp hzx).resolve_left hz₁
          have hy₂ : repC c₂ 1 = 0 := (mul_eq_zero.mp hzy).resolve_left hz₁
          apply (hcurveC c₂).1
          funext i; fin_cases i <;> assumption
        refine ⟨repC c₁ 2 * (repC c₂ 2)⁻¹, mul_ne_zero hz₁ (inv_ne_zero hz₂), ?_⟩
        funext i
        fin_cases i
        · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, smul_eq_mul]
          calc repC c₁ 0 = (repC c₂ 2 * repC c₁ 0) * (repC c₂ 2)⁻¹ := by
                  rw [mul_comm (repC c₂ 2), mul_assoc, mul_inv_cancel₀ hz₂, mul_one]
            _ = repC c₁ 2 * (repC c₂ 2)⁻¹ * repC c₂ 0 := by rw [← hzx]; ring
        · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
          calc repC c₁ 1 = (repC c₂ 2 * repC c₁ 1) * (repC c₂ 2)⁻¹ := by
                  rw [mul_comm (repC c₂ 2), mul_assoc, mul_inv_cancel₀ hz₂, mul_one]
            _ = repC c₁ 2 * (repC c₂ 2)⁻¹ * repC c₂ 1 := by rw [← hzy]; ring
        · simp only [Fin.reduceFinMk, Fin.isValue, Pi.smul_apply, smul_eq_mul]
          rw [mul_assoc, inv_mul_cancel₀ hz₂, mul_one]
    have hd₁ := hd c₁
    have hd₂ := hd c₂
    rw [Fin.sum_univ_two] at hd₁ hd₂
    have hM0 : M₂ 0 0 * d 0 + M₂ 0 1 * d 1 = 0 := by simpa [M₂] using hd₁
    have hM1 : M₂ 1 0 * d 0 + M₂ 1 1 * d 1 = 0 := by simpa [M₂] using hd₂
    have hd0_mul : (M₂ 0 0 * M₂ 1 1 - M₂ 0 1 * M₂ 1 0) * d 0 = 0 := by
      linear_combination M₂ 1 1 * hM0 - M₂ 0 1 * hM1
    have hd1_mul : (M₂ 0 0 * M₂ 1 1 - M₂ 0 1 * M₂ 1 0) * d 1 = 0 := by
      linear_combination -M₂ 1 0 * hM0 + M₂ 0 0 * hM1
    have hd0 : d 0 = 0 := (mul_eq_zero.mp hd0_mul).resolve_left hdet_ne
    have hd1 : d 1 = 0 := (mul_eq_zero.mp hd1_mul).resolve_left hdet_ne
    funext k; fin_cases k <;> assumption
  have h2L : (2 : L) ≠ 0 := by
    intro h0; apply h2; apply φ.injective; rw [map_ofNat, map_zero, h0]
  have h3L : (3 : L) ≠ 0 := by
    intro h0; apply h3; apply φ.injective; rw [map_ofNat, map_zero, h0]
  have hbL : φ b ≠ 0 := by
    intro h0; apply hb; apply φ.injective; rw [map_zero, h0]
  have hrk := fun r => hasTensorRankLe_mapTensor_iff_of_leftInv hLA_φ hLB_φ hLC
    (Psi_RCB L (φ b) imUnit) r
  have hbrk := fun r => hasFormalBorderRankLe_mapTensor_iff_of_leftInv hLA_φ hLB_φ hLC
    (Psi_RCB L (φ b) imUnit) r
  exact ⟨(hrk 8).mpr (Psi_RCB_hasTensorRankLe_eight h2L h3L hbL hi),
    fun h7 => Psi_RCB_not_hasTensorRankLe_seven h2L h3L hbL hi ((hrk 7).mp h7),
    (hbrk 6).mpr (Psi_RCB_hasFormalBorderRankLe_six h2L h3L hbL hi),
    fun h5 => Psi_RCB_not_hasFormalBorderRankLe_five h2L h3L hbL hi ((hbrk 5).mp h5)⟩

/-! ## Section 5: Bosma–Lenstra Base Locus, Completeness, and `ZMod 67` Witness (Theorem 1.2(4)) -/

/-- Normalized projective point of `E_b(K)`: either `O = [0 : 1 : 0]` (`inf`) or `[x : y : 1]` (`aff`). -/
inductive EbPoint (K : Type*) [CommRing K] (b : K)
  | inf : EbPoint K b
  | aff (x y : K) (h : y ^ 2 = x ^ 3 + b) : EbPoint K b

instance {K : Type*} [CommRing K] [DecidableEq K] {b : K} : DecidableEq (EbPoint K b)
  | .inf, .inf => isTrue rfl
  | .inf, .aff _ _ _ => isFalse (by intro h; cases h)
  | .aff _ _ _, .inf => isFalse (by intro h; cases h)
  | .aff x₁ y₁ _, .aff x₂ y₂ _ =>
    if hx : x₁ = x₂ then
      if hy : y₁ = y₂ then
        isTrue (by subst hx; subst hy; rfl)
      else
        isFalse (by intro h; cases h; exact hy rfl)
    else
      isFalse (by intro h; cases h; exact hx rfl)

/-- Canonical homogeneous representative `![0, 1, 0]` or `![x, y, 1]` of an `EbPoint`. -/
def EbPoint.toProj {K : Type*} [CommRing K] {b : K} : EbPoint K b → Fin 3 → K
  | .inf => ![0, 1, 0]
  | .aff x y _ => ![x, y, 1]

lemma EbPoint.isProjCurvePoint {K : Type*} [Field K] {b : K} (p : EbPoint K b) :
    IsProjCurvePoint b p.toProj := by
  cases p with
  | inf =>
    refine ⟨?_, by simp [EbPoint.toProj]⟩
    intro h0; have := congrFun h0 1; simp [EbPoint.toProj] at this
  | aff x y h =>
    refine ⟨?_, by simpa [EbPoint.toProj] using h⟩
    intro h0; have := congrFun h0 2; simp [EbPoint.toProj] at this

/-- Every projective curve point `P` on `E_b(K)` normalizes projectively to a unique `EbPoint`. -/
def IsProjCurvePoint.toEbPoint {K : Type*} [Field K] [DecidableEq K] {b : K}
    {P : Fin 3 → K} (hP : IsProjCurvePoint b P) : EbPoint K b :=
  if hz : P 2 = 0 then .inf
  else .aff (P 0 * (P 2)⁻¹) (P 1 * (P 2)⁻¹) (hP.affine_norm hz).1

lemma IsProjCurvePoint.projEquiv_toEbPoint {K : Type*} [Field K] [DecidableEq K] {b : K}
    {P : Fin 3 → K} (hP : IsProjCurvePoint b P) :
    ProjEquiv P (hP.toEbPoint).toProj := by
  unfold IsProjCurvePoint.toEbPoint
  split_ifs with hz
  · exact (hP.z_eq_zero hz).2.2
  · exact ⟨P 2, hz, (hP.affine_norm hz).2⟩

/-- Point negation `-P` on `E_b(K)`. -/
def ebNeg {K : Type*} [CommRing K] {b : K} : EbPoint K b → EbPoint K b
  | .inf => .inf
  | .aff x y h => .aff x (-y) (by linear_combination h)

/-- Standard chord-and-tangent group addition `P₁ + P₂` on `E_b(K)`. -/
def ebAdd {K : Type*} [Field K] [DecidableEq K] {b : K} :
    EbPoint K b → EbPoint K b → EbPoint K b
  | .inf, q => q
  | p, .inf => p
  | .aff x₁ y₁ h₁, .aff x₂ y₂ h₂ =>
    if hx : x₁ = x₂ then
      if hy : y₁ + y₂ = 0 then .inf
      else
        let lam := (3 * x₁ ^ 2) * (2 * y₁)⁻¹
        let x₃ := lam ^ 2 - 2 * x₁
        let y₃ := lam * (x₁ - x₃) - y₁
        .aff x₃ y₃ (by
          have hy_eq : y₁ = y₂ := by
            have hsq : (y₁ - y₂) * (y₁ + y₂) = 0 := by
              calc (y₁ - y₂) * (y₁ + y₂) = y₁ ^ 2 - y₂ ^ 2 := by ring
                _ = (x₁ ^ 3 + b) - (x₂ ^ 3 + b) := by rw [h₁, h₂]
                _ = 0 := by rw [hx, sub_self]
            exact sub_eq_zero.mp ((mul_eq_zero.mp hsq).resolve_right hy)
          have h2y₁ : 2 * y₁ ≠ 0 := by
            intro h0; apply hy; rw [← hy_eq]; linear_combination h0
          have htan : 2 * y₁ * lam - 3 * x₁ ^ 2 = 0 := by
            dsimp [lam]
            calc 2 * y₁ * (3 * x₁ ^ 2 * (2 * y₁)⁻¹) - 3 * x₁ ^ 2
                = 3 * x₁ ^ 2 * ((2 * y₁) * (2 * y₁)⁻¹ - 1) := by ring
              _ = 0 := by rw [mul_inv_cancel₀ h2y₁, sub_self, mul_zero]
          dsimp [x₃, y₃]
          linear_combination h₁ + (lam ^ 2 - 3 * x₁) * htan)
    else
      let lam := (y₂ - y₁) * (x₂ - x₁)⁻¹
      let x₃ := lam ^ 2 - x₁ - x₂
      let y₃ := lam * (x₁ - x₃) - y₁
      .aff x₃ y₃ (by
        have hdx : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
        have hy₂_rel : y₂ = y₁ + lam * (x₂ - x₁) := by
          dsimp [lam]
          calc y₂ = y₁ + (y₂ - y₁) * ((x₂ - x₁)⁻¹ * (x₂ - x₁)) := by
                  rw [inv_mul_cancel₀ hdx, mul_one, add_sub_cancel]
            _ = y₁ + (y₂ - y₁) * (x₂ - x₁)⁻¹ * (x₂ - x₁) := by ring
        have hsec_mul : (x₂ - x₁) *
            (2 * y₁ * lam + (x₂ - x₁) * lam ^ 2 - (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2)) = 0 := by
          have hdiff : y₂ ^ 2 - x₂ ^ 3 - (y₁ ^ 2 - x₁ ^ 3) = 0 := by
            linear_combination h₂ - h₁
          rw [hy₂_rel] at hdiff
          linear_combination hdiff
        have hsec : 2 * y₁ * lam + (x₂ - x₁) * lam ^ 2 - (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2) = 0 :=
          (mul_eq_zero.mp hsec_mul).resolve_left hdx
        dsimp [x₃, y₃]
        linear_combination h₁ + (lam ^ 2 - 2 * x₁ - x₂) * hsec)

/-- Group difference `P₁ - P₂ := P₁ + (-P₂)` on `E_b(K)`. -/
def ebSub {K : Type*} [Field K] [DecidableEq K] {b : K} (p₁ p₂ : EbPoint K b) : EbPoint K b :=
  ebAdd p₁ (ebNeg p₂)

/-- Predicate `P ∈ E_b(K)[2] \ {O}` (`P = [r : 0 : 1]` with `r³ + b = 0`). -/
def IsNonzeroTwoTorsion {K : Type*} [CommRing K] {b : K} (p : EbPoint K b) : Prop :=
  ∃ (r : K) (hr : (0 : K) ^ 2 = r ^ 3 + b), p = .aff r 0 hr

lemma isNonzeroTwoTorsion_iff {K : Type*} [Field K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) {b : K} (p : EbPoint K b) :
    IsNonzeroTwoTorsion p ↔ p ≠ .inf ∧ ebAdd p p = .inf := by
  cases p with
  | inf =>
    simp [IsNonzeroTwoTorsion]
  | aff x y h =>
    constructor
    · rintro ⟨r, hr, heq⟩
      cases heq
      simp [ebAdd]
    · rintro ⟨_, h2p⟩
      simp only [ebAdd, ↓reduceDIte] at h2p
      split_ifs at h2p with hy
      · have h2y : 2 * y = 0 := by linear_combination hy
        have hy0 : y = 0 := (mul_eq_zero.mp h2y).resolve_left h2
        subst hy0
        exact ⟨x, h, rfl⟩

lemma rcbEval_smul {K : Type*} [CommRing K] (b c₁ c₂ : K) (P₁ P₂ : Fin 3 → K) :
    rcbEval b (c₁ • P₁) (c₂ • P₂) = (c₁ ^ 2 * c₂ ^ 2) • rcbEval b P₁ P₂ := by
  funext k
  fin_cases k <;> simp [rcbEval, rcbX, rcbY, rcbZ] <;> ring

/-- **Theorem 1.2(4) (Bosma–Lenstra base-locus characterization & group-law correctness):**
Over any field `K` (`char K ≠ 2, 3`, `b ≠ 0`), for all `p₁, p₂ : EbPoint K b`:
1. `rcbEval b p₁.toProj p₂.toProj = 0 ↔ p₁ - p₂ ∈ E_b(K)[2] \ {O}`.
2. Whenever `p₁ - p₂ ∉ E_b(K)[2] \ {O}`, `rcbEval b p₁.toProj p₂.toProj` is projectively equal
   to `(p₁ + p₂).toProj` in `ℙ²(K)`. -/
theorem rcb_bosma_lenstra_ebPoint {K : Type*} [Field K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {b : K} (hb : b ≠ 0)
    (p₁ p₂ : EbPoint K b) :
    (rcbEval b p₁.toProj p₂.toProj = 0 ↔ IsNonzeroTwoTorsion (ebSub p₁ p₂)) ∧
    (¬ IsNonzeroTwoTorsion (ebSub p₁ p₂) →
      ProjEquiv (rcbEval b p₁.toProj p₂.toProj) (ebAdd p₁ p₂).toProj) := by
  have h8 : (8 : K) ≠ 0 := by
    have : (8 : K) = 2 * 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero (mul_ne_zero h2 h2) h2
  have h27 : (27 : K) ≠ 0 := by
    have : (27 : K) = 3 * 3 * 3 := by norm_num
    rw [this]; exact mul_ne_zero (mul_ne_zero h3 h3) h3
  cases p₁ with
  | inf =>
    cases p₂ with
    | inf =>
      have hval : rcbEval b (EbPoint.inf : EbPoint K b).toProj
          (EbPoint.inf : EbPoint K b).toProj = ![0, 1, 0] := by
        funext k; fin_cases k <;> simp [rcbEval, rcbX, rcbY, rcbZ, EbPoint.toProj]
      refine ⟨⟨fun h0 => ?_, fun ⟨_, _, h⟩ => by simp [ebSub, ebNeg, ebAdd] at h⟩,
        fun _ => ⟨1, one_ne_zero, by rw [hval, one_smul]; rfl⟩⟩
      have := congrFun h0 1
      simp [hval] at this
    | aff x₂ y₂ h₂ =>
      have hval : rcbEval b (EbPoint.inf : EbPoint K b).toProj
          (EbPoint.aff x₂ y₂ h₂).toProj = y₂ • ![x₂, y₂, 1] := by
        funext k; (fin_cases k <;> simp [rcbEval, rcbX, rcbY, rcbZ, EbPoint.toProj]); ring
      refine ⟨?_, ?_⟩
      · constructor
        · intro h0
          have hz := congrFun h0 2
          simp [hval] at hz
          subst hz
          exact ⟨x₂, h₂, by simp [ebSub, ebNeg, ebAdd]⟩
        · rintro ⟨r, hr, heq⟩
          simp only [ebSub, ebNeg, ebAdd, EbPoint.aff.injEq] at heq
          have hy0 : y₂ = 0 := neg_eq_zero.mp heq.2
          subst hy0
          simp [hval]
      · intro hnot
        have hy₂ : y₂ ≠ 0 := by
          intro hy0; subst hy0
          exact hnot ⟨x₂, h₂, by simp [ebSub, ebNeg, ebAdd]⟩
        exact ⟨y₂, hy₂, hval⟩
  | aff x₁ y₁ h₁ =>
    cases p₂ with
    | inf =>
      have hval : rcbEval b (EbPoint.aff x₁ y₁ h₁).toProj
          (EbPoint.inf : EbPoint K b).toProj = y₁ • ![x₁, y₁, 1] := by
        funext k; (fin_cases k <;> simp [rcbEval, rcbX, rcbY, rcbZ, EbPoint.toProj]); ring
      refine ⟨?_, ?_⟩
      · constructor
        · intro h0
          have hz := congrFun h0 2
          simp [hval] at hz
          subst hz
          exact ⟨x₁, h₁, by simp [ebSub, ebNeg, ebAdd]⟩
        · rintro ⟨r, hr, heq⟩
          simp only [ebSub, ebNeg, ebAdd, EbPoint.aff.injEq] at heq
          rcases heq with ⟨_, rfl⟩
          simp [hval]
      · intro hnot
        have hy₁ : y₁ ≠ 0 := by
          intro hy0; subst hy0
          exact hnot ⟨x₁, h₁, by simp [ebSub, ebNeg, ebAdd]⟩
        exact ⟨y₁, hy₁, hval⟩
    | aff x₂ y₂ h₂ =>
      by_cases hx : x₁ = x₂
      · subst hx
        have hsq : (y₁ - y₂) * (y₁ + y₂) = 0 := by
          calc (y₁ - y₂) * (y₁ + y₂) = y₁ ^ 2 - y₂ ^ 2 := by ring
            _ = (x₁ ^ 3 + b) - (x₁ ^ 3 + b) := by rw [h₁, h₂]
            _ = 0 := sub_self _
        by_cases hy_eq : y₁ = y₂
        · subst hy_eq
          have hsub_inf : ebSub (.aff x₁ y₁ h₁) (.aff x₁ y₁ h₂) = .inf := by
            simp [ebSub, ebNeg, ebAdd]
          have hnot_tor : ¬ IsNonzeroTwoTorsion (ebSub (.aff x₁ y₁ h₁) (.aff x₁ y₁ h₂)) := by
            rw [hsub_inf]; rintro ⟨_, _, h⟩; cases h
          by_cases hy0 : y₁ = 0
          · subst hy0
            have hadd_inf : ebAdd (.aff x₁ 0 h₁) (.aff x₁ 0 h₂) = .inf := by simp [ebAdd]
            have hval : rcbEval b (EbPoint.aff x₁ 0 h₁).toProj (EbPoint.aff x₁ 0 h₂).toProj =
                (-27 * b ^ 2) • ![0, 1, 0] := by
              funext k
              fin_cases k
              · simp [rcbEval, rcbX, EbPoint.toProj]
              · simp only [Fin.mk_one, Fin.isValue, rcbEval, rcbY, EbPoint.toProj,
                  Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val, Pi.smul_apply,
                  smul_eq_mul, mul_one]
                linear_combination -18 * b * h₁
              · simp [rcbEval, rcbZ, EbPoint.toProj]
            have hc_ne : -27 * b ^ 2 ≠ 0 :=
              mul_ne_zero (neg_ne_zero.mpr h27) (pow_ne_zero 2 hb)
            refine ⟨⟨fun h0 => ?_, fun ht => absurd ht hnot_tor⟩,
              fun _ => ⟨-27 * b ^ 2, hc_ne, by rw [hval, hadd_inf, EbPoint.toProj]⟩⟩
            have hy_coord := congrFun h0 1
            simp only [hval, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one,
              Matrix.cons_val_zero, mul_one, Pi.zero_apply] at hy_coord
            exact absurd hy_coord hc_ne
          · -- Doubling case `p₁ = p₂` with `y₁ ≠ 0`:
            have hy_sum_ne : y₁ + y₁ ≠ 0 := by
              intro h0
              have h2y : 2 * y₁ = 0 := by linear_combination h0
              exact hy0 ((mul_eq_zero.mp h2y).resolve_left h2)
            let lam := (3 * x₁ ^ 2) * (2 * y₁)⁻¹
            let x₃ := lam ^ 2 - 2 * x₁
            let y₃ := lam * (x₁ - x₃) - y₁
            have htan : 2 * y₁ * lam - 3 * x₁ ^ 2 = 0 := by
              dsimp [lam]
              have h2y : 2 * y₁ ≠ 0 := mul_ne_zero h2 hy0
              calc 2 * y₁ * (3 * x₁ ^ 2 * (2 * y₁)⁻¹) - 3 * x₁ ^ 2
                  = 3 * x₁ ^ 2 * ((2 * y₁) * (2 * y₁)⁻¹ - 1) := by ring
                _ = 0 := by rw [mul_inv_cancel₀ h2y, sub_self, mul_zero]
            have hE₁ : y₁ ^ 2 - x₁ ^ 3 - b = 0 := by linear_combination h₁
            have hZ : rcbZ b ![x₁, y₁, 1] ![x₁, y₁, 1] = 8 * y₁ ^ 3 := by
              simp only [rcbZ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
              linear_combination -6 * y₁ * hE₁
            have hX : rcbX b ![x₁, y₁, 1] ![x₁, y₁, 1] = 8 * y₁ ^ 3 * x₃ := by
              simp only [rcbX, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, x₃]
              linear_combination -2 * y₁ * (2 * y₁ * lam + 3 * x₁ ^ 2) * htan + 18 * x₁ * y₁ * hE₁
            have hY : rcbY b ![x₁, y₁, 1] ![x₁, y₁, 1] = 8 * y₁ ^ 3 * y₃ := by
              simp only [rcbY, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, x₃, y₃]
              linear_combination
                ((2 * y₁ * lam) ^ 2 + 6 * x₁ ^ 2 * y₁ * lam + 9 * x₁ ^ 4 - 12 * x₁ * y₁ ^ 2) * htan +
                9 * (y₁ ^ 2 - 3 * x₁ ^ 3 + b) * hE₁
            have hval : rcbEval b (EbPoint.aff x₁ y₁ h₁).toProj (EbPoint.aff x₁ y₁ h₂).toProj =
                (8 * y₁ ^ 3) • (ebAdd (.aff x₁ y₁ h₁) (.aff x₁ y₁ h₂)).toProj := by
              simp only [ebAdd, ↓reduceDIte, hy_sum_ne, EbPoint.toProj]
              funext k
              fin_cases k
              · simpa [rcbEval, x₃, lam] using hX
              · simpa [rcbEval, x₃, y₃, lam] using hY
              · simpa [rcbEval] using hZ
            have hc_ne : 8 * y₁ ^ 3 ≠ 0 := mul_ne_zero h8 (pow_ne_zero 3 hy0)
            refine ⟨⟨fun h0 => ?_, fun ht => absurd ht hnot_tor⟩,
              fun _ => ⟨8 * y₁ ^ 3, hc_ne, hval⟩⟩
            have hz_coord := congrFun h0 2
            simp [EbPoint.toProj, rcbEval, hZ, hc_ne] at hz_coord
        · -- Opposite case `p₂ = -p₁` with `y₁ ≠ 0` (`y₂ = -y₁`):
          have hy_sum : y₁ + y₂ = 0 :=
            (mul_eq_zero.mp hsq).resolve_left (sub_ne_zero.mpr hy_eq)
          have hy₂ : y₂ = -y₁ := eq_neg_of_add_eq_zero_right hy_sum
          have hy₁_ne : y₁ ≠ 0 := by
            intro h0; apply hy_eq; rw [hy₂, h0, neg_zero]
          have hy_dbl_ne : y₁ + -y₂ ≠ 0 := by
            rw [hy₂, neg_neg]
            intro h0
            have h2y : 2 * y₁ = 0 := by linear_combination h0
            exact hy₁_ne ((mul_eq_zero.mp h2y).resolve_left h2)
          let lam := (3 * x₁ ^ 2) * (2 * y₁)⁻¹
          let x₃ := lam ^ 2 - 2 * x₁
          let y₃ := lam * (x₁ - x₃) - y₁
          have htan : 2 * y₁ * lam - 3 * x₁ ^ 2 = 0 := by
            dsimp [lam]
            have h2y : 2 * y₁ ≠ 0 := mul_ne_zero h2 hy₁_ne
            calc 2 * y₁ * (3 * x₁ ^ 2 * (2 * y₁)⁻¹) - 3 * x₁ ^ 2
                = 3 * x₁ ^ 2 * ((2 * y₁) * (2 * y₁)⁻¹ - 1) := by ring
              _ = 0 := by rw [mul_inv_cancel₀ h2y, sub_self, mul_zero]
          have hE₁ : y₁ ^ 2 - x₁ ^ 3 - b = 0 := by linear_combination h₁
          have hcurve₃ : y₃ ^ 2 = x₃ ^ 3 + b := by
            dsimp [x₃, y₃]
            linear_combination h₁ + (lam ^ 2 - 3 * x₁) * htan
          have hsub_eq : ebSub (.aff x₁ y₁ h₁) (.aff x₁ y₂ h₂) = .aff x₃ y₃ hcurve₃ := by
            simp [ebSub, ebNeg, ebAdd, hy_dbl_ne, x₃, y₃, lam]
          have hX0 : rcbX b ![x₁, y₁, 1] ![x₁, y₂, 1] = 0 := by
            rw [hy₂]; simp [rcbX]
          have hZ0 : rcbZ b ![x₁, y₁, 1] ![x₁, y₂, 1] = 0 := by
            rw [hy₂]; simp [rcbZ]
          have hY_opp : rcbY b ![x₁, y₁, 1] ![x₁, y₂, 1] = 8 * y₁ ^ 3 * y₃ := by
            rw [hy₂]
            simp only [rcbY, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, x₃, y₃]
            linear_combination
              ((2 * y₁ * lam) ^ 2 + 6 * x₁ ^ 2 * y₁ * lam + 9 * x₁ ^ 4 - 12 * x₁ * y₁ ^ 2) * htan +
              9 * (y₁ ^ 2 - 3 * x₁ ^ 3 + b) * hE₁
          have hc_ne : 8 * y₁ ^ 3 ≠ 0 := mul_ne_zero h8 (pow_ne_zero 3 hy₁_ne)
          have hadd_inf : ebAdd (.aff x₁ y₁ h₁) (.aff x₁ y₂ h₂) = .inf := by
            simp [ebAdd, hy_sum]
          refine ⟨?_, ?_⟩
          · constructor
            · intro h0
              have hy_coord := congrFun h0 1
              simp only [EbPoint.toProj, rcbEval, Matrix.cons_val_one, Matrix.cons_val_zero,
                Pi.zero_apply, hY_opp] at hy_coord
              have hy₃_0 : y₃ = 0 := (mul_eq_zero.mp hy_coord).resolve_left hc_ne
              rw [hsub_eq]
              exact ⟨x₃, by rw [← hy₃_0]; exact hcurve₃, by simp [hy₃_0]⟩
            · rw [hsub_eq]
              rintro ⟨r, hr, heq⟩
              simp only [EbPoint.aff.injEq] at heq
              have hy₃_0 : y₃ = 0 := heq.2
              funext k
              fin_cases k
              · simpa [EbPoint.toProj, rcbEval] using hX0
              · simp [EbPoint.toProj, rcbEval, hY_opp, hy₃_0]
              · simpa [EbPoint.toProj, rcbEval] using hZ0
          · intro hnot
            have hy₃_ne : y₃ ≠ 0 := by
              intro hy₃_0
              apply hnot
              rw [hsub_eq]
              exact ⟨x₃, by rw [← hy₃_0]; exact hcurve₃, by simp [hy₃_0]⟩
            refine ⟨8 * y₁ ^ 3 * y₃, mul_ne_zero hc_ne hy₃_ne, ?_⟩
            rw [hadd_inf]
            funext k
            fin_cases k
            · simpa [EbPoint.toProj, rcbEval] using hX0
            · simp [EbPoint.toProj, rcbEval, hY_opp]
            · simpa [EbPoint.toProj, rcbEval] using hZ0
      · -- Chord case `x₁ ≠ x₂`:
        have hdx : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
        have hdx12 : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
        let lam := (y₂ - y₁) * (x₂ - x₁)⁻¹
        let xs := lam ^ 2 - x₁ - x₂
        let ys := lam * (x₁ - xs) - y₁
        let mu := (y₁ + y₂) * (x₁ - x₂)⁻¹
        let xd := mu ^ 2 - x₁ - x₂
        let yd := mu * (x₁ - xd) - y₁
        have hL : (x₂ - x₁) * lam - (y₂ - y₁) = 0 := by
          dsimp [lam]
          calc (x₂ - x₁) * ((y₂ - y₁) * (x₂ - x₁)⁻¹) - (y₂ - y₁)
              = (y₂ - y₁) * ((x₂ - x₁) * (x₂ - x₁)⁻¹ - 1) := by ring
            _ = 0 := by rw [mul_inv_cancel₀ hdx12, sub_self, mul_zero]
        have hM : (x₁ - x₂) * mu - (y₁ + y₂) = 0 := by
          dsimp [mu]
          calc (x₁ - x₂) * ((y₁ + y₂) * (x₁ - x₂)⁻¹) - (y₁ + y₂)
              = (y₁ + y₂) * ((x₁ - x₂) * (x₁ - x₂)⁻¹ - 1) := by ring
            _ = 0 := by rw [mul_inv_cancel₀ hdx, sub_self, mul_zero]
        have hE₁ : y₁ ^ 2 - x₁ ^ 3 - b = 0 := by linear_combination h₁
        have hE₂ : y₂ ^ 2 - x₂ ^ 3 - b = 0 := by linear_combination h₂
        have hd_curve : yd ^ 2 = xd ^ 3 + b := by
          have hy₂_rel : -y₂ = y₁ - mu * (x₁ - x₂) := by linear_combination hM
          have hsec_mul : (x₂ - x₁) *
              (2 * y₁ * mu + (x₂ - x₁) * mu ^ 2 - (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2)) = 0 := by
            have hdiff : (-y₂) ^ 2 - x₂ ^ 3 - (y₁ ^ 2 - x₁ ^ 3) = 0 := by
              linear_combination h₂ - h₁
            rw [hy₂_rel] at hdiff
            linear_combination hdiff
          have hsec : 2 * y₁ * mu + (x₂ - x₁) * mu ^ 2 - (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2) = 0 :=
            (mul_eq_zero.mp hsec_mul).resolve_left hdx12
          dsimp [xd, yd]
          linear_combination h₁ + (mu ^ 2 - 2 * x₁ - x₂) * hsec
        have hsub_aff : ebSub (.aff x₁ y₁ h₁) (.aff x₂ y₂ h₂) = .aff xd yd hd_curve := by
          simp only [ebSub, ebNeg, ebAdd, hx, ↓reduceDIte, EbPoint.aff.injEq]
          have hmu_eq : (-y₂ - y₁) * (x₂ - x₁)⁻¹ = mu := by
            dsimp [mu]
            simp only [← div_eq_mul_inv]
            field_simp [hdx, hdx12]
            ring
          dsimp [xd, yd]
          simp [hmu_eq]
        have hZ : rcbZ b ![x₁, y₁, 1] ![x₂, y₂, 1] = -(x₁ - x₂) ^ 3 * yd := by
          simp only [rcbZ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, xd, yd]
          linear_combination
            ((x₁ - x₂) ^ 2 * (2 * x₁ + x₂) -
              (((x₁ - x₂) * mu) ^ 2 + (x₁ - x₂) * mu * (y₁ + y₂) + (y₁ + y₂) ^ 2)) * hM -
            (2 * y₂ + y₁) * hE₁ - (y₂ + 2 * y₁) * hE₂
        have hX_mul : (x₂ - x₁) ^ 2 * rcbX b ![x₁, y₁, 1] ![x₂, y₂, 1] =
            (x₂ - x₁) ^ 2 * (rcbZ b ![x₁, y₁, 1] ![x₂, y₂, 1] * xs) := by
          have hxs_eq : (x₂ - x₁) ^ 2 * xs =
              (y₂ - y₁) ^ 2 - (x₁ + x₂) * (x₂ - x₁) ^ 2 := by
            dsimp [xs]
            linear_combination ((x₂ - x₁) * lam + (y₂ - y₁)) * hL
          calc (x₂ - x₁) ^ 2 * rcbX b ![x₁, y₁, 1] ![x₂, y₂, 1]
              = ((y₂ - y₁) ^ 2 - (x₁ + x₂) * (x₂ - x₁) ^ 2) *
                  rcbZ b ![x₁, y₁, 1] ![x₂, y₂, 1] := by
                    simp only [rcbX, rcbZ, Matrix.cons_val_zero, Matrix.cons_val_one,
                      Matrix.cons_val]
                    linear_combination
                      (2 * y₂ * b + y₂ ^ 3 + 2 * x₂ ^ 3 * y₂ - 3 * y₁ * b + y₁ * y₂ ^ 2 -
                        y₁ ^ 2 * y₂ + 3 * x₁ * x₂ ^ 2 * y₂ - 3 * x₁ * y₁ * x₂ ^ 2 -
                        3 * x₁ ^ 2 * x₂ * y₂) * hE₁ +
                      (-2 * y₂ * b + 3 * y₁ * b - y₁ * y₂ ^ 2 - 3 * x₁ * y₁ * x₂ ^ 2 -
                        3 * x₁ ^ 2 * x₂ * y₂ + 3 * x₁ ^ 2 * y₁ * x₂ + x₁ ^ 3 * y₂ +
                        3 * x₁ ^ 3 * y₁) * hE₂
            _ = (x₂ - x₁) ^ 2 * (rcbZ b ![x₁, y₁, 1] ![x₂, y₂, 1] * xs) := by
                  rw [← hxs_eq]; ring
        have hX : rcbX b ![x₁, y₁, 1] ![x₂, y₂, 1] =
            rcbZ b ![x₁, y₁, 1] ![x₂, y₂, 1] * xs :=
          mul_left_cancel₀ (pow_ne_zero 2 hdx12) hX_mul
        have hY_mul : (x₂ - x₁) ^ 3 * rcbY b ![x₁, y₁, 1] ![x₂, y₂, 1] =
            (x₂ - x₁) ^ 3 * (rcbZ b ![x₁, y₁, 1] ![x₂, y₂, 1] * ys) := by
          let ys_num := (y₂ - y₁) * (x₁ * (x₂ - x₁) ^ 2 -
              ((y₂ - y₁) ^ 2 - (x₁ + x₂) * (x₂ - x₁) ^ 2)) - y₁ * (x₂ - x₁) ^ 3
          have hys_eq : (x₂ - x₁) ^ 3 * ys = ys_num := by
            dsimp [ys, xs, ys_num]
            linear_combination
              ((x₂ - x₁) ^ 2 * (2 * x₁ + x₂) -
                (((x₂ - x₁) * lam) ^ 2 + (x₂ - x₁) * lam * (y₂ - y₁) + (y₂ - y₁) ^ 2)) * hL
          calc (x₂ - x₁) ^ 3 * rcbY b ![x₁, y₁, 1] ![x₂, y₂, 1]
              = ys_num * rcbZ b ![x₁, y₁, 1] ![x₂, y₂, 1] := by
                  dsimp [ys_num]
                  simp only [rcbY, rcbZ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
                  linear_combination
                    (-3 * b ^ 2 + 2 * y₂ ^ 2 * b - 2 * y₂ ^ 4 + 6 * x₂ ^ 3 * b +
                      2 * x₂ ^ 3 * y₂ ^ 2 + 5 * y₁ * y₂ * b + 2 * y₁ * x₂ ^ 3 * y₂ -
                      3 * y₁ ^ 2 * b + 2 * y₁ ^ 2 * y₂ ^ 2 - y₁ ^ 3 * y₂ - 12 * x₁ * x₂ ^ 2 * b -
                      15 * x₁ * x₂ ^ 2 * y₂ ^ 2 + 6 * x₁ * x₂ ^ 5 + 6 * x₁ * y₁ * x₂ ^ 2 * y₂ -
                      3 * x₁ * y₁ ^ 2 * x₂ ^ 2 + 15 * x₁ ^ 2 * x₂ * y₂ ^ 2 - 9 * x₁ ^ 2 * x₂ ^ 4 -
                      3 * x₁ ^ 2 * y₁ * x₂ * y₂) * hE₁ +
                    (3 * b ^ 2 + y₂ ^ 2 * b - 5 * y₁ * y₂ * b + y₁ * y₂ ^ 3 -
                      15 * x₁ * x₂ ^ 2 * b + 3 * x₁ * y₁ * x₂ ^ 2 * y₂ + 27 * x₁ ^ 2 * x₂ * b +
                      3 * x₁ ^ 2 * x₂ * y₂ ^ 2 - 6 * x₁ ^ 2 * y₁ * x₂ * y₂ - 6 * x₁ ^ 3 * b -
                      2 * x₁ ^ 3 * y₂ ^ 2 - 2 * x₁ ^ 3 * y₁ * y₂ - 6 * x₁ ^ 4 * x₂ ^ 2 +
                      9 * x₁ ^ 5 * x₂) * hE₂
            _ = (x₂ - x₁) ^ 3 * (rcbZ b ![x₁, y₁, 1] ![x₂, y₂, 1] * ys) := by
                  rw [← hys_eq]; ring
        have hY : rcbY b ![x₁, y₁, 1] ![x₂, y₂, 1] =
            rcbZ b ![x₁, y₁, 1] ![x₂, y₂, 1] * ys :=
          mul_left_cancel₀ (pow_ne_zero 3 hdx12) hY_mul
        have hdx3_ne : -(x₁ - x₂) ^ 3 ≠ 0 := neg_ne_zero.mpr (pow_ne_zero 3 hdx)
        refine ⟨?_, ?_⟩
        · constructor
          · intro h0
            have hz_coord := congrFun h0 2
            simp only [EbPoint.toProj, rcbEval, hZ, Pi.zero_apply] at hz_coord
            have hyd0 : yd = 0 := (mul_eq_zero.mp hz_coord).resolve_left hdx3_ne
            rw [hsub_aff]
            exact ⟨xd, by rw [← hyd0]; exact hd_curve, by simp [hyd0]⟩
          · rw [hsub_aff]
            rintro ⟨r, hr, heq⟩
            simp only [EbPoint.aff.injEq] at heq
            have hyd0 : yd = 0 := heq.2
            have hz0 : rcbZ b ![x₁, y₁, 1] ![x₂, y₂, 1] = 0 := by rw [hZ, hyd0, mul_zero]
            funext k
            fin_cases k
            · simp [EbPoint.toProj, rcbEval, hX, hz0]
            · simp [EbPoint.toProj, rcbEval, hY, hz0]
            · simp [EbPoint.toProj, rcbEval, hz0]
        · intro hnot
          have hyd_ne : yd ≠ 0 := by
            intro hyd0
            apply hnot
            rw [hsub_aff]
            exact ⟨xd, by rw [← hyd0]; exact hd_curve, by simp [hyd0]⟩
          have hz_ne : rcbZ b ![x₁, y₁, 1] ![x₂, y₂, 1] ≠ 0 := by
            rw [hZ]; exact mul_ne_zero hdx3_ne hyd_ne
          refine ⟨rcbZ b ![x₁, y₁, 1] ![x₂, y₂, 1], hz_ne, ?_⟩
          simp only [ebAdd, hx, ↓reduceDIte, EbPoint.toProj]
          funext k
          fin_cases k
          · simpa [rcbEval, xs, lam] using hX
          · simpa [rcbEval, xs, ys, lam] using hY
          · simp [rcbEval]

/-- Projective homogeneous form of Bosma–Lenstra base-locus characterization on `E_b(K)`. -/
theorem rcb_bosma_lenstra_proj {K : Type*} [Field K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {b : K} (hb : b ≠ 0)
    {P₁ P₂ : Fin 3 → K} (hP₁ : IsProjCurvePoint b P₁) (hP₂ : IsProjCurvePoint b P₂) :
    (rcbEval b P₁ P₂ = 0 ↔ IsNonzeroTwoTorsion (ebSub hP₁.toEbPoint hP₂.toEbPoint)) ∧
    (¬ IsNonzeroTwoTorsion (ebSub hP₁.toEbPoint hP₂.toEbPoint) →
      ProjEquiv (rcbEval b P₁ P₂) (ebAdd hP₁.toEbPoint hP₂.toEbPoint).toProj) := by
  rcases hP₁.projEquiv_toEbPoint with ⟨c₁, hc₁, h1⟩
  rcases hP₂.projEquiv_toEbPoint with ⟨c₂, hc₂, h2'⟩
  have hscale := rcbEval_smul b c₁ c₂ hP₁.toEbPoint.toProj hP₂.toEbPoint.toProj
  rw [← h1, ← h2'] at hscale
  have hc12 : c₁ ^ 2 * c₂ ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero 2 hc₁) (pow_ne_zero 2 hc₂)
  rcases rcb_bosma_lenstra_ebPoint h2 h3 hb hP₁.toEbPoint hP₂.toEbPoint with ⟨hiff, hproj⟩
  refine ⟨?_, ?_⟩
  · rw [hscale, smul_eq_zero, or_iff_right hc12, hiff]
  · intro hnot
    rcases hproj hnot with ⟨c, hc, heq⟩
    exact ⟨c₁ ^ 2 * c₂ ^ 2 * c, mul_ne_zero hc12 hc, by rw [hscale, heq, smul_smul]⟩

/-- **Theorem 1.2(4) (Unconditional completeness criterion on `E_b(K)`):**
The projective RCB law has no base-locus zeros on `E_b(K) × E_b(K)` if and only if
`b` is NOT a cube in `K`. -/
theorem rcb_unconditionally_complete_iff {K : Type*} [Field K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {b : K} (hb : b ≠ 0) :
    (∀ P₁ P₂ : Fin 3 → K, IsProjCurvePoint b P₁ → IsProjCurvePoint b P₂ →
      rcbEval b P₁ P₂ ≠ 0) ↔
    ¬ ∃ c : K, c ^ 3 = b := by
  constructor
  · intro hcomp ⟨c, hc⟩
    let P₁ : Fin 3 → K := ![-c, 0, 1]
    let P₂ : Fin 3 → K := ![0, 1, 0]
    have hP₁ : IsProjCurvePoint b P₁ := by
      refine ⟨?_, ?_⟩
      · intro h0; have := congrFun h0 2; simp [P₁] at this
      · simp only [P₁, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
        linear_combination hc
    have hP₂ : IsProjCurvePoint b P₂ := EbPoint.isProjCurvePoint (.inf : EbPoint K b)
    apply hcomp P₁ P₂ hP₁ hP₂
    funext k
    fin_cases k <;> simp [rcbEval, rcbX, rcbY, rcbZ, P₁, P₂]
  · intro hnocube P₁ P₂ hP₁ hP₂ hzero
    have htor := (rcb_bosma_lenstra_proj h2 h3 hb hP₁ hP₂).1.mp hzero
    rcases htor with ⟨r, hr, _⟩
    exact hnocube ⟨-r, by linear_combination hr⟩

/-- **Theorem 1.2(4) (Zero-spuriousness of the complexified scalar relation):**
When `-1` is not a square in `K` and `p₁ - p₂ ∉ E_b(K)[2] \ {O}`, the single `L`-scalar relation
`(X_+ + i Y_+) Z₃ - Z_+ (X₃ - i Y₃) = 0` holds if and only if `p₁ + p₂ + p₃ = O`. -/
theorem rcb_complex_scalar_relation_iff {K L : Type*} [Field K] [DecidableEq K] [Field L]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {b : K} (hb : b ≠ 0)
    (hnsq : ¬ IsSquare (-1 : K))
    (φ : K →+* L) {imUnit : L} (hi : imUnit ^ 2 = -1)
    (p₁ p₂ p₃ : EbPoint K b)
    (hnot_tor : ¬ IsNonzeroTwoTorsion (ebSub p₁ p₂)) :
    let Pplus := rcbEval b p₁.toProj p₂.toProj
    let P₃ := p₃.toProj
    (φ (Pplus 0) + imUnit * φ (Pplus 1)) * φ (P₃ 2) -
      φ (Pplus 2) * (φ (P₃ 0) - imUnit * φ (P₃ 1)) = 0 ↔
    ebAdd (ebAdd p₁ p₂) p₃ = .inf := by
  have hlin_indep : ∀ x y : K, φ x + imUnit * φ y = 0 → x = 0 ∧ y = 0 := by
    intro x y hxy
    by_cases hy : y = 0
    · subst hy
      simp only [map_zero, mul_zero, add_zero] at hxy
      exact ⟨φ.injective (by rw [hxy, map_zero]), rfl⟩
    · exfalso
      have hφy : φ y ≠ 0 := fun h0 => hy (φ.injective (by rw [h0, map_zero]))
      have him : imUnit = φ (-x * y⁻¹) := by
        calc imUnit = (-φ x) * (φ y)⁻¹ := by
                have heq : imUnit * φ y = -φ x := by linear_combination hxy
                rw [← heq, mul_assoc, mul_inv_cancel₀ hφy, mul_one]
          _ = φ (-x * y⁻¹) := by simp [map_mul, map_inv₀]
      have hsqL : φ ((-x * y⁻¹) * (-x * y⁻¹)) = φ (-1) := by
        rw [map_mul, ← him, ← sq, hi, map_neg, map_one]
      exact hnsq ⟨-x * y⁻¹, (φ.injective hsqL).symm⟩
  rcases (rcb_bosma_lenstra_ebPoint h2 h3 hb p₁ p₂).2 hnot_tor with ⟨c, hc, hproj⟩
  dsimp only
  rw [hproj]
  constructor
  · intro hrel
    have hcomb : φ ((c • (ebAdd p₁ p₂).toProj) 0 * p₃.toProj 2 -
          (c • (ebAdd p₁ p₂).toProj) 2 * p₃.toProj 0) +
        imUnit * φ ((c • (ebAdd p₁ p₂).toProj) 1 * p₃.toProj 2 +
          (c • (ebAdd p₁ p₂).toProj) 2 * p₃.toProj 1) = 0 := by
      simp only [map_sub, map_add, map_mul]
      linear_combination hrel
    obtain ⟨hre, him⟩ := hlin_indep _ _ hcomb
    cases hs : ebAdd p₁ p₂ with
    | inf =>
      rw [hs] at hre him
      cases p₃ with
      | inf => rfl
      | aff x₃ y₃ h₃ =>
        simp [EbPoint.toProj] at him
        exact absurd him hc
    | aff xs ys hs_curve =>
      rw [hs] at hre him
      cases p₃ with
      | inf =>
        simp [EbPoint.toProj] at him
        exact absurd him hc
      | aff x₃ y₃ h₃ =>
        simp only [EbPoint.toProj, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val, mul_one] at hre him
        have hx_eq : xs = x₃ := by
          have : c * (xs - x₃) = 0 := by linear_combination hre
          exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hc)
        have hy_sum : ys + y₃ = 0 := by
          have : c * (ys + y₃) = 0 := by linear_combination him
          exact (mul_eq_zero.mp this).resolve_left hc
        simp [ebAdd, hx_eq, hy_sum]
  · intro hsum0
    cases hs : ebAdd p₁ p₂ with
    | inf =>
      rw [hs, ebAdd] at hsum0
      subst hsum0
      simp [EbPoint.toProj]
    | aff xs ys hs_curve =>
      rw [hs] at hsum0
      cases p₃ with
      | inf =>
        simp [ebAdd] at hsum0
      | aff x₃ y₃ h₃ =>
        simp only [ebAdd] at hsum0
        split_ifs at hsum0 with hx_eq hy_sum
        · subst hx_eq
          have hy₃ : y₃ = -ys := eq_neg_of_add_eq_zero_right hy_sum
          subst hy₃
          simp [EbPoint.toProj]
          ring

/-- Scalar multiplication `[n]P` on `EbPoint K b`. -/
def ebNsmul {K : Type*} [Field K] [DecidableEq K] {b : K} : ℕ → EbPoint K b → EbPoint K b
  | 0, _ => .inf
  | n + 1, p => ebAdd p (ebNsmul n p)

instance fact_prime_67 : Fact (Nat.Prime 67) := ⟨by decide⟩

lemma ebAdd_dbl_of_eq {K : Type*} [Field K] [DecidableEq K] {b x₁ y₁ m x₃ y₃ : K}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 + b) (hy : y₁ + y₁ ≠ 0)
    (hm : m * (2 * y₁) = 3 * x₁ ^ 2)
    (hx₃ : x₃ = m ^ 2 - 2 * x₁) (hy₃ : y₃ = m * (x₁ - x₃) - y₁)
    (h₃ : y₃ ^ 2 = x₃ ^ 3 + b) :
    ebAdd (.aff x₁ y₁ h₁) (.aff x₁ y₁ h₁) = .aff x₃ y₃ h₃ := by
  have h2y : 2 * y₁ ≠ 0 := by intro h0; apply hy; linear_combination h0
  have hlam : 3 * x₁ ^ 2 * (2 * y₁)⁻¹ = m := by
    rw [← hm, mul_assoc, mul_inv_cancel₀ h2y, mul_one]
  simp only [ebAdd, ↓reduceDIte, hy, hlam, hx₃, hy₃]

lemma ebAdd_chord_of_eq {K : Type*} [Field K] [DecidableEq K] {b x₁ y₁ x₂ y₂ m x₃ y₃ : K}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 + b) (h₂ : y₂ ^ 2 = x₂ ^ 3 + b) (hx : x₁ ≠ x₂)
    (hm : m * (x₂ - x₁) = y₂ - y₁)
    (hx₃ : x₃ = m ^ 2 - x₁ - x₂) (hy₃ : y₃ = m * (x₁ - x₃) - y₁)
    (h₃ : y₃ ^ 2 = x₃ ^ 3 + b) :
    ebAdd (.aff x₁ y₁ h₁) (.aff x₂ y₂ h₂) = .aff x₃ y₃ h₃ := by
  have hdx : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr hx.symm
  have hlam : (y₂ - y₁) * (x₂ - x₁)⁻¹ = m := by
    rw [← hm, mul_assoc, mul_inv_cancel₀ hdx, mul_one]
  simp only [ebAdd, hx, ↓reduceDIte, hlam, hx₃, hy₃]

private def zmod67GX : ℕ → ZMod 67
  | 1 => 4 | 2 => 39 | 3 => 57 | 4 => 25 | 5 => 42 | 6 => 18 | 7 => 7 | 8 => 36 | 9 => 60
  | 10 => 59 | 11 => 33 | 12 => 53 | 13 => 11 | 14 => 0 | 15 => 6 | 16 => 54 | 17 => 26
  | 18 => 63 | 19 => 62 | 20 => 55 | 21 => 30 | 22 => 55 | 23 => 62 | 24 => 63 | 25 => 26
  | 26 => 54 | 27 => 6 | 28 => 0 | 29 => 11 | 30 => 53 | 31 => 33 | 32 => 59 | 33 => 60
  | 34 => 36 | 35 => 7 | 36 => 18 | 37 => 42 | 38 => 25 | 39 => 57 | 40 => 39 | 41 => 4
  | _ => 0

private def zmod67GY : ℕ → ZMod 67
  | 1 => 20 | 2 => 5 | 3 => 41 | 4 => 45 | 5 => 56 | 6 => 2 | 7 => 3 | 8 => 5 | 9 => 23
  | 10 => 62 | 11 => 48 | 12 => 2 | 13 => 40 | 14 => 1 | 15 => 4 | 16 => 45 | 17 => 36
  | 18 => 65 | 19 => 55 | 20 => 22 | 21 => 0 | 22 => 45 | 23 => 12 | 24 => 2 | 25 => 31
  | 26 => 22 | 27 => 63 | 28 => 66 | 29 => 27 | 30 => 65 | 31 => 19 | 32 => 5 | 33 => 44
  | 34 => 62 | 35 => 64 | 36 => 65 | 37 => 11 | 38 => 22 | 39 => 26 | 40 => 62 | 41 => 47
  | _ => 0

private def zmod67GSlope : ℕ → ZMod 67
  | 1 => 28 | 2 => 57 | 3 => 32 | 4 => 65 | 5 => 8 | 6 => 37 | 7 => 39 | 8 => 10 | 9 => 18
  | 10 => 30 | 11 => 31 | 12 => 1 | 13 => 22 | 14 => 55 | 15 => 59 | 16 => 34 | 17 => 19
  | 18 => 53 | 19 => 11 | 20 => 25 | 21 => 25 | 22 => 11 | 23 => 53 | 24 => 19 | 25 => 34
  | 26 => 59 | 27 => 55 | 28 => 22 | 29 => 1 | 30 => 31 | 31 => 30 | 32 => 18 | 33 => 10
  | 34 => 39 | 35 => 37 | 36 => 8 | 37 => 65 | 38 => 32 | 39 => 57 | 40 => 28
  | _ => 0

private lemma zmod67G_curve_fin :
    ∀ k : Fin 42, k.val ≠ 0 → (zmod67GY k.val) ^ 2 = (zmod67GX k.val) ^ 3 + 1 := by
  decide

private lemma zmod67G_curve (k : ℕ) (hk1 : 1 ≤ k) (hk41 : k ≤ 41) :
    (zmod67GY k) ^ 2 = (zmod67GX k) ^ 3 + 1 :=
  zmod67G_curve_fin ⟨k, by omega⟩ (by dsimp; omega)

private lemma zmod67G_chord :
    ∀ k : Fin 39,
      (4 : ZMod 67) ≠ zmod67GX (k.val + 2) ∧
      zmod67GSlope (k.val + 2) * (zmod67GX (k.val + 2) - 4) = zmod67GY (k.val + 2) - 20 ∧
      zmod67GX (k.val + 3) = (zmod67GSlope (k.val + 2)) ^ 2 - 4 - zmod67GX (k.val + 2) ∧
      zmod67GY (k.val + 3) = zmod67GSlope (k.val + 2) * (4 - zmod67GX (k.val + 3)) - 20 := by
  decide

private lemma zmod67_ebNsmul_table (k : ℕ) (hk1 : 1 ≤ k) (hk41 : k ≤ 41) :
    ebNsmul k (.aff (4 : ZMod 67) 20 (by decide) : EbPoint (ZMod 67) 1) =
      .aff (zmod67GX k) (zmod67GY k) (zmod67G_curve k hk1 hk41) := by
  induction k with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst hn0
      rfl
    · have hn1 : 1 ≤ n := by omega
      have hprev := ih hn1 (by omega)
      simp only [ebNsmul, hprev]
      by_cases hn_eq1 : n = 1
      · subst hn_eq1
        exact ebAdd_dbl_of_eq _ (by decide) (m := 28) (by decide) (by decide) (by decide) _
      · rcases zmod67G_chord ⟨n - 2, by omega⟩ with ⟨hne, hm, hx₃, hy₃⟩
        have hidx : (⟨n - 2, by omega⟩ : Fin 39).val + 2 = n := by dsimp; omega
        have hnxt : (⟨n - 2, by omega⟩ : Fin 39).val + 3 = n + 1 := by dsimp; omega
        rw [hidx] at hne hm hx₃
        rw [hnxt] at hx₃ hy₃
        rw [hidx] at hy₃
        exact ebAdd_chord_of_eq _ _ hne hm hx₃ hy₃ _

/-- **Theorem 1.2(4) (Kernel-verified `ZMod 67`, `b = 1` even-order base-locus witness):**
In `𝔽₆₇` (`-1` non-square), `G = (4, 20)` on `E₁ : y² = x³ + 1` has exact order `42`, with
`[21]G = (30, 0) ∈ E₁(𝔽₆₇)[2] \ {O}`, `[22]G = (55, 45)`, `[19]G = (62, 55) = -(G + [22]G)`,
and `RCB(G, [22]G) = (0, 0, 0)`. -/
theorem rcb_zmod67_base_locus_witness :
    let G : EbPoint (ZMod 67) (1 : ZMod 67) := .aff 4 20 (by decide)
    ¬ IsSquare (-1 : ZMod 67) ∧
    (∀ k : Fin 42, k.val ≠ 0 → ebNsmul k.val G ≠ .inf) ∧
    ebNsmul 42 G = .inf ∧
    ebNsmul 21 G = .aff 30 0 (by decide) ∧
    ebNsmul 22 G = .aff 55 45 (by decide) ∧
    ebNsmul 19 G = .aff 62 55 (by decide) ∧
    ebNeg (ebAdd G (ebNsmul 22 G)) = ebNsmul 19 G ∧
    rcbEval (1 : ZMod 67) G.toProj (ebNsmul 22 G).toProj = ![0, 0, 0] := by
  dsimp only
  let G : EbPoint (ZMod 67) (1 : ZMod 67) := .aff 4 20 (by decide)
  have h41 : ebNsmul 41 G = .aff 4 47 (by decide) := zmod67_ebNsmul_table 41 (by omega) (by omega)
  have h21 : ebNsmul 21 G = .aff 30 0 (by decide) := zmod67_ebNsmul_table 21 (by omega) (by omega)
  have h22 : ebNsmul 22 G = .aff 55 45 (by decide) := zmod67_ebNsmul_table 22 (by omega) (by omega)
  have h23 : ebNsmul 23 G = .aff 62 12 (by decide) := zmod67_ebNsmul_table 23 (by omega) (by omega)
  have h19 : ebNsmul 19 G = .aff 62 55 (by decide) := zmod67_ebNsmul_table 19 (by omega) (by omega)
  refine ⟨by decide, ?_, ?_, h21, h22, h19, ?_, ?_⟩
  · intro k hk0
    have hk1 : 1 ≤ k.val := Nat.pos_of_ne_zero hk0
    have hk41 : k.val ≤ 41 := Nat.le_sub_one_of_lt k.isLt
    rw [zmod67_ebNsmul_table k.val hk1 hk41]
    simp
  · change ebAdd G (ebNsmul 41 G) = .inf
    rw [h41]
    have hy0 : (20 : ZMod 67) + 47 = 0 := by decide
    simp [G, ebAdd, hy0]
  · have hadd22 : ebAdd G (ebNsmul 22 G) = ebNsmul 23 G := rfl
    rw [hadd22, h23, h19]
    simp only [ebNeg, EbPoint.aff.injEq, true_and]
    decide
  · rw [h22]
    funext i
    fin_cases i <;> decide

end SemaevRCB
