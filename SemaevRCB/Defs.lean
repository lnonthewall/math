module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

@[expose] public section

/-!
# Shared Definitions for `SemaevRCB`

Core definitions of 3-tensors, tensor rank, `(1,2)`-symmetric rank, formal algebraic
border rank, purely algebraic flattening lower bounds (Remark 2.3(a)), the Levi-Civita
tensor `ε₃`, its mode-shared double `I₂ ⊗₁,₂ ε₃`, and the Renes–Costello–Batina (RCB)
projective addition tensor `T_RCB` on `j = 0` elliptic curves `E_b : Y²Z = X³ + b Z³`.
-/

namespace SemaevRCB

open Matrix Polynomial BigOperators

/-- A 3-tensor over `K` indexed by `I × J × L`. -/
abbrev Tensor3 (K : Type*) (I J L : Type*) := I → J → L → K

/-- Pure (rank-1) 3-tensor `u ⊗ v ⊗ w`. -/
def rankOneTensor {K I J L : Type*} [Mul K] (u : I → K) (v : J → K) (w : L → K) :
    Tensor3 K I J L :=
  fun i j l => u i * v j * w l

/-- `T` has tensor rank at most `r` over `K`. -/
def HasTensorRankLe {K I J L : Type*} [CommSemiring K] (T : Tensor3 K I J L) (r : ℕ) : Prop :=
  ∃ (u : Fin r → I → K) (v : Fin r → J → K) (w : Fin r → L → K),
    ∀ i j l, T i j l = ∑ t, u t i * v t j * w t l

/-- `T` has `(1,2)`-symmetric rank at most `r` over `K`. -/
def HasSym12RankLe {K I L : Type*} [CommSemiring K] (T : Tensor3 K I I L) (r : ℕ) : Prop :=
  ∃ (u : Fin r → I → K) (w : Fin r → L → K),
    ∀ i j l, T i j l = ∑ t, u t i * u t j * w t l

/-- `T` has formal algebraic border rank at most `r` over `K` (cleared-denominator polynomial
form, equivalent to Laurent degeneration over `K[ε, ε⁻¹]`). -/
def HasFormalBorderRankLe {K I J L : Type*} [CommSemiring K]
    (T : Tensor3 K I J L) (r : ℕ) : Prop :=
  ∃ (d : ℕ) (U : Fin r → I → K[X]) (V : Fin r → J → K[X]) (W : Fin r → L → K[X])
    (E : I → J → L → K[X]),
    ∀ i j l, ∑ t, U t i * V t j * W t l = C (T i j l) * X ^ d + X ^ (d + 1) * E i j l

/-- `T` has `(1,2)`-symmetric formal algebraic border rank at most `r` over `K`. -/
def HasSym12FormalBorderRankLe {K I L : Type*} [CommSemiring K]
    (T : Tensor3 K I I L) (r : ℕ) : Prop :=
  ∃ (d : ℕ) (U : Fin r → I → K[X]) (W : Fin r → L → K[X]) (E : I → I → L → K[X]),
    ∀ i j l, ∑ t, U t i * U t j * W t l = C (T i j l) * X ^ d + X ^ (d + 1) * E i j l

/-- Base change of a 3-tensor along a ring homomorphism `φ : K →+* F`. -/
def baseChangeTensor {K F I J L : Type*} [CommSemiring K] [CommSemiring F]
    (φ : K →+* F) (T : Tensor3 K I J L) : Tensor3 F I J L :=
  fun i j l => φ (T i j l)

/-- Multilinear transformation `(A ⊗ B ⊗ C)(T)`. -/
def mapTensor {K I I' J J' L L' : Type*} [CommSemiring K]
    [Fintype I] [Fintype J] [Fintype L]
    (A : Matrix I' I K) (B : Matrix J' J K) (C : Matrix L' L K)
    (T : Tensor3 K I J L) : Tensor3 K I' J' L' :=
  fun i' j' l' => ∑ i, ∑ j, ∑ l, A i' i * B j' j * C l' l * T i j l

/-- `GL`-equivalence (isotopy) of 3-tensors over `K`. -/
def TensorEquiv {K I I' J J' L L' : Type*} [CommRing K]
    [Fintype I] [Fintype I'] [Fintype J] [Fintype J'] [Fintype L] [Fintype L']
    [DecidableEq I] [DecidableEq I'] [DecidableEq J] [DecidableEq J']
    [DecidableEq L] [DecidableEq L']
    (T : Tensor3 K I J L) (T' : Tensor3 K I' J' L') : Prop :=
  ∃ (A : Matrix I' I K) (Ai : Matrix I I' K)
    (B : Matrix J' J K) (Bi : Matrix J J' K)
    (C : Matrix L' L K) (Ci : Matrix L L' K),
    A * Ai = 1 ∧ Ai * A = 1 ∧ B * Bi = 1 ∧ Bi * B = 1 ∧ C * Ci = 1 ∧ Ci * C = 1 ∧
    mapTensor A B C T = T'

/-- `(1,2)`-congruence `(A ⊗ A ⊗ C)(T) = T'` with invertible `A, C`. -/
def TensorSym12Congruent {K I I' L L' : Type*} [CommRing K]
    [Fintype I] [Fintype I'] [Fintype L] [Fintype L']
    [DecidableEq I] [DecidableEq I'] [DecidableEq L] [DecidableEq L']
    (T : Tensor3 K I I L) (T' : Tensor3 K I' I' L') : Prop :=
  ∃ (A : Matrix I' I K) (Ai : Matrix I I' K)
    (C : Matrix L' L K) (Ci : Matrix L L' K),
    A * Ai = 1 ∧ Ai * A = 1 ∧ C * Ci = 1 ∧ Ci * C = 1 ∧
    mapTensor A A C T = T'

lemma HasSym12RankLe.toTensorRankLe {K I L : Type*} [CommSemiring K]
    {T : Tensor3 K I I L} {r : ℕ} (h : HasSym12RankLe T r) : HasTensorRankLe T r := by
  rcases h with ⟨u, w, hT⟩
  exact ⟨u, u, w, hT⟩

lemma HasTensorRankLe.toFormalBorderRankLe {K I J L : Type*} [CommSemiring K]
    {T : Tensor3 K I J L} {r : ℕ} (h : HasTensorRankLe T r) : HasFormalBorderRankLe T r := by
  rcases h with ⟨u, v, w, hT⟩
  refine ⟨0, fun t i => C (u t i), fun t j => C (v t j), fun t l => C (w t l),
    fun _ _ _ => 0, fun i j l => ?_⟩
  simp only [pow_zero, mul_one, mul_zero, add_zero, ← map_mul, ← map_sum, hT i j l]

lemma HasSym12RankLe.toSym12FormalBorderRankLe {K I L : Type*} [CommSemiring K]
    {T : Tensor3 K I I L} {r : ℕ} (h : HasSym12RankLe T r) :
    HasSym12FormalBorderRankLe T r := by
  rcases h with ⟨u, w, hT⟩
  refine ⟨0, fun t i => C (u t i), fun t l => C (w t l), fun _ _ _ => 0, fun i j l => ?_⟩
  simp only [pow_zero, mul_one, mul_zero, add_zero, ← map_mul, ← map_sum, hT i j l]

lemma HasSym12FormalBorderRankLe.toFormalBorderRankLe {K I L : Type*} [CommSemiring K]
    {T : Tensor3 K I I L} {r : ℕ} (h : HasSym12FormalBorderRankLe T r) :
    HasFormalBorderRankLe T r := by
  rcases h with ⟨d, U, W, E, hT⟩
  exact ⟨d, U, U, W, E, hT⟩

lemma HasTensorRankLe.mono {K I J L : Type*} [CommSemiring K]
    {T : Tensor3 K I J L} {r r' : ℕ} (h : HasTensorRankLe T r) (hrr : r ≤ r') :
    HasTensorRankLe T r' := by
  rcases h with ⟨u, v, w, hT⟩
  refine ⟨fun t i => if ht : t.1 < r then u ⟨t.1, ht⟩ i else 0,
    fun t j => if ht : t.1 < r then v ⟨t.1, ht⟩ j else 0,
    fun t l => if ht : t.1 < r then w ⟨t.1, ht⟩ l else 0, fun i j l => ?_⟩
  rw [hT i j l]
  symm
  calc
    ∑ t : Fin r', (if ht : t.1 < r then u ⟨t.1, ht⟩ i else 0) *
        (if ht : t.1 < r then v ⟨t.1, ht⟩ j else 0) *
        (if ht : t.1 < r then w ⟨t.1, ht⟩ l else 0)
      = ∑ t : Fin r', if ht : t.1 < r then u ⟨t.1, ht⟩ i * v ⟨t.1, ht⟩ j * w ⟨t.1, ht⟩ l
        else 0 := by
          refine Finset.sum_congr rfl fun t _ => ?_
          split_ifs <;> simp
    _ = ∑ t : Fin r, u t i * v t j * w t l := by
          rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter fun t : Fin r' => t.1 < r))]
          · refine (Finset.sum_bij (fun (t : Fin r) _ => ⟨t.1, lt_of_lt_of_le t.2 hrr⟩)
              (fun t _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, t.2⟩) ?_ ?_ ?_).symm
            · intro a _ b _ hab
              exact Fin.ext (by simpa using congrArg Fin.val hab)
            · intro b hb
              have hlt : b.1 < r := (Finset.mem_filter.mp hb).2
              exact ⟨⟨b.1, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩
            · intro a _
              simp [a.2]
          · intro b _ hb
            have hnot : ¬ b.1 < r := by simpa [Finset.mem_filter] using hb
            simp [hnot]

lemma HasSym12RankLe.mono {K I L : Type*} [CommSemiring K]
    {T : Tensor3 K I I L} {r r' : ℕ} (h : HasSym12RankLe T r) (hrr : r ≤ r') :
    HasSym12RankLe T r' := by
  rcases h with ⟨u, w, hT⟩
  refine ⟨fun t i => if ht : t.1 < r then u ⟨t.1, ht⟩ i else 0,
    fun t l => if ht : t.1 < r then w ⟨t.1, ht⟩ l else 0, fun i j l => ?_⟩
  rw [hT i j l]
  symm
  calc
    ∑ t : Fin r', (if ht : t.1 < r then u ⟨t.1, ht⟩ i else 0) *
        (if ht : t.1 < r then u ⟨t.1, ht⟩ j else 0) *
        (if ht : t.1 < r then w ⟨t.1, ht⟩ l else 0)
      = ∑ t : Fin r', if ht : t.1 < r then u ⟨t.1, ht⟩ i * u ⟨t.1, ht⟩ j * w ⟨t.1, ht⟩ l
        else 0 := by
          refine Finset.sum_congr rfl fun t _ => ?_
          split_ifs <;> simp
    _ = ∑ t : Fin r, u t i * u t j * w t l := by
          rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter fun t : Fin r' => t.1 < r))]
          · refine (Finset.sum_bij (fun (t : Fin r) _ => ⟨t.1, lt_of_lt_of_le t.2 hrr⟩)
              (fun t _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, t.2⟩) ?_ ?_ ?_).symm
            · intro a _ b _ hab
              exact Fin.ext (by simpa using congrArg Fin.val hab)
            · intro b hb
              have hlt : b.1 < r := (Finset.mem_filter.mp hb).2
              exact ⟨⟨b.1, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩
            · intro a _
              simp [a.2]
          · intro b _ hb
            have hnot : ¬ b.1 < r := by simpa [Finset.mem_filter] using hb
            simp [hnot]

lemma HasTensorRankLe.mapTensor {K I I' J J' L L' : Type*} [CommSemiring K]
    [Fintype I] [Fintype J] [Fintype L]
    {T : Tensor3 K I J L} {r : ℕ} (h : HasTensorRankLe T r)
    (A : Matrix I' I K) (B : Matrix J' J K) (C : Matrix L' L K) :
    HasTensorRankLe (mapTensor A B C T) r := by
  rcases h with ⟨u, v, w, hT⟩
  refine ⟨fun t i' => ∑ i, A i' i * u t i,
    fun t j' => ∑ j, B j' j * v t j,
    fun t l' => ∑ l, C l' l * w t l, fun i' j' l' => ?_⟩
  simp only [SemaevRCB.mapTensor, hT]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext i
    rw [Finset.sum_comm]
    arg 2; ext j
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext j
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

lemma HasSym12RankLe.mapSym12 {K I I' L L' : Type*} [CommSemiring K]
    [Fintype I] [Fintype L]
    {T : Tensor3 K I I L} {r : ℕ} (h : HasSym12RankLe T r)
    (A : Matrix I' I K) (C : Matrix L' L K) :
    HasSym12RankLe (mapTensor A A C T) r := by
  rcases h with ⟨u, w, hT⟩
  refine ⟨fun t i' => ∑ i, A i' i * u t i,
    fun t l' => ∑ l, C l' l * w t l, fun i' j' l' => ?_⟩
  simp only [SemaevRCB.mapTensor, hT]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext i
    rw [Finset.sum_comm]
    arg 2; ext j
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext j
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

lemma HasFormalBorderRankLe.mapTensor {K I I' J J' L L' : Type*} [CommSemiring K]
    [Fintype I] [Fintype J] [Fintype L]
    {T : Tensor3 K I J L} {r : ℕ} (h : HasFormalBorderRankLe T r)
    (A : Matrix I' I K) (B : Matrix J' J K) (C_mat : Matrix L' L K) :
    HasFormalBorderRankLe (mapTensor A B C_mat T) r := by
  rcases h with ⟨d, U, V, W, E, hT⟩
  refine ⟨d,
    fun t i' => ∑ i, C (A i' i) * U t i,
    fun t j' => ∑ j, C (B j' j) * V t j,
    fun t l' => ∑ l, C (C_mat l' l) * W t l,
    fun i' j' l' => ∑ i, ∑ j, ∑ l, C (A i' i) * C (B j' j) * C (C_mat l' l) * E i j l,
    fun i' j' l' => ?_⟩
  calc
    ∑ t, (∑ i, C (A i' i) * U t i) * (∑ j, C (B j' j) * V t j) * (∑ l, C (C_mat l' l) * W t l)
      = ∑ i, ∑ j, ∑ l, C (A i' i) * C (B j' j) * C (C_mat l' l) *
          ∑ t, U t i * V t j * W t l := by
            simp_rw [Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            conv_lhs =>
              arg 2; ext i
              rw [Finset.sum_comm]
              arg 2; ext j
              rw [Finset.sum_comm]
            rw [Finset.sum_comm]
            conv_lhs =>
              arg 2; ext j
              rw [Finset.sum_comm]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => ?_
            refine Finset.sum_congr rfl fun j _ => ?_
            refine Finset.sum_congr rfl fun l _ => ?_
            refine Finset.sum_congr rfl fun t _ => ?_
            ring
    _ = ∑ i, ∑ j, ∑ l, C (A i' i) * C (B j' j) * C (C_mat l' l) *
          (C (T i j l) * X ^ d + X ^ (d + 1) * E i j l) := by
            simp_rw [hT]
    _ = C (SemaevRCB.mapTensor A B C_mat T i' j' l') * X ^ d +
          X ^ (d + 1) * ∑ i, ∑ j, ∑ l, C (A i' i) * C (B j' j) * C (C_mat l' l) * E i j l := by
            simp only [SemaevRCB.mapTensor, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
            simp_rw [mul_add, Finset.sum_add_distrib]
            congr 1
            · refine Finset.sum_congr rfl fun i _ => ?_
              refine Finset.sum_congr rfl fun j _ => ?_
              refine Finset.sum_congr rfl fun l _ => ?_
              ring
            · refine Finset.sum_congr rfl fun i _ => ?_
              refine Finset.sum_congr rfl fun j _ => ?_
              refine Finset.sum_congr rfl fun l _ => ?_
              ring

lemma HasSym12FormalBorderRankLe.mapSym12 {K I I' L L' : Type*} [CommSemiring K]
    [Fintype I] [Fintype L]
    {T : Tensor3 K I I L} {r : ℕ} (h : HasSym12FormalBorderRankLe T r)
    (A : Matrix I' I K) (C_mat : Matrix L' L K) :
    HasSym12FormalBorderRankLe (mapTensor A A C_mat T) r := by
  rcases h with ⟨d, U, W, E, hT⟩
  refine ⟨d,
    fun t i' => ∑ i, C (A i' i) * U t i,
    fun t l' => ∑ l, C (C_mat l' l) * W t l,
    fun i' j' l' => ∑ i, ∑ j, ∑ l, C (A i' i) * C (A j' j) * C (C_mat l' l) * E i j l,
    fun i' j' l' => ?_⟩
  calc
    ∑ t, (∑ i, C (A i' i) * U t i) * (∑ j, C (A j' j) * U t j) * (∑ l, C (C_mat l' l) * W t l)
      = ∑ i, ∑ j, ∑ l, C (A i' i) * C (A j' j) * C (C_mat l' l) *
          ∑ t, U t i * U t j * W t l := by
            simp_rw [Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            conv_lhs =>
              arg 2; ext i
              rw [Finset.sum_comm]
              arg 2; ext j
              rw [Finset.sum_comm]
            rw [Finset.sum_comm]
            conv_lhs =>
              arg 2; ext j
              rw [Finset.sum_comm]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => ?_
            refine Finset.sum_congr rfl fun j _ => ?_
            refine Finset.sum_congr rfl fun l _ => ?_
            refine Finset.sum_congr rfl fun t _ => ?_
            ring
    _ = ∑ i, ∑ j, ∑ l, C (A i' i) * C (A j' j) * C (C_mat l' l) *
          (C (T i j l) * X ^ d + X ^ (d + 1) * E i j l) := by
            simp_rw [hT]
    _ = C (mapTensor A A C_mat T i' j' l') * X ^ d +
          X ^ (d + 1) * ∑ i, ∑ j, ∑ l, C (A i' i) * C (A j' j) * C (C_mat l' l) * E i j l := by
            simp only [SemaevRCB.mapTensor, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
            simp_rw [mul_add, Finset.sum_add_distrib]
            congr 1
            · refine Finset.sum_congr rfl fun i _ => ?_
              refine Finset.sum_congr rfl fun j _ => ?_
              refine Finset.sum_congr rfl fun l _ => ?_
              ring
            · refine Finset.sum_congr rfl fun i _ => ?_
              refine Finset.sum_congr rfl fun j _ => ?_
              refine Finset.sum_congr rfl fun l _ => ?_
              ring

lemma HasTensorRankLe.baseChange {K F I J L : Type*} [CommSemiring K] [CommSemiring F]
    (φ : K →+* F) {T : Tensor3 K I J L} {r : ℕ} (h : HasTensorRankLe T r) :
    HasTensorRankLe (baseChangeTensor φ T) r := by
  rcases h with ⟨u, v, w, hT⟩
  refine ⟨fun t i => φ (u t i), fun t j => φ (v t j), fun t l => φ (w t l), fun i j l => ?_⟩
  simp only [baseChangeTensor, hT, map_sum, map_mul]

lemma HasSym12RankLe.baseChange {K F I L : Type*} [CommSemiring K] [CommSemiring F]
    (φ : K →+* F) {T : Tensor3 K I I L} {r : ℕ} (h : HasSym12RankLe T r) :
    HasSym12RankLe (baseChangeTensor φ T) r := by
  rcases h with ⟨u, w, hT⟩
  refine ⟨fun t i => φ (u t i), fun t l => φ (w t l), fun i j l => ?_⟩
  simp only [baseChangeTensor, hT, map_sum, map_mul]

lemma HasFormalBorderRankLe.baseChange {K F I J L : Type*} [CommSemiring K] [CommSemiring F]
    (φ : K →+* F) {T : Tensor3 K I J L} {r : ℕ} (h : HasFormalBorderRankLe T r) :
    HasFormalBorderRankLe (baseChangeTensor φ T) r := by
  rcases h with ⟨d, U, V, W, E, hT⟩
  refine ⟨d, fun t i => (U t i).map φ, fun t j => (V t j).map φ,
    fun t l => (W t l).map φ, fun i j l => (E i j l).map φ, fun i j l => ?_⟩
  have hmap := congrArg (Polynomial.map φ) (hT i j l)
  simpa [baseChangeTensor, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_add,
    Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X] using hmap

lemma HasSym12FormalBorderRankLe.baseChange {K F I L : Type*} [CommSemiring K] [CommSemiring F]
    (φ : K →+* F) {T : Tensor3 K I I L} {r : ℕ} (h : HasSym12FormalBorderRankLe T r) :
    HasSym12FormalBorderRankLe (baseChangeTensor φ T) r := by
  rcases h with ⟨d, U, W, E, hT⟩
  refine ⟨d, fun t i => (U t i).map φ, fun t l => (W t l).map φ,
    fun i j l => (E i j l).map φ, fun i j l => ?_⟩
  have hmap := congrArg (Polynomial.map φ) (hT i j l)
  simpa [baseChangeTensor, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_add,
    Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X] using hmap

/-- Linear flattening of a 3-tensor defined by a coefficient array `c` over `K`, evaluated over
any `K`-algebra `R` via `φ : K →+* R`. -/
def linearFlattening {K R I J L M₁ M₂ : Type*} [CommSemiring K] [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    (φ : K →+* R) (c : M₁ → M₂ → I → J → L → K) (T : Tensor3 R I J L) :
    Matrix M₁ M₂ R :=
  fun p q => ∑ i, ∑ j, ∑ l, φ (c p q i j l) * T i j l

lemma linearFlattening_add {K R I J L M₁ M₂ : Type*} [CommSemiring K] [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    (φ : K →+* R) (c : M₁ → M₂ → I → J → L → K) (T₁ T₂ : Tensor3 R I J L) :
    linearFlattening φ c (fun i j l => T₁ i j l + T₂ i j l) =
      linearFlattening φ c T₁ + linearFlattening φ c T₂ := by
  ext p q
  simp only [linearFlattening, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

lemma linearFlattening_sum {K R I J L M₁ M₂ ι : Type*} [CommSemiring K] [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype L]
    (φ : K →+* R) (c : M₁ → M₂ → I → J → L → K) (s : Finset ι) (T : ι → Tensor3 R I J L) :
    linearFlattening φ c (fun i j l => ∑ t ∈ s, T t i j l) =
      ∑ t ∈ s, linearFlattening φ c (T t) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    ext p q
    simp [linearFlattening]
  | @insert a s ha ih =>
    ext p q
    simp only [Finset.sum_insert ha, Matrix.sum_apply, linearFlattening, mul_add,
      Finset.sum_add_distrib]
    have hih := congrFun (congrFun ih p) q
    simpa [linearFlattening, Matrix.sum_apply] using congrArg (fun x => _ + x) hih

/-- Subadditivity of matrix rank over a field: `rank (A + B) ≤ rank A + rank B`. -/
lemma matrix_rank_add_le {F M₁ M₂ : Type*} [Field F] [Fintype M₁] [Fintype M₂]
    (A B : Matrix M₁ M₂ F) : (A + B).rank ≤ A.rank + B.rank := by
  have hsub : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    have hmul : (A + B).mulVecLin v = A.mulVecLin v + B.mulVecLin v := by
      simp
    rw [hmul]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self _ v) (LinearMap.mem_range_self _ v)
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin)
  have hmono : (A + B).rank ≤
      Module.finrank F ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin) :=
    Submodule.finrank_mono hsub
  change (A + B).rank ≤
    Module.finrank F (LinearMap.range A.mulVecLin) +
      Module.finrank F (LinearMap.range B.mulVecLin)
  omega

/-- Subadditivity of matrix rank for finite sums over a field. -/
lemma matrix_rank_sum_le {F M₁ M₂ ι : Type*} [Field F] [Fintype M₁] [Fintype M₂]
    (s : Finset ι) (A : ι → Matrix M₁ M₂ F) : (∑ t ∈ s, A t).rank ≤ ∑ t ∈ s, (A t).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Matrix.rank_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact le_trans (matrix_rank_add_le (A a) (∑ t ∈ s, A t)) (Nat.add_le_add_left ih _)

/-- Helper: a nonsingular `Q × Q` minor bounds `|Q| ≤ κ * r` for any sum of `r` matrices
of rank `≤ κ` over a field `F`. -/
lemma matrix_card_le_sum_rank {F M₁ M₂ Q : Type*} [Field F]
    [Fintype M₁] [Fintype M₂] [Fintype Q] [DecidableEq Q]
    (M : Matrix M₁ M₂ F) (rowSub : Q → M₁) (colSub : Q → M₂)
    (hdet : (M.submatrix rowSub colSub).det ≠ 0)
    {r : ℕ} (A : Fin r → Matrix M₁ M₂ F) (hsum : M = ∑ t, A t)
    (κ : ℕ) (hκ : ∀ t, (A t).rank ≤ κ) :
    Fintype.card Q ≤ κ * r := by
  have h1 : Fintype.card Q ≤ (M.submatrix rowSub colSub).rank := by
    rw [Matrix.rank_of_det_ne_zero hdet]
  have h2 : (M.submatrix rowSub colSub).rank ≤ M.rank :=
    Matrix.rank_submatrix_le M rowSub colSub
  have h3 : M.rank ≤ ∑ t, (A t).rank := by
    rw [hsum]
    exact matrix_rank_sum_le Finset.univ A
  have h4 : ∑ t, (A t).rank ≤ κ * r := by
    calc ∑ t, (A t).rank ≤ ∑ _t : Fin r, κ := Finset.sum_le_sum fun t _ => hκ t
      _ = κ * r := by simp [mul_comm]
  exact le_trans h1 (le_trans h2 (le_trans h3 h4))

/-- **Remark 2.3(a) (Purely algebraic flattening lower bound for formal border rank):**
If a `K`-linear flattening `Φ` satisfies `rank (Φ_{K(ε)}(u ⊗ v ⊗ w)) ≤ κ` on every pure tensor
over `RatFunc K`, and `Φ_K(T)` has a nonsingular `Q × Q` submatrix over `K`, then every formal
border-rank-`r` degeneration of `T` over `K` satisfies `|Q| ≤ κ * r`. This holds over arbitrary
fields `K` (including finite and imperfect fields) without analytic topology. -/
theorem formalBorderRank_flattening_lower_bound
    {K I J L M₁ M₂ Q : Type*} [Field K]
    [Fintype I] [Fintype J] [Fintype L] [Fintype M₁] [Fintype M₂] [Fintype Q]
    [DecidableEq Q]
    (c : M₁ → M₂ → I → J → L → K)
    (κ : ℕ)
    (hκ : ∀ (u : I → RatFunc K) (v : J → RatFunc K) (w : L → RatFunc K),
      (linearFlattening (algebraMap K (RatFunc K)) c (rankOneTensor u v w)).rank ≤ κ)
    {T : Tensor3 K I J L}
    (rowSub : Q → M₁) (colSub : Q → M₂)
    (hdet : ((linearFlattening (RingHom.id K) c T).submatrix rowSub colSub).det ≠ 0)
    {r : ℕ} (hr : HasFormalBorderRankLe T r) :
    Fintype.card Q ≤ κ * r := by
  rcases hr with ⟨d, U, V, W, E, hT⟩
  let toRF : K[X] →+* RatFunc K := algebraMap K[X] (RatFunc K)
  let M_poly : Matrix M₁ M₂ K[X] :=
    linearFlattening Polynomial.C c (fun i j l => C (T i j l) * X ^ d + X ^ (d + 1) * E i j l)
  let M_base : Matrix M₁ M₂ K[X] :=
    fun p q => C (linearFlattening (RingHom.id K) c T p q) +
      X * linearFlattening Polynomial.C c E p q
  have hM_eq : M_poly = (X : K[X]) ^ d • M_base := by
    funext p q
    change linearFlattening Polynomial.C c
      (fun i j l => C (T i j l) * X ^ d + X ^ (d + 1) * E i j l) p q =
      (X : K[X]) ^ d * (C (linearFlattening (RingHom.id K) c T p q) +
        X * linearFlattening Polynomial.C c E p q)
    simp only [linearFlattening, RingHom.id_apply, map_sum, map_mul, mul_add,
      Finset.mul_sum, Finset.sum_add_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    · refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [pow_succ]
      ring
  have hbase_eval : ((M_base.submatrix rowSub colSub).det).eval (0 : K) =
      ((linearFlattening (RingHom.id K) c T).submatrix rowSub colSub).det := by
    change (Polynomial.evalRingHom (0 : K)) (M_base.submatrix rowSub colSub).det = _
    rw [RingHom.map_det]
    congr 1
    funext p q
    simp [Matrix.submatrix, M_base]
  have hbase_ne : (M_base.submatrix rowSub colSub).det ≠ 0 := by
    intro h0
    apply hdet
    rw [← hbase_eval, h0, Polynomial.eval_zero]
  have hpoly_det_ne : (M_poly.submatrix rowSub colSub).det ≠ 0 := by
    have hsub : M_poly.submatrix rowSub colSub =
        (X : K[X]) ^ d • (M_base.submatrix rowSub colSub) := by
      rw [hM_eq]; rfl
    rw [hsub, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ Polynomial.X_ne_zero)) hbase_ne
  let M_rf : Matrix M₁ M₂ (RatFunc K) := M_poly.map toRF
  have hrf_det_ne : (M_rf.submatrix rowSub colSub).det ≠ 0 := by
    have hmap : (M_rf.submatrix rowSub colSub).det = toRF ((M_poly.submatrix rowSub colSub).det) := by
      rw [RingHom.map_det toRF]
      congr 1
    rw [hmap]
    intro h0
    apply hpoly_det_ne
    exact (RatFunc.algebraMap_injective K) (by simpa [toRF] using h0)
  have hrf_eq_sum : M_rf = ∑ t : Fin r,
      linearFlattening (algebraMap K (RatFunc K)) c
        (rankOneTensor (fun i => toRF (U t i)) (fun j => toRF (V t j))
          (fun l => toRF (W t l))) := by
    have hM_poly_sum : M_poly = ∑ t : Fin r,
        linearFlattening Polynomial.C c (rankOneTensor (U t) (V t) (W t)) := by
      rw [← linearFlattening_sum]
      exact congrArg (linearFlattening Polynomial.C c) (by funext i j l; exact (hT i j l).symm)
    funext p q
    simp only [M_rf, Matrix.map_apply, hM_poly_sum, Matrix.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [linearFlattening, rankOneTensor, map_sum, map_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun l _ => ?_
    have hC : toRF (C (c p q i j l)) = algebraMap K (RatFunc K) (c p q i j l) :=
      (IsScalarTower.algebraMap_apply K K[X] (RatFunc K) (c p q i j l)).symm
    rw [hC]
  exact matrix_card_le_sum_rank M_rf rowSub colSub hrf_det_ne _ hrf_eq_sum κ
    (fun t => hκ _ _ _)

/-! ### Levi-Civita tensor `ε₃`, mode-shared double `I₂ ⊗₁,₂ ε₃`, and projective RCB tensor -/

/-- The `3 × 3 × 3` Levi-Civita cross-product tensor `ε₃` with `(E_k)_{ij} = ε_{ijk}`. -/
def eps3 (K : Type*) [CommRing K] : Tensor3 K (Fin 3) (Fin 3) (Fin 3) :=
  fun i j k =>
    match i.val, j.val, k.val with
    | 0, 1, 2 => 1
    | 1, 2, 0 => 1
    | 2, 0, 1 => 1
    | 0, 2, 1 => -1
    | 2, 1, 0 => -1
    | 1, 0, 2 => -1
    | _, _, _ => 0

/-- Cross product on `K³` (`Fin 3 → K`). -/
def cross3 {K : Type*} [CommRing K] (u v : Fin 3 → K) : Fin 3 → K :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

/-- The mode-shared Levi-Civita double `I₂ ⊗₁,₂ ε₃ ∈ (K² ⊗ K³) ⊗ (K² ⊗ K³) ⊗ K³`. -/
def I2_eps3 (K : Type*) [CommRing K] :
    Tensor3 K (Fin 2 × Fin 3) (Fin 2 × Fin 3) (Fin 3) :=
  fun p q k => if p.1 = q.1 then eps3 K p.2 q.2 k else 0

/-- The `(1,2)`-symmetric skew-doubled tensor `T̃` with slices `[[0, E_k], [-E_k, 0]]`. -/
def symEps3 (K : Type*) [CommRing K] :
    Tensor3 K (Fin 2 × Fin 3) (Fin 2 × Fin 3) (Fin 3) :=
  fun p q k =>
    if p.1 = 0 ∧ q.1 = 1 then eps3 K p.2 q.2 k
    else if p.1 = 1 ∧ q.1 = 0 then -eps3 K p.2 q.2 k
    else 0

/-- Renes–Costello–Batina projective addition formulas `(X_+, Y_+, Z_+)` on
`E_b : Y²Z = X³ + b Z³` (Equation (5.1) of Paper 1). -/
def rcbX {K : Type*} [CommRing K] (b : K) (P₁ P₂ : Fin 3 → K) : K :=
  let t1 := P₁ 1 * P₂ 1
  let t2 := P₁ 2 * P₂ 2
  let t3 := P₁ 0 * P₂ 1 + P₂ 0 * P₁ 1
  let t4 := P₁ 1 * P₂ 2 + P₂ 1 * P₁ 2
  let t5 := P₁ 0 * P₂ 2 + P₂ 0 * P₁ 2
  t3 * (t1 - 3 * b * t2) - 3 * b * t4 * t5

def rcbY {K : Type*} [CommRing K] (b : K) (P₁ P₂ : Fin 3 → K) : K :=
  let t0 := P₁ 0 * P₂ 0
  let t1 := P₁ 1 * P₂ 1
  let t2 := P₁ 2 * P₂ 2
  let t5 := P₁ 0 * P₂ 2 + P₂ 0 * P₁ 2
  (t1 + 3 * b * t2) * (t1 - 3 * b * t2) + 9 * b * t0 * t5

def rcbZ {K : Type*} [CommRing K] (b : K) (P₁ P₂ : Fin 3 → K) : K :=
  let t0 := P₁ 0 * P₂ 0
  let t1 := P₁ 1 * P₂ 1
  let t2 := P₁ 2 * P₂ 2
  let t3 := P₁ 0 * P₂ 1 + P₂ 0 * P₁ 1
  let t4 := P₁ 1 * P₂ 2 + P₂ 1 * P₁ 2
  3 * t0 * t3 + (t1 + 3 * b * t2) * t4

/-- Canonical quadratic Veronese monomial basis `(X², Y², Z², XY, YZ, XZ)` of `Sym²((K³)*)`. -/
def veronese2 {K : Type*} [CommRing K] (P : Fin 3 → K) : Fin 6 → K :=
  ![P 0 * P 0, P 1 * P 1, P 2 * P 2, P 0 * P 1, P 1 * P 2, P 0 * P 2]

/-- Algebraic coefficient tensor `T_RCB ∈ Sym²(K⁶) ⊗ K³` of the projective RCB addition law
in the canonical monomial basis `(X², Y², Z², XY, YZ, XZ)`. -/
def T_RCB (K : Type*) [CommRing K] (b : K) : Tensor3 K (Fin 6) (Fin 6) (Fin 3) :=
  fun i j k =>
    match k.val, i.val, j.val with
    -- Slice 0: X_+
    | 0, 1, 3 => 1
    | 0, 3, 1 => 1
    | 0, 2, 3 => -3 * b
    | 0, 3, 2 => -3 * b
    | 0, 4, 5 => -6 * b
    | 0, 5, 4 => -6 * b
    -- Slice 1: Y_+
    | 1, 1, 1 => 1
    | 1, 2, 2 => -9 * b * b
    | 1, 0, 5 => 9 * b
    | 1, 5, 0 => 9 * b
    -- Slice 2: Z_+
    | 2, 0, 3 => 3
    | 2, 3, 0 => 3
    | 2, 1, 4 => 1
    | 2, 4, 1 => 1
    | 2, 2, 4 => 3 * b
    | 2, 4, 2 => 3 * b
    | _, _, _ => 0

/-- `T_RCB` evaluates verbatim to `(rcbX, rcbY, rcbZ)` on Veronese lifts over any `CommRing`. -/
theorem T_RCB_eval {K : Type*} [CommRing K] (b : K) (P₁ P₂ : Fin 3 → K) :
    (∑ i : Fin 6, ∑ j : Fin 6, veronese2 P₁ i * veronese2 P₂ j * T_RCB K b i j 0 = rcbX b P₁ P₂) ∧
    (∑ i : Fin 6, ∑ j : Fin 6, veronese2 P₁ i * veronese2 P₂ j * T_RCB K b i j 1 = rcbY b P₁ P₂) ∧
    (∑ i : Fin 6, ∑ j : Fin 6, veronese2 P₁ i * veronese2 P₂ j * T_RCB K b i j 2 = rcbZ b P₁ P₂) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Fin.sum_univ_six, veronese2, T_RCB, rcbX, rcbY, rcbZ] <;>
    ring

end SemaevRCB
