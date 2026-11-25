module

public import SemaevRCB.Defs
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic

@[expose] public section

/-!
# Saturated Flattenings, Trace Obstructions, and Equiangular Idempotent Bases

General algebraic obstructions to rank-saturated flattenings over arbitrary fields `K`:

1. **Rank-sum saturation (`linearMap_rank_sum_saturation`):**
   For finite-dimensional vector spaces `V, W` over a field `K`, if `A : Fin r → (V →ₗ[K] W)`
   satisfies `finrank (range (A i)) ≤ κ i` and `finrank (range (∑ i, A i)) = ∑ i, κ i`, then
   every summand achieves full rank `κ i`, the ranges form an internal direct sum equal to
   `range (∑ i, A i)`, and `⋂ i, ker (A i) = ker (∑ i, A i)`.
2. **Square-matrix idempotent saturation (`matrix_sum_one_saturated_idempotents`):**
   If `∑ i, P i = 1` in `Matrix M M K` with `(P i).rank ≤ κ i` and `∑ i, κ i = Fintype.card M`,
   then `P i * P j = δ_{ij} P i`, `(P i).rank = κ i`, and `trace (P i) = (κ i : K)` over every
   field `K` (including positive characteristic).
3. **Trace obstruction to saturated flattenings (`trace_obstruction_saturated_flattening`):**
   If an additive flattening `F : Tensor3 K I J L →+ Matrix M M K` satisfies
   `rank (F (u ⊗ v ⊗ w)) ≤ κ`, `F T` is invertible with inverse `Fi`, `(κ : K) ≠ 0`, and
   `trace (F (u ⊗ v ⊗ w) * Fi) = 0` on all rank-one tensors, then every tensor decomposition of
   `T` over `K` has length at least `Fintype.card M / κ + 1`.
4. **Saturated characteristic determinant (`det_one_add_X_smul_of_idempotent`,
   `det_add_smul_saturated_summand`):**
   For an idempotent `P` of rank `κ`, `det (1 + X • P) = (1 + X) ^ κ` in `K[X]`, and hence
   for any saturated decomposition `∑ j, A j` with inverse `Ai`,
   `det ((∑ j, A j) + X • A i) = det (∑ j, A j) * (1 + X) ^ (κ i)`.
5. **Equiangular rank-one idempotent bases (`equiangular_idempotent_basis_discriminant`,
   `no_equiangular_idempotent_basis_orderedField`):**
   Any `d²`-element linearly independent family of rank-one idempotents `Q i ∈ Mat_d(K)` (`d ≥ 2`)
   with constant off-diagonal trace `Tr(Q i Q j) = c` forces `(d : K) ≠ 0`, `(d + 1 : K) ≠ 0`,
   `c = (d + 1 : K)⁻¹`, `∑ i, Q i = (d : K) • 1`, and the quadratic discriminant condition
   `IsSquare (if Odd d then (-1)^((d - 1) / 2) * d else (-1)^(d / 2) * (d + 1))`. Over any
   strictly ordered field, no such basis exists for any `d ≥ 2`.
-/

namespace SemaevRCB

open Matrix Polynomial BigOperators

/-! ## Section 1: Rectangular Rank-Sum Saturation (Lemma 1) -/

private lemma finrank_biSup_le_sum {K W ι : Type*} [Field K]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (s : Finset ι) (p : ι → Submodule K W) :
    Module.finrank K ↥(⨆ i ∈ s, p i) ≤ ∑ i ∈ s, Module.finrank K ↥(p i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hsup_eq : (⨆ i ∈ insert a s, p i) = p a ⊔ (⨆ i ∈ s, p i) := by
      apply le_antisymm
      · refine iSup₂_le fun i hi => ?_
        rcases Finset.mem_insert.mp hi with rfl | his
        · exact le_sup_left
        · exact le_trans (le_biSup p his) le_sup_right
      · exact sup_le (le_biSup p (Finset.mem_insert_self a s))
          (iSup₂_le fun i his => le_biSup p (Finset.mem_insert_of_mem his))
    rw [hsup_eq]
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq (p a) (⨆ i ∈ s, p i)
    omega

private lemma finrank_iSup_le_sum {K W ι : Type*} [Field K]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Fintype ι]
    (p : ι → Submodule K W) :
    Module.finrank K ↥(⨆ i, p i) ≤ ∑ i, Module.finrank K ↥(p i) := by
  have heq : (⨆ i, p i) = ⨆ i ∈ (Finset.univ : Finset ι), p i := by simp
  rw [heq]
  exact finrank_biSup_le_sum Finset.univ p

private lemma iSup_eq_sup_erase {α ι : Type*} [CompleteLattice α] [Fintype ι] [DecidableEq ι]
    (p : ι → α) (i : ι) :
    (⨆ j, p j) = p i ⊔ ⨆ j ∈ Finset.univ.erase i, p j := by
  apply le_antisymm
  · refine iSup_le fun j => ?_
    by_cases hji : j = i
    · subst hji; exact le_sup_left
    · exact le_trans (le_biSup p (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)) le_sup_right
  · refine sup_le (le_iSup p i) ?_
    exact iSup₂_le fun j _ => le_iSup p j

private lemma biSup_erase_eq_iSup_ne {α ι : Type*} [CompleteLattice α] [Fintype ι] [DecidableEq ι]
    (p : ι → α) (i : ι) :
    (⨆ j ∈ Finset.univ.erase i, p j) = ⨆ (j : ι) (_ : j ≠ i), p j := by
  apply le_antisymm
  · refine iSup₂_le fun j hj => ?_
    exact le_iSup₂ (f := fun j (_ : j ≠ i) => p j) j (Finset.mem_erase.mp hj).1
  · refine iSup₂_le fun j hji => ?_
    exact le_biSup p (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)

/-- **Rectangular rank-sum saturation:** If linear maps `A : Fin r → (V →ₗ[K] W)` between
finite-dimensional `K`-vector spaces satisfy `rank (A i) ≤ κ i` for all `i` and
`rank (∑ i, A i) = ∑ i, κ i`, then every summand has exact rank `κ i`, the ranges `range (A i)`
form an internal direct sum equal to `range (∑ i, A i)`, and `⋂ i, ker (A i) = ker (∑ i, A i)`. -/
theorem linearMap_rank_sum_saturation {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {r : ℕ} (A : Fin r → (V →ₗ[K] W)) (κ : Fin r → ℕ)
    (hκ : ∀ i, Module.finrank K (LinearMap.range (A i)) ≤ κ i)
    (hsat : Module.finrank K (LinearMap.range (∑ i, A i)) = ∑ i, κ i) :
    (∀ i, Module.finrank K (LinearMap.range (A i)) = κ i) ∧
    iSupIndep (fun i => LinearMap.range (A i)) ∧
    (⨆ i, LinearMap.range (A i)) = LinearMap.range (∑ i, A i) ∧
    (⨅ i, LinearMap.ker (A i)) = LinearMap.ker (∑ i, A i) := by
  let R : Fin r → Submodule K W := fun i => LinearMap.range (A i)
  have hrange_le : LinearMap.range (∑ i, A i) ≤ ⨆ i, R i := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact le_iSup R i (LinearMap.mem_range_self (A i) v)
  have hle1 : ∑ i, κ i ≤ Module.finrank K ↥(⨆ i, R i) := by
    rw [← hsat]
    exact Submodule.finrank_mono hrange_le
  have hle2 : Module.finrank K ↥(⨆ i, R i) ≤ ∑ i, Module.finrank K ↥(R i) :=
    finrank_iSup_le_sum R
  have hle3 : ∑ i, Module.finrank K ↥(R i) ≤ ∑ i, κ i :=
    Finset.sum_le_sum fun i _ => hκ i
  have hsum_eq : ∑ i, Module.finrank K ↥(R i) = ∑ i, κ i := le_antisymm hle3 (le_trans hle1 hle2)
  have hfin_eq : ∀ i, Module.finrank K ↥(R i) = κ i := by
    intro i
    by_contra hne
    have hlt : Module.finrank K ↥(R i) < κ i := lt_of_le_of_ne (hκ i) hne
    have hstrict : ∑ j, Module.finrank K ↥(R j) < ∑ j, κ j :=
      Finset.sum_lt_sum (fun j _ => hκ j) ⟨i, Finset.mem_univ i, hlt⟩
    omega
  have hsup_dim : Module.finrank K ↥(⨆ i, R i) = Module.finrank K (LinearMap.range (∑ i, A i)) := by
    rw [hsat]
    exact le_antisymm (le_trans hle2 hle3) hle1
  have hsup_eq : (⨆ i, R i) = LinearMap.range (∑ i, A i) :=
    (Submodule.eq_of_le_of_finrank_eq hrange_le hsup_dim.symm).symm
  have hindep : iSupIndep R := by
    intro i
    rw [← biSup_erase_eq_iSup_ne R i, disjoint_iff]
    have hsplit := iSup_eq_sup_erase R i
    have hmod := Submodule.finrank_sup_add_finrank_inf_eq (R i) (⨆ j ∈ Finset.univ.erase i, R j)
    rw [← hsplit] at hmod
    have herase_le := finrank_biSup_le_sum (Finset.univ.erase i) R
    have hadd_erase : Module.finrank K ↥(R i) + ∑ j ∈ Finset.univ.erase i, Module.finrank K ↥(R j) =
        ∑ j, Module.finrank K ↥(R j) :=
      Finset.add_sum_erase Finset.univ (fun j => Module.finrank K ↥(R j)) (Finset.mem_univ i)
    have hinf_zero : Module.finrank K ↥(R i ⊓ ⨆ j ∈ Finset.univ.erase i, R j) = 0 := by
      omega
    exact (Submodule.finrank_eq_zero).mp hinf_zero
  have hker_eq : (⨅ i, LinearMap.ker (A i)) = LinearMap.ker (∑ i, A i) := by
    apply le_antisymm
    · intro x hx
      rw [LinearMap.mem_ker, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      exact LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hx i)
    · intro x hx
      rw [Submodule.mem_iInf]
      intro i
      rw [LinearMap.mem_ker] at hx ⊢
      rw [LinearMap.sum_apply] at hx
      have hdecomp : A i x = -(∑ j ∈ Finset.univ.erase i, A j x) := by
        have hadd := Finset.add_sum_erase Finset.univ (fun j => A j x) (Finset.mem_univ i)
        rw [hx] at hadd
        exact eq_neg_of_add_eq_zero_left hadd
      have hmem_i : A i x ∈ R i := LinearMap.mem_range_self (A i) x
      have hmem_rest : A i x ∈ ⨆ (j : Fin r) (_ : j ≠ i), R j := by
        rw [hdecomp, ← biSup_erase_eq_iSup_ne R i]
        refine Submodule.neg_mem _ (Submodule.sum_mem _ fun j hj => ?_)
        exact le_biSup R hj (LinearMap.mem_range_self (A j) x)
      have hbot : A i x ∈ (⊥ : Submodule K W) := by
        rw [← (disjoint_iff.mp (hindep i))]
        exact ⟨hmem_i, hmem_rest⟩
      exact (Submodule.mem_bot K).mp hbot
  exact ⟨hfin_eq, hindep, hsup_eq, hker_eq⟩

/-! ## Section 2: Idempotent Normal Form, Trace, and Square Saturation -/

/-- Over any field `K`, any idempotent matrix `P * P = P` is similar via an invertible matrix
`S` (`Si * S = 1`, `S * Si = 1`) to a block matrix `fromBlocks 1 0 0 0` whose identity block has
size `P.rank`. -/
lemma idempotent_exists_conj_fromBlocks {K M : Type*} [Field K] [Fintype M] [DecidableEq M]
    (P : Matrix M M K) (hP : P * P = P) :
    ∃ (l : ℕ) (e : Fin P.rank ⊕ Fin l ≃ M) (S Si : Matrix M M K),
      Si * S = 1 ∧ S * Si = 1 ∧
      Si * P * S = Matrix.reindex e e
        (Matrix.fromBlocks (1 : Matrix (Fin P.rank) (Fin P.rank) K) 0 0
          (0 : Matrix (Fin l) (Fin l) K)) := by
  classical
  let R : Submodule K (M → K) := LinearMap.range P.mulVecLin
  let N : Submodule K (M → K) := LinearMap.ker P.mulVecLin
  have hP_on_R : ∀ y : M → K, y ∈ R → P.mulVecLin y = y := by
    rintro _ ⟨z, rfl⟩
    change P *ᵥ (P *ᵥ z) = P *ᵥ z
    rw [Matrix.mulVec_mulVec, hP]
  have hcompl : IsCompl R N := by
    refine ⟨?_, ?_⟩
    · rw [disjoint_iff]
      apply le_antisymm
      · intro y ⟨hyR, hyN⟩
        rw [Submodule.mem_bot]
        have h1 : P.mulVecLin y = y := hP_on_R y hyR
        have h2 : P.mulVecLin y = 0 := LinearMap.mem_ker.mp hyN
        rw [← h1, h2]
      · exact bot_le
    · rw [codisjoint_iff]
      apply le_antisymm le_top
      intro x _
      have hx_split : x = P.mulVecLin x + (x - P.mulVecLin x) := by abel
      rw [hx_split]
      refine Submodule.add_mem_sup (LinearMap.mem_range_self P.mulVecLin x) ?_
      rw [LinearMap.mem_ker, map_sub]
      have hPP : P.mulVecLin (P.mulVecLin x) = P.mulVecLin x :=
        hP_on_R _ (LinearMap.mem_range_self P.mulVecLin x)
      rw [hPP, sub_self]
  let addMap : (R × N) →ₗ[K] (M → K) := R.subtype.coprod N.subtype
  have hadd_inj : Function.Injective addMap := by
    intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
    have hsub : (a₁.1 - a₂.1) = -(b₁.1 - b₂.1) := by
      have h' : a₁.1 + b₁.1 = a₂.1 + b₂.1 := h
      exact eq_neg_of_add_eq_zero_left (by abel_nf; rw [← sub_eq_zero]; linear_combination h')
    have hmem_R : a₁.1 - a₂.1 ∈ R := R.sub_mem a₁.2 a₂.2
    have hmem_N : a₁.1 - a₂.1 ∈ N := by
      rw [hsub]
      exact N.neg_mem (N.sub_mem b₁.2 b₂.2)
    have ha0 : a₁.1 - a₂.1 = 0 := by
      have hbot : a₁.1 - a₂.1 ∈ (⊥ : Submodule K (M → K)) := by
        rw [← (disjoint_iff.mp hcompl.1)]
        exact ⟨hmem_R, hmem_N⟩
      exact (Submodule.mem_bot K).mp hbot
    have hb0 : b₁.1 - b₂.1 = 0 := by
      rw [ha0] at hsub
      exact neg_eq_zero.mp hsub.symm
    exact Prod.ext (Subtype.ext (sub_eq_zero.mp ha0)) (Subtype.ext (sub_eq_zero.mp hb0))
  have hadd_surj : Function.Surjective addMap := by
    intro x
    have hx : x ∈ R ⊔ N := by rw [codisjoint_iff.mp hcompl.2]; exact Submodule.mem_top
    rcases Submodule.mem_sup.mp hx with ⟨a, ha, b, hb, hab⟩
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩
  let eRN : (R × N) ≃ₗ[K] (M → K) := LinearEquiv.ofBijective addMap ⟨hadd_inj, hadd_surj⟩
  let k : ℕ := P.rank
  let l : ℕ := Module.finrank K N
  have hk_eq : Module.finrank K R = k := rfl
  let bR : Module.Basis (Fin k) K R := (Module.finBasis K R).reindex (finCongr hk_eq)
  let bN : Module.Basis (Fin l) K N := Module.finBasis K N
  let b : Module.Basis (Fin k ⊕ Fin l) K (M → K) := (bR.prod bN).map eRN
  let b0 : Module.Basis M K (M → K) := Pi.basisFun K M
  have hcard : Fintype.card (Fin k ⊕ Fin l) = Fintype.card M := by
    have h1 := Module.finrank_eq_card_basis b
    have h2 := Module.finrank_eq_card_basis b0
    omega
  let e : Fin k ⊕ Fin l ≃ M := Fintype.equivOfCardEq hcard
  let bM : Module.Basis M K (M → K) := b.reindex e
  let S : Matrix M M K := b0.toMatrix bM
  let Si : Matrix M M K := bM.toMatrix b0
  have hSiS : Si * S = 1 := bM.toMatrix_mul_toMatrix_flip b0
  have hSSi : S * Si = 1 := b0.toMatrix_mul_toMatrix_flip bM
  have hb_inl : ∀ j : Fin k, P.mulVecLin (b (.inl j)) = b (.inl j) := by
    intro j
    apply hP_on_R
    have heq : b (.inl j) = (bR j : M → K) := by
      simp only [b, eRN, addMap, Module.Basis.map_apply, Module.Basis.prod_apply]
      exact add_zero (bR j : M → K)
    rw [heq]
    exact (bR j).2
  have hb_inr : ∀ j : Fin l, P.mulVecLin (b (.inr j)) = 0 := by
    intro j
    have hmem : b (.inr j) ∈ N := by
      have heq : b (.inr j) = (bN j : M → K) := by
        simp only [b, eRN, addMap, Module.Basis.map_apply, Module.Basis.prod_apply]
        exact zero_add (bN j : M → K)
      rw [heq]
      exact (bN j).2
    exact LinearMap.mem_ker.mp hmem
  have hP_toMatrix_b : LinearMap.toMatrix b b P.mulVecLin =
      Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) K) 0 0 (0 : Matrix (Fin l) (Fin l) K) := by
    ext x y
    rw [LinearMap.toMatrix_apply]
    rcases y with j | j
    · rw [hb_inl j, b.repr_self, Finsupp.single_apply]
      rcases x with i | i
      · simp [Matrix.fromBlocks, Matrix.one_apply, eq_comm]
      · simp [Matrix.fromBlocks]
    · rw [hb_inr j, map_zero, Finsupp.zero_apply]
      rcases x with i | i <;> simp [Matrix.fromBlocks]
  have hSiPS : Si * P * S = Matrix.reindex e e
      (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) K) 0 0 (0 : Matrix (Fin l) (Fin l) K)) := by
    have hmul_bM : Si * P * S = LinearMap.toMatrix bM bM P.mulVecLin := by
      have hP_b0 : P = LinearMap.toMatrix b0 b0 P.mulVecLin := by
        ext i j
        simp [b0, Matrix.mulVec_single]
      have hSi_id : Si = LinearMap.toMatrix b0 bM LinearMap.id :=
        (LinearMap.toMatrix_id_eq_basis_toMatrix b0 bM).symm
      have hS_id : S = LinearMap.toMatrix bM b0 LinearMap.id :=
        (LinearMap.toMatrix_id_eq_basis_toMatrix bM b0).symm
      conv_lhs => rw [hSi_id, hP_b0, hS_id]
      rw [← LinearMap.toMatrix_comp b0 b0 bM, ← LinearMap.toMatrix_comp bM b0 bM]
      simp
    rw [hmul_bM, ← hP_toMatrix_b]
    ext i j
    simp [bM, LinearMap.toMatrix_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact ⟨l, e, S, Si, hSiS, hSSi, hSiPS⟩

/-- Over any field `K` (of arbitrary characteristic), the trace of an idempotent matrix equals
its rank cast to `K`. -/
theorem matrix_trace_eq_rank_of_idempotent {K M : Type*} [Field K] [Fintype M] [DecidableEq M]
    (P : Matrix M M K) (hP : P * P = P) :
    Matrix.trace P = (P.rank : K) := by
  rcases idempotent_exists_conj_fromBlocks P hP with ⟨l, e, S, Si, _, hSSi, hconj⟩
  calc Matrix.trace P = Matrix.trace (P * (S * Si)) := by rw [hSSi, Matrix.mul_one]
    _ = Matrix.trace (Si * P * S) := by
          rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    _ = Matrix.trace (Matrix.reindex e e
          (Matrix.fromBlocks (1 : Matrix (Fin P.rank) (Fin P.rank) K) 0 0
            (0 : Matrix (Fin l) (Fin l) K))) := by rw [hconj]
    _ = Matrix.trace (Matrix.fromBlocks (1 : Matrix (Fin P.rank) (Fin P.rank) K) 0 0
          (0 : Matrix (Fin l) (Fin l) K)) := by
          simp only [Matrix.trace, Matrix.diag, Matrix.reindex_apply, Matrix.submatrix_apply]
          exact e.symm.sum_comp (fun x => Matrix.fromBlocks (1 : Matrix (Fin P.rank) (Fin P.rank) K)
            0 0 (0 : Matrix (Fin l) (Fin l) K) x x)
    _ = (P.rank : K) := by
          simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type, Matrix.fromBlocks]

/-- **Square-matrix idempotent saturation (Lemma 1):** If `∑ i, P i = 1` in `Matrix M M K` with
`(P i).rank ≤ κ i` and `∑ i, κ i = Fintype.card M`, then each `P i` has exact rank `κ i`,
the `P i` are pairwise annihilating idempotents (`P i * P j = δ_{ij} P i`), and
`trace (P i) = (κ i : K)` over every field `K`. -/
theorem matrix_sum_one_saturated_idempotents {K M : Type*} [Field K] [Fintype M] [DecidableEq M]
    {r : ℕ} (P : Fin r → Matrix M M K) (κ : Fin r → ℕ)
    (hsum : ∑ i, P i = 1)
    (hκ : ∀ i, (P i).rank ≤ κ i)
    (hcard : ∑ i, κ i = Fintype.card M) :
    (∀ i, (P i).rank = κ i) ∧
    (∀ i j, P i * P j = if i = j then P i else 0) ∧
    (∀ i, Matrix.trace (P i) = (κ i : K)) := by
  let A : Fin r → ((M → K) →ₗ[K] (M → K)) := fun i => (P i).mulVecLin
  have hA_sum : ∑ i, A i = LinearMap.id := by
    apply LinearMap.ext
    intro x
    rw [LinearMap.sum_apply]
    change ∑ i, (P i) *ᵥ x = x
    rw [← Matrix.sum_mulVec, hsum, Matrix.one_mulVec]
  have hsat : Module.finrank K (LinearMap.range (∑ i, A i)) = ∑ i, κ i := by
    rw [hA_sum, LinearMap.range_id, finrank_top, Module.finrank_pi, hcard]
  rcases linearMap_rank_sum_saturation A κ hκ hsat with ⟨hrank, hindep, _, _⟩
  have horth : ∀ i j, P i * P j = if i = j then P i else 0 := by
    intro i j
    have hmulVec : ∀ x : M → K, (P i * P j) *ᵥ x = (if i = j then P i else 0) *ᵥ x := by
      intro x
      let y : M → K := (P j) *ᵥ x
      let v : Fin r → (M → K) := fun t => if t = j then (P j) *ᵥ y - y else (P t) *ᵥ y
      have hv_mem : ∀ t, v t ∈ LinearMap.range (A t) := by
        intro t
        by_cases htj : t = j
        · subst htj
          simp only [v, ↓reduceIte]
          exact Submodule.sub_mem _ (LinearMap.mem_range_self (A t) y)
            (LinearMap.mem_range_self (A t) x)
        · simp only [v, htj, ↓reduceIte]
          exact LinearMap.mem_range_self (A t) y
      have hv_sum : ∑ t, v t = 0 := by
        have hsplit : ∑ t, v t = (∑ t, (P t) *ᵥ y) - y := by
          have h1 : ∀ t, v t = (P t) *ᵥ y - (if t = j then y else 0) := by
            intro t; by_cases htj : t = j <;> simp [v, htj]
          simp only [h1, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        rw [hsplit, ← Matrix.sum_mulVec, hsum, Matrix.one_mulVec, sub_self]
      have hv_zero : ∀ t, v t = 0 := by
        intro t
        have hdecomp : v t = -(∑ s ∈ Finset.univ.erase t, v s) := by
          have hadd := Finset.add_sum_erase Finset.univ v (Finset.mem_univ t)
          rw [hv_sum] at hadd
          exact eq_neg_of_add_eq_zero_left hadd
        have hmem_rest : v t ∈ ⨆ (s : Fin r) (_ : s ≠ t), LinearMap.range (A s) := by
          rw [hdecomp, ← biSup_erase_eq_iSup_ne (fun s => LinearMap.range (A s)) t]
          refine Submodule.neg_mem _ (Submodule.sum_mem _ fun s hs => ?_)
          exact le_biSup (fun s => LinearMap.range (A s)) hs (hv_mem s)
        have hbot : v t ∈ (⊥ : Submodule K (M → K)) := by
          rw [← (disjoint_iff.mp (hindep t))]
          exact ⟨hv_mem t, hmem_rest⟩
        exact (Submodule.mem_bot K).mp hbot
      have hvi := hv_zero i
      by_cases hij : i = j
      · subst hij
        simp only [v, ↓reduceIte] at hvi
        simp only [↓reduceIte, ← Matrix.mulVec_mulVec]
        exact sub_eq_zero.mp hvi
      · simp only [v, hij, ↓reduceIte] at hvi
        simp only [hij, ↓reduceIte, Matrix.zero_mulVec, ← Matrix.mulVec_mulVec]
        exact hvi
    ext m n
    have hsingle := congrFun (hmulVec (Pi.single n 1)) m
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hsingle
  have htrace : ∀ i, Matrix.trace (P i) = (κ i : K) := by
    intro i
    have hidem : P i * P i = P i := by simpa using horth i i
    have hri : (P i).rank = κ i := hrank i
    rw [matrix_trace_eq_rank_of_idempotent (P i) hidem, hri]
  exact ⟨hrank, horth, htrace⟩

/-! ## Section 3: Trace Obstruction to Saturated Flattenings (Theorem 2) -/

private lemma matrix_rank_mul_right_le' {K m n n' : Type*} [Field K]
    [Fintype m] [Fintype n] [Fintype n'] (A : Matrix m n K) (B : Matrix n n' K) :
    (A * B).rank ≤ A.rank := by
  have hsub : LinearMap.range (A * B).mulVecLin ≤ LinearMap.range A.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    exact ⟨B.mulVecLin v, by simp [Matrix.mulVec_mulVec]⟩
  exact Submodule.finrank_mono hsub

/-- **Theorem 2 (Trace obstruction to saturated flattenings):** Let `F : Tensor3 K I J L →+ Matrix M M K`
be an additive flattening of `T` into `|M| × |M|` matrices (`Nonempty M`) such that:
1. `(F (rankOneTensor u v w)).rank ≤ κ` (`0 < κ`),
2. `F T` is invertible with inverse `Fi`,
3. `(κ : K) ≠ 0`,
4. `trace (F (rankOneTensor u v w) * Fi) = 0` for all pure tensors `u ⊗ v ⊗ w`.

Then every tensor decomposition of `T` over `K` has rank at least `Fintype.card M / κ + 1`, and in
particular `¬ HasTensorRankLe T (Fintype.card M / κ)`. -/
theorem trace_obstruction_saturated_flattening
    {K I J L M : Type*} [Field K] [Fintype M] [DecidableEq M] [Nonempty M]
    (T : Tensor3 K I J L) (F : Tensor3 K I J L →+ Matrix M M K) (Fi : Matrix M M K)
    (κ : ℕ) (hκ_pos : 0 < κ)
    (hκ_rank : ∀ (u : I → K) (v : J → K) (w : L → K), (F (rankOneTensor u v w)).rank ≤ κ)
    (hinv : F T * Fi = 1 ∧ Fi * F T = 1)
    (hκ_ne : (κ : K) ≠ 0)
    (htrace : ∀ (u : I → K) (v : J → K) (w : L → K),
      Matrix.trace (F (rankOneTensor u v w) * Fi) = 0) :
    (∀ r : ℕ, HasTensorRankLe T r → Fintype.card M / κ + 1 ≤ r) ∧
    ¬ HasTensorRankLe T (Fintype.card M / κ) := by
  have hge : ∀ r : ℕ, HasTensorRankLe T r → Fintype.card M / κ + 1 ≤ r := by
    intro r hr
    rcases hr with ⟨u, v, w, hT⟩
    have hT_eq : T = ∑ t : Fin r, rankOneTensor (u t) (v t) (w t) := by
      funext i j l
      simp [Finset.sum_apply, rankOneTensor, hT i j l]
    let P : Fin r → Matrix M M K := fun t => F (rankOneTensor (u t) (v t) (w t)) * Fi
    have hP_sum : ∑ t : Fin r, P t = 1 := by
      dsimp [P]
      rw [← Finset.sum_mul, ← map_sum, ← hT_eq, hinv.1]
    have hP_rank : ∀ t : Fin r, (P t).rank ≤ κ := fun t =>
      le_trans (matrix_rank_mul_right_le' _ Fi) (hκ_rank (u t) (v t) (w t))
    have hN_le : Fintype.card M ≤ r * κ := by
      have h1 : Fintype.card M = (1 : Matrix M M K).rank := by
        rw [Matrix.rank_of_det_ne_zero (by simp)]
      calc Fintype.card M = (∑ t : Fin r, P t).rank := by rw [hP_sum, h1]
        _ ≤ ∑ t : Fin r, (P t).rank := matrix_rank_sum_le Finset.univ P
        _ ≤ ∑ _t : Fin r, κ := Finset.sum_le_sum fun t _ => hP_rank t
        _ = r * κ := by simp
    have hdiv_mod := Nat.div_add_mod (Fintype.card M) κ
    by_cases hrem : Fintype.card M % κ = 0
    · have hN_eq : κ * (Fintype.card M / κ) = Fintype.card M := by omega
      have hdiv_le : Fintype.card M / κ ≤ r := by
        have hmul : κ * (Fintype.card M / κ) ≤ κ * r := by
          rw [hN_eq, mul_comm]; exact hN_le
        exact Nat.le_of_mul_le_mul_left hmul hκ_pos
      by_cases hlt : Fintype.card M / κ < r
      · omega
      · have hr_eq : r = Fintype.card M / κ := by omega
        have hN_pos : 0 < Fintype.card M := Fintype.card_pos
        have hr_pos : 0 < r := by
          by_contra h0
          have hr0 : r = 0 := by omega
          rw [hr0] at hr_eq
          rw [← hr_eq, mul_zero] at hN_eq
          omega
        have hcard_sum : ∑ _t : Fin r, κ = Fintype.card M := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
          rw [hr_eq, mul_comm, hN_eq]
        have htr := (matrix_sum_one_saturated_idempotents P (fun _ => κ) hP_sum hP_rank
          hcard_sum).2.2 ⟨0, hr_pos⟩
        have htr0 : Matrix.trace (P ⟨0, hr_pos⟩) = 0 :=
          htrace (u ⟨0, hr_pos⟩) (v ⟨0, hr_pos⟩) (w ⟨0, hr_pos⟩)
        rw [htr0] at htr
        exact absurd htr.symm hκ_ne
    · have hlt : κ * (Fintype.card M / κ) < κ * r := by
        have : κ * (Fintype.card M / κ) < Fintype.card M := by omega
        calc κ * (Fintype.card M / κ) < Fintype.card M := this
          _ ≤ κ * r := by rw [mul_comm]; exact hN_le
      have : Fintype.card M / κ < r := Nat.lt_of_mul_lt_mul_left hlt
      omega
  exact ⟨hge, fun h => absurd (hge _ h) (by omega)⟩

/-! ## Section 4: Saturated Characteristic Determinant (Proposition 4) -/

private lemma matrix_map_C_mul {K M : Type*} [CommRing K] [Fintype M]
    (A B : Matrix M M K) :
    (A * B).map Polynomial.C = A.map Polynomial.C * B.map Polynomial.C := by
  ext i j
  simp [Matrix.mul_apply, map_sum, map_mul]

private lemma matrix_map_C_one {K M : Type*} [CommRing K] [DecidableEq M] :
    (1 : Matrix M M K).map Polynomial.C = 1 := by
  funext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

/-- For any idempotent matrix `P : Matrix M M K` over a field `K`,
`det (1 + X • P) = (1 + X) ^ P.rank` in `K[X]`. -/
theorem det_one_add_X_smul_of_idempotent {K M : Type*} [Field K] [Fintype M] [DecidableEq M]
    (P : Matrix M M K) (hP : P * P = P) :
    ((1 : Matrix M M K[X]) + (Polynomial.X : K[X]) • P.map Polynomial.C).det =
      (1 + Polynomial.X) ^ P.rank := by
  rcases idempotent_exists_conj_fromBlocks P hP with ⟨l, e, S, Si, hSiS, _, hconj⟩
  let Sc : Matrix M M K[X] := S.map Polynomial.C
  let Sic : Matrix M M K[X] := Si.map Polynomial.C
  have hSicSc : Sic * Sc = 1 := by
    change Si.map Polynomial.C * S.map Polynomial.C = 1
    rw [← matrix_map_C_mul, hSiS, matrix_map_C_one]
  have hdet_inv : Sic.det * Sc.det = 1 := by
    rw [← Matrix.det_mul, hSicSc, Matrix.det_one]
  have hconj_poly : Sic * ((1 : Matrix M M K[X]) + (Polynomial.X : K[X]) • P.map Polynomial.C) * Sc =
      Matrix.reindex e e
        (Matrix.fromBlocks
          ((1 + (Polynomial.X : K[X])) • (1 : Matrix (Fin P.rank) (Fin P.rank) K[X])) 0 0
          (1 : Matrix (Fin l) (Fin l) K[X])) := by
    have h1 : Sic * ((1 : Matrix M M K[X]) + (Polynomial.X : K[X]) • P.map Polynomial.C) * Sc =
        1 + (Polynomial.X : K[X]) • (Si * P * S).map Polynomial.C := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hSicSc, Matrix.mul_smul,
        Matrix.smul_mul]
      congr 2
      change Si.map Polynomial.C * P.map Polynomial.C * S.map Polynomial.C =
        (Si * P * S).map Polynomial.C
      rw [← matrix_map_C_mul, ← matrix_map_C_mul]
    rw [h1, hconj]
    ext i j
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.map_apply,
      Matrix.reindex_apply, Matrix.submatrix_apply, smul_eq_mul]
    cases h_i : e.symm i with
    | inl a =>
      cases h_j : e.symm j with
      | inl b =>
        have hij : (i = j) ↔ (a = b) := by
          constructor
          · intro h; subst h; rw [h_i] at h_j; exact Sum.inl.inj h_j
          · intro h; subst h; exact e.symm.injective (h_i.trans h_j.symm)
        by_cases hab : a = b
        · subst hab
          have hij' : i = j := hij.mpr rfl
          simp [hij', Matrix.fromBlocks]
        · have hij' : i ≠ j := fun h => hab (hij.mp h)
          simp [hij', hab, Matrix.fromBlocks]
      | inr b =>
        have hij' : i ≠ j := by
          intro h; subst h; rw [h_i] at h_j; simp at h_j
        simp [hij', Matrix.fromBlocks]
    | inr a =>
      cases h_j : e.symm j with
      | inl b =>
        have hij' : i ≠ j := by
          intro h; subst h; rw [h_i] at h_j; simp at h_j
        simp [hij', Matrix.fromBlocks]
      | inr b =>
        have hij : (i = j) ↔ (a = b) := by
          constructor
          · intro h; subst h; rw [h_i] at h_j; exact Sum.inr.inj h_j
          · intro h; subst h; exact e.symm.injective (h_i.trans h_j.symm)
        by_cases hab : a = b
        · subst hab
          have hij' : i = j := hij.mpr rfl
          simp [hij', Matrix.fromBlocks]
        · have hij' : i ≠ j := fun h => hab (hij.mp h)
          simp [hij', hab, Matrix.fromBlocks]
  have hdet_eq : (Sic * ((1 : Matrix M M K[X]) + (Polynomial.X : K[X]) • P.map Polynomial.C) * Sc).det =
      ((1 : Matrix M M K[X]) + (Polynomial.X : K[X]) • P.map Polynomial.C).det := by
    rw [Matrix.det_mul, Matrix.det_mul]
    calc Sic.det * ((1 : Matrix M M K[X]) + (Polynomial.X : K[X]) • P.map Polynomial.C).det * Sc.det
        = (Sic.det * Sc.det) *
            ((1 : Matrix M M K[X]) + (Polynomial.X : K[X]) • P.map Polynomial.C).det := by ring
      _ = ((1 : Matrix M M K[X]) + (Polynomial.X : K[X]) • P.map Polynomial.C).det := by
            rw [hdet_inv, one_mul]
  rw [← hdet_eq, hconj_poly, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_smul, Matrix.det_one, Matrix.det_one, Fintype.card_fin, mul_one, mul_one]

/-- **Proposition 4 (Saturated summand characteristic determinant):**
If `A : Fin r → Matrix M M K` has invertible sum `M_sum = ∑ j, A j` (inverse `Ai`),
`(A j).rank ≤ κ j`, and `∑ j, κ j = Fintype.card M`, then for every `i : Fin r`:
1. `(1 + X • (A i * Ai).map C).det = (1 + X) ^ (κ i)` in `K[X]`, and
2. `((∑ j, A j).map C + X • (A i).map C).det = C (∑ j, A j).det * (1 + X) ^ (κ i)`. -/
theorem det_add_smul_saturated_summand {K M : Type*} [Field K] [Fintype M] [DecidableEq M]
    {r : ℕ} (A : Fin r → Matrix M M K) (Ai : Matrix M M K) (κ : Fin r → ℕ)
    (hinv : (∑ j, A j) * Ai = 1 ∧ Ai * (∑ j, A j) = 1)
    (hκ : ∀ j, (A j).rank ≤ κ j)
    (hcard : ∑ j, κ j = Fintype.card M) (i : Fin r) :
    ((1 : Matrix M M K[X]) + (Polynomial.X : K[X]) • (A i * Ai).map Polynomial.C).det =
      (1 + Polynomial.X) ^ (κ i) ∧
    ((∑ j, A j).map Polynomial.C + (Polynomial.X : K[X]) • (A i).map Polynomial.C).det =
      Polynomial.C (∑ j, A j).det * (1 + Polynomial.X) ^ (κ i) := by
  let P : Fin r → Matrix M M K := fun j => A j * Ai
  have hP_sum : ∑ j, P j = 1 := by
    dsimp [P]
    rw [← Finset.sum_mul, hinv.1]
  have hP_rank : ∀ j, (P j).rank ≤ κ j := fun j =>
    le_trans (matrix_rank_mul_right_le' (A j) Ai) (hκ j)
  rcases matrix_sum_one_saturated_idempotents P κ hP_sum hP_rank hcard with
    ⟨hPrk, hPorth, _⟩
  have hPi_idem : P i * P i = P i := by simpa using hPorth i i
  have hdet1 : ((1 : Matrix M M K[X]) + (Polynomial.X : K[X]) • (P i).map Polynomial.C).det =
      (1 + Polynomial.X) ^ (κ i) := by
    rw [det_one_add_X_smul_of_idempotent (P i) hPi_idem, hPrk i]
  have hAi_mul : A i = P i * (∑ j, A j) := by
    dsimp [P]
    rw [Matrix.mul_assoc, hinv.2, Matrix.mul_one]
  have hfac : (∑ j, A j).map Polynomial.C + (Polynomial.X : K[X]) • (A i).map Polynomial.C =
      ((1 : Matrix M M K[X]) + (Polynomial.X : K[X]) • (P i).map Polynomial.C) *
        (∑ j, A j).map Polynomial.C := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
    congr 2
    rw [hAi_mul, matrix_map_C_mul]
  have hdet2 :
      ((∑ j, A j).map Polynomial.C + (Polynomial.X : K[X]) • (A i).map Polynomial.C).det =
        Polynomial.C (∑ j, A j).det * (1 + Polynomial.X) ^ (κ i) := by
    have hmap_det : ((∑ j, A j).map Polynomial.C).det = Polynomial.C (∑ j, A j).det := by
      rw [← RingHom.mapMatrix_apply]
      exact (RingHom.map_det Polynomial.C (∑ j, A j)).symm
    rw [hfac, Matrix.det_mul, hdet1, hmap_det]
    ring
  exact ⟨hdet1, hdet2⟩

/-- Specialization of `det_add_smul_saturated_summand` to an additive flattening
`F : Tensor3 K I J L →+ Matrix M M K` evaluated on a saturated tensor decomposition `T = ∑ j, S j`. -/
theorem det_add_smul_saturated_flattening
    {K I J L M : Type*} [Field K] [Fintype M] [DecidableEq M]
    {r : ℕ} (T : Tensor3 K I J L) (S : Fin r → Tensor3 K I J L)
    (F : Tensor3 K I J L →+ Matrix M M K) (Fi : Matrix M M K) (κ : Fin r → ℕ)
    (hT : T = ∑ j, S j)
    (hinv : F T * Fi = 1 ∧ Fi * F T = 1)
    (hκ : ∀ j, (F (S j)).rank ≤ κ j)
    (hcard : ∑ j, κ j = Fintype.card M) (i : Fin r) :
    ((1 : Matrix M M K[X]) + (Polynomial.X : K[X]) • (F (S i) * Fi).map Polynomial.C).det =
      (1 + Polynomial.X) ^ (κ i) ∧
    ((F T).map Polynomial.C + (Polynomial.X : K[X]) • (F (S i)).map Polynomial.C).det =
      Polynomial.C (F T).det * (1 + Polynomial.X) ^ (κ i) := by
  have hsum : ∑ j, F (S j) = F T := by rw [← map_sum, ← hT]
  have hinv' : (∑ j, F (S j)) * Fi = 1 ∧ Fi * (∑ j, F (S j)) = 1 := by
    simpa [hsum] using hinv
  simpa [hsum] using
    det_add_smul_saturated_summand (fun j => F (S j)) Fi κ hinv' hκ hcard i

/-! ## Section 5: Equiangular Rank-One Idempotent Bases (Proposition 15) -/

/-- Standard trace Gram matrix `(G_std)_{(a,b),(u,v)} = Tr(E_{ab} E_{uv}) = δ_{bu} δ_{av}` on
`Mat_d(K)`. -/
def stdTraceGram (K : Type*) [CommRing K] (d : ℕ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) K :=
  fun p q => if p.2 = q.1 ∧ p.1 = q.2 then 1 else 0

private def swapDecompEquiv (d : ℕ) :
    (Fin d × Fin d) ⊕ (Fin 1 ⊕ (Fin 2 × Fin d)) ≃ Fin (d + 1) × Fin (d + 1) where
  toFun
    | .inl p => (p.1.castSucc, p.2.castSucc)
    | .inr (.inl _) => (Fin.last d, Fin.last d)
    | .inr (.inr (b, i)) =>
        if b = 0 then (i.castSucc, Fin.last d) else (Fin.last d, i.castSucc)
  invFun pq :=
    Fin.lastCases
      (Fin.lastCases (.inr (.inl 0)) (fun j => .inr (.inr (1, j))) pq.2)
      (fun i => Fin.lastCases (.inr (.inr (0, i))) (fun j => .inl (i, j)) pq.2)
      pq.1
  left_inv x := by
    rcases x with ⟨i, j⟩ | (u | ⟨b, i⟩)
    · simp [Fin.lastCases_castSucc]
    · fin_cases u
      simp [Fin.lastCases_last]
    · fin_cases b <;> simp [Fin.lastCases_castSucc, Fin.lastCases_last]
  right_inv pq := by
    rcases pq with ⟨p, q⟩
    refine Fin.lastCases ?_ (fun i => ?_) p
    · refine Fin.lastCases ?_ (fun j => ?_) q
      · simp [Fin.lastCases_last]
      · simp [Fin.lastCases_last, Fin.lastCases_castSucc]
    · refine Fin.lastCases ?_ (fun j => ?_) q
      · simp [Fin.lastCases_last, Fin.lastCases_castSucc]
      · simp [Fin.lastCases_castSucc]

private lemma triangular_nat_step (d : ℕ) : d * (d - 1) / 2 + d = (d + 1) * d / 2 := by
  cases d with
  | zero => rfl
  | succ k =>
    have hmul : (k + 1 + 1) * (k + 1) = (k + 1) * k + 2 * (k + 1) := by ring
    rw [Nat.add_sub_cancel, hmul, Nat.add_mul_div_left _ _ (by decide : 0 < 2)]

/-- Determinant of the standard trace Gram matrix on `Mat_d(K)`:
`det(G_std) = (-1)^(d (d - 1) / 2)` over every commutative ring `K`. -/
theorem det_stdTraceGram (K : Type*) [CommRing K] (d : ℕ) :
    (stdTraceGram K d).det = (-1 : K) ^ (d * (d - 1) / 2) := by
  induction d with
  | zero =>
    simp [Matrix.det_isEmpty]
  | succ d ih =>
    let F2 : Matrix (Fin 2) (Fin 2) K := ![![0, 1], ![1, 0]]
    rw [← Matrix.det_reindex_self (swapDecompEquiv d).symm (stdTraceGram K (d + 1))]
    have hblk : Matrix.reindex (swapDecompEquiv d).symm (swapDecompEquiv d).symm
        (stdTraceGram K (d + 1)) =
        Matrix.fromBlocks (stdTraceGram K d) 0 0
          (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) K) 0 0
            (Matrix.blockDiagonal (fun _ : Fin d => F2))) := by
      ext x y
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
      rcases x with ⟨i₁, j₁⟩ | (u₁ | ⟨b₁, i₁⟩) <;>
        rcases y with ⟨i₂, j₂⟩ | (u₂ | ⟨b₂, i₂⟩)
      · simp [swapDecompEquiv, stdTraceGram, Matrix.fromBlocks]
      · fin_cases u₂
        simp [swapDecompEquiv, stdTraceGram, Matrix.fromBlocks, Fin.castSucc_ne_last]
      · fin_cases b₂ <;>
          simp [swapDecompEquiv, stdTraceGram, Matrix.fromBlocks, Fin.castSucc_ne_last]
      · fin_cases u₁
        simp [swapDecompEquiv, stdTraceGram, Matrix.fromBlocks, (Fin.castSucc_ne_last _).symm]
      · fin_cases u₁; fin_cases u₂
        simp [swapDecompEquiv, stdTraceGram, Matrix.fromBlocks]
      · fin_cases u₁; fin_cases b₂ <;>
          simp [swapDecompEquiv, stdTraceGram, Matrix.fromBlocks, (Fin.castSucc_ne_last _).symm]
      · fin_cases b₁ <;>
          simp [swapDecompEquiv, stdTraceGram, Matrix.fromBlocks, (Fin.castSucc_ne_last _).symm]
      · fin_cases b₁ <;> fin_cases u₂ <;>
          simp [swapDecompEquiv, stdTraceGram, Matrix.fromBlocks, Fin.castSucc_ne_last]
      · fin_cases b₁ <;> fin_cases b₂ <;>
          simp [swapDecompEquiv, stdTraceGram, Matrix.fromBlocks, Matrix.blockDiagonal, F2,
            Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]
    rw [hblk, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁,
      ih, Matrix.det_one, Matrix.det_blockDiagonal]
    have hF2 : F2.det = -1 := by rw [Matrix.det_fin_two]; simp [F2]
    simp only [hF2, Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_mul]
    rw [← pow_add, triangular_nat_step, Nat.add_sub_cancel]

/-- Equiangular matrix `a I_n + b J_n` with diagonal `a + b` and off-diagonal `b`. -/
def equiangularMat {K : Type*} [CommRing K] (n : ℕ) (a b : K) : Matrix (Fin n) (Fin n) K :=
  fun i j => if i = j then a + b else b

/-- Determinant formula `det(a I_n + b J_n) = (a + n b) * a^(n - 1)` for `n ≥ 1` over any
commutative ring `K`. -/
theorem det_equiangularMat {K : Type*} [CommRing K] {n : ℕ} (hn : 1 ≤ n) (a b : K) :
    (equiangularMat n a b).det = (a + (n : K) * b) * a ^ (n - 1) := by
  cases n with
  | zero => omega
  | succ m =>
    let R1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
      fun i j => if i = j then 1 else if j = 0 then -1 else 0
    let C1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
      fun i j => if i = j then 1 else if j = 0 then 1 else 0
    have hR1_low : R1.IsLowerTriangular := by
      intro i j hij
      have hne : i ≠ j := ne_of_lt hij
      have hj0 : j ≠ 0 := by intro h0; subst h0; exact Nat.not_lt_zero i.val hij
      simp [R1, hne, hj0]
    have hC1_low : C1.IsLowerTriangular := by
      intro i j hij
      have hne : i ≠ j := ne_of_lt hij
      have hj0 : j ≠ 0 := by intro h0; subst h0; exact Nat.not_lt_zero i.val hij
      simp [C1, hne, hj0]
    have hR1_det : R1.det = 1 := by
      rw [Matrix.det_of_isLowerTriangular R1 hR1_low]
      exact Finset.prod_eq_one fun i _ => by simp [R1]
    have hC1_det : C1.det = 1 := by
      rw [Matrix.det_of_isLowerTriangular C1 hC1_low]
      exact Finset.prod_eq_one fun i _ => by simp [C1]
    let RG : Matrix (Fin (m + 1)) (Fin (m + 1)) K := R1 * equiangularMat (m + 1) a b
    have hRG : ∀ i j : Fin (m + 1), RG i j =
        if i = 0 then equiangularMat (m + 1) a b 0 j
        else if j = 0 then -a
        else if i = j then a else 0 := by
      intro i j
      change (R1 * equiangularMat (m + 1) a b) i j = _
      rw [Matrix.mul_apply, Fin.sum_univ_succ]
      refine Fin.cases ?_ (fun i' => ?_) i
      · have htail :
            (∑ x : Fin m, R1 0 x.succ * equiangularMat (m + 1) a b x.succ j) = 0 := by
          refine Finset.sum_eq_zero fun x _ => ?_
          have h0s : (0 : Fin (m + 1)) ≠ x.succ := (Fin.succ_ne_zero x).symm
          simp [R1, h0s, Fin.succ_ne_zero]
        rw [htail, add_zero]
        simp [R1]
      · have hs0 : i'.succ ≠ 0 := Fin.succ_ne_zero i'
        have h0i : (0 : Fin (m + 1)) ≠ i'.succ := hs0.symm
        have htail :
            (∑ x : Fin m, R1 i'.succ x.succ * equiangularMat (m + 1) a b x.succ j) =
              equiangularMat (m + 1) a b i'.succ j := by
          have hite : ∀ x : Fin m, R1 i'.succ x.succ * equiangularMat (m + 1) a b x.succ j =
              if x = i' then equiangularMat (m + 1) a b i'.succ j else 0 := by
            intro x
            by_cases hx : x = i'
            · subst hx; simp [R1]
            · have hsx : i'.succ ≠ x.succ := fun h => hx (Fin.succ_inj.mp h).symm
              simp [R1, hsx, Fin.succ_ne_zero, hx]
          simp_rw [hite]
          simp
        rw [htail]
        have hR10 : R1 i'.succ 0 = -1 := by simp [R1, hs0]
        rw [hR10]
        refine Fin.cases ?_ (fun j' => ?_) j
        · simp only [hs0, ↓reduceIte, equiangularMat]
          ring
        · have hj0 : j'.succ ≠ 0 := Fin.succ_ne_zero j'
          have h0j : (0 : Fin (m + 1)) ≠ j'.succ := hj0.symm
          by_cases hij : i' = j'
          · subst hij
            simp only [hs0, h0i, ↓reduceIte, equiangularMat]
            ring
          · have hsij : i'.succ ≠ j'.succ := fun h => hij (Fin.succ_inj.mp h)
            simp only [hs0, hj0, h0j, hsij, ↓reduceIte, equiangularMat]
            ring
    let U : Matrix (Fin (m + 1)) (Fin (m + 1)) K := RG * C1
    have hU_entry : ∀ i j : Fin (m + 1), U i j =
        if i = 0 then (if j = 0 then a + ((m + 1 : ℕ) : K) * b else b)
        else if i = j then a else 0 := by
      intro i j
      change (RG * C1) i j = _
      rw [Matrix.mul_apply, Fin.sum_univ_succ]
      refine Fin.cases ?_ (fun j' => ?_) j
      · have hC1_0 : ∀ k : Fin (m + 1), C1 k 0 = 1 := by
          intro k; by_cases hk : k = 0 <;> simp [C1, hk]
        simp_rw [hC1_0, mul_one]
        refine Fin.cases ?_ (fun i' => ?_) i
        · simp only [↓reduceIte, hRG]
          have htail : (∑ x : Fin m, equiangularMat (m + 1) a b 0 x.succ) = (m : K) * b := by
            have hc : ∀ x : Fin m, equiangularMat (m + 1) a b 0 x.succ = b := fun x => by
              have h0s : (0 : Fin (m + 1)) ≠ x.succ := (Fin.succ_ne_zero x).symm
              simp [equiangularMat, h0s]
            simp_rw [hc]
            simp
          rw [htail]
          simp only [equiangularMat, ↓reduceIte, Nat.cast_add, Nat.cast_one]
          ring
        · have hs0 : i'.succ ≠ 0 := Fin.succ_ne_zero i'
          simp only [hs0, ↓reduceIte, hRG, Fin.succ_ne_zero]
          have htail : (∑ x : Fin m, if i'.succ = x.succ then a else (0 : K)) = a := by
            simp only [Fin.succ_inj, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
          rw [htail]
          ring
      · have hj0 : j'.succ ≠ 0 := Fin.succ_ne_zero j'
        have hC1_s : ∀ k : Fin (m + 1), C1 k j'.succ = if k = j'.succ then 1 else 0 := by
          intro k; by_cases hk : k = j'.succ <;> simp [C1, hk, hj0]
        simp_rw [hC1_s]
        have h0j : (0 : Fin (m + 1)) ≠ j'.succ := hj0.symm
        have htail : (∑ x : Fin m, RG i x.succ * (if x.succ = j'.succ then 1 else 0)) =
            RG i j'.succ := by
          simp only [Fin.succ_inj, mul_ite, mul_one, mul_zero,
            Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        rw [htail]
        simp only [h0j, ↓reduceIte, mul_zero, zero_add, hRG, hj0]
        by_cases hi0 : i = 0
        · subst hi0; simp [equiangularMat, h0j]
        · simp [hi0]
    have hU_up : U.IsUpperTriangular := by
      intro i j hij
      have hi0 : i ≠ 0 := by intro h0; subst h0; exact Nat.not_lt_zero j.val hij
      have hne : i ≠ j := ne_of_gt hij
      rw [hU_entry]
      simp [hi0, hne]
    have hU_det : U.det = (a + ((m + 1 : ℕ) : K) * b) * a ^ m := by
      rw [Matrix.det_of_isUpperTriangular hU_up, Fin.prod_univ_succ]
      have h00 : U 0 0 = a + ((m + 1 : ℕ) : K) * b := by rw [hU_entry]; simp
      have hdiag : ∀ x : Fin m, U x.succ x.succ = a := fun x => by
        rw [hU_entry]; simp [Fin.succ_ne_zero]
      simp_rw [h00, hdiag]
      simp
    have hdet_rel : U.det = (equiangularMat (m + 1) a b).det := by
      change (R1 * equiangularMat (m + 1) a b * C1).det = _
      rw [Matrix.det_mul, Matrix.det_mul, hR1_det, hC1_det, one_mul, mul_one]
    rw [← hdet_rel, hU_det, Nat.add_sub_cancel]

private lemma trace_sum_eq {K M ι : Type*} [AddCommMonoid K] [Fintype M]
    (s : Finset ι) (f : ι → Matrix M M K) :
    Matrix.trace (∑ i ∈ s, f i) = ∑ i ∈ s, Matrix.trace (f i) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.sum_apply]
  rw [Finset.sum_comm]

private lemma trace_sub_eq {K M : Type*} [AddCommGroup K] [Fintype M]
    (A B : Matrix M M K) :
    Matrix.trace (A - B) = Matrix.trace A - Matrix.trace B := by
  simp [Matrix.trace, Matrix.diag, Finset.sum_sub_distrib]

/-- Any rank-one matrix over a field factors as an outer product `u ⊗ v`. -/
private lemma rank_one_exists_outer {K m n : Type*} [Field K] [Fintype m] [Fintype n]
    [DecidableEq n] (A : Matrix m n K) (hrk : A.rank = 1) :
    ∃ (u : m → K) (v : n → K), ∀ a b, A a b = u a * v b := by
  let R : Submodule K (m → K) := LinearMap.range A.mulVecLin
  have hfin : Module.finrank K R = 1 := hrk
  let bR : Module.Basis (Fin 1) K R := (Module.finBasis K R).reindex (finCongr hfin)
  let u : m → K := (bR 0).1
  let v : n → K := fun j => bR.repr ⟨A.mulVecLin (Pi.single j 1), LinearMap.mem_range_self _ _⟩ 0
  refine ⟨u, v, fun a b => ?_⟩
  have hrep := bR.sum_repr ⟨A.mulVecLin (Pi.single b 1), LinearMap.mem_range_self _ _⟩
  rw [Fin.sum_univ_one] at hrep
  have hval := congrFun (congrArg Subtype.val hrep) a
  have hcol : A.mulVecLin (Pi.single b 1) a = A a b := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hval' : v b * u a = A.mulVecLin (Pi.single b 1) a := by
    simpa [u, v] using hval
  rw [← hcol, ← hval', mul_comm]

/-- A rank-one idempotent matrix `Q` satisfies `Q * X * Q = Tr(Q * X) • Q` for all `X`,
`Tr(Q) = 1`, and the `2 × 2` minor symmetry `Q p r * Q s q = Q p q * Q s r`. -/
private lemma rank_one_idempotent_props {K M : Type*} [Field K] [Fintype M] [DecidableEq M]
    (Q : Matrix M M K) (hidem : Q * Q = Q) (hrk : Q.rank = 1) :
    Matrix.trace Q = 1 ∧
    (∀ X : Matrix M M K, Q * X * Q = Matrix.trace (Q * X) • Q) ∧
    (∀ p q r s : M, Q p r * Q s q = Q p q * Q s r) := by
  have htr : Matrix.trace Q = 1 := by
    rw [matrix_trace_eq_rank_of_idempotent Q hidem, hrk, Nat.cast_one]
  rcases rank_one_exists_outer Q hrk with ⟨u, v, hQ⟩
  refine ⟨htr, ?_, ?_⟩
  · intro X
    ext p q
    simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.trace, Matrix.diag]
    calc (∑ s : M, (∑ r : M, Q p r * X r s) * Q s q)
        = ∑ s : M, ∑ r : M, Q p r * X r s * Q s q := by
            refine Finset.sum_congr rfl fun s _ => ?_
            rw [Finset.sum_mul]
      _ = ∑ s : M, ∑ r : M, Q s r * X r s * Q p q := by
            refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ => ?_
            rw [hQ p r, hQ s q, hQ s r, hQ p q]
            ring
      _ = (∑ s : M, ∑ r : M, Q s r * X r s) * Q p q := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun s _ => (Finset.sum_mul _ _ _).symm
  · intro p q r s
    rw [hQ p r, hQ s q, hQ p q, hQ s r]
    ring

/-- **Proposition 15 (Equiangular rank-one idempotent basis discriminant):**
Let `K` be any field, `d ≥ 2`, and let `Q : Fin (d ^ 2) → Matrix (Fin d) (Fin d) K` be a linearly
independent family of rank-one idempotents with constant off-diagonal trace
`Tr(Q i * Q j) = c` (`i ≠ j`). Then:
1. `(d : K) ≠ 0` and `(d + 1 : K) ≠ 0`,
2. `c = (d + 1 : K)⁻¹`,
3. `∑ i, Q i = (d : K) • 1`, and
4. `IsSquare (if Odd d then (-1 : K) ^ ((d - 1) / 2) * (d : K) else (-1 : K) ^ (d / 2) * (d + 1 : K))`. -/
theorem equiangular_idempotent_basis_discriminant {K : Type*} [Field K] {d : ℕ} (hd : 2 ≤ d)
    (Q : Fin (d ^ 2) → Matrix (Fin d) (Fin d) K) (c : K)
    (hli : LinearIndependent K Q)
    (hidem : ∀ i, Q i * Q i = Q i)
    (hrank : ∀ i, (Q i).rank = 1)
    (hequi : ∀ i j, i ≠ j → Matrix.trace (Q i * Q j) = c) :
    ((d : K) ≠ 0 ∧ (d + 1 : K) ≠ 0) ∧
    c = (d + 1 : K)⁻¹ ∧
    (∑ i, Q i) = (d : K) • (1 : Matrix (Fin d) (Fin d) K) ∧
    IsSquare (if Odd d then (-1 : K) ^ ((d - 1) / 2) * (d : K)
              else (-1 : K) ^ (d / 2) * (d + 1 : K)) := by
  have hQ_props : ∀ i, Matrix.trace (Q i) = 1 ∧
      (∀ X : Matrix (Fin d) (Fin d) K, Q i * X * Q i = Matrix.trace (Q i * X) • Q i) ∧
      (∀ p q r s : Fin d, Q i p r * Q i s q = Q i p q * Q i s r) :=
    fun i => rank_one_idempotent_props (Q i) (hidem i) (hrank i)
  have hQ_tr : ∀ i, Matrix.trace (Q i) = 1 := fun i => (hQ_props i).1
  have hQ_tr_prod : ∀ i j, Matrix.trace (Q i * Q j) = if i = j then 1 else c := by
    intro i j
    by_cases hij : i = j
    · subst hij; rw [hidem i, hQ_tr i]; simp
    · simp [hij, hequi i j hij]
  have hcard_finrank : Fintype.card (Fin (d ^ 2)) =
      Module.finrank K (Matrix (Fin d) (Fin d) K) := by
    rw [Fintype.card_fin, Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one, sq]
  let bQ : Module.Basis (Fin (d ^ 2)) K (Matrix (Fin d) (Fin d) K) :=
    basisOfLinearIndependentOfCardEqFinrank' Q hli hcard_finrank
  have hbQ_apply : ∀ i, bQ i = Q i := fun i => by
    simp [bQ]
  -- Expand 1 = ∑ j, lam j • Q j
  let lam : Fin (d ^ 2) → K := fun j => bQ.repr 1 j
  have h1_eq : (1 : Matrix (Fin d) (Fin d) K) = ∑ j, lam j • Q j := by
    have h := (bQ.sum_repr (1 : Matrix (Fin d) (Fin d) K)).symm
    simpa [lam, hbQ_apply] using h
  have hsum_lam : ∑ j, lam j = (d : K) := by
    have htr1 : Matrix.trace (1 : Matrix (Fin d) (Fin d) K) = (d : K) := by
      simp [Matrix.trace_one]
    rw [← htr1, h1_eq, trace_sum_eq]
    simp [Matrix.trace_smul, hQ_tr]
  have hlam_eq : ∀ i, (1 - c) * lam i + c * (d : K) = 1 := by
    intro i
    have htr : Matrix.trace (Q i * 1) = 1 := by rw [Matrix.mul_one, hQ_tr i]
    rw [h1_eq, Matrix.mul_sum, trace_sum_eq] at htr
    have hexp : (∑ j : Fin (d ^ 2), Matrix.trace (Q i * (lam j • Q j))) =
        (1 - c) * lam i + c * ∑ j, lam j := by
      have hterm : ∀ j : Fin (d ^ 2),
          Matrix.trace (Q i * (lam j • Q j)) =
            (if j = i then (1 - c) * lam j else 0) + c * lam j := by
        intro j
        rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, hQ_tr_prod i j]
        by_cases hji : j = i
        · subst hji; simp; ring
        · have hij : i ≠ j := Ne.symm hji
          simp [hji, hij]; ring
      simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
        ← Finset.mul_sum]
    rw [hexp, hsum_lam] at htr
    exact htr
  have h1_sub_c_ne : 1 - c ≠ 0 := by
    intro h0
    have hc1 : c = 1 := by linear_combination -h0
    have hd2_gt : 1 < d ^ 2 := by nlinarith
    let i0 : Fin (d ^ 2) := ⟨0, by omega⟩
    let i1 : Fin (d ^ 2) := ⟨1, hd2_gt⟩
    have hi01 : i0 ≠ i1 := by intro h; have := congrArg Fin.val h; simp [i0, i1] at this
    let D : Matrix (Fin d) (Fin d) K := Q i0 - Q i1
    have hD_tr_Q : ∀ j, Matrix.trace (D * Q j) = 0 := by
      intro j
      dsimp [D]
      rw [Matrix.sub_mul, trace_sub_eq, hQ_tr_prod i0 j, hQ_tr_prod i1 j, hc1]
      simp
    have hD_tr_all : ∀ X : Matrix (Fin d) (Fin d) K, Matrix.trace (D * X) = 0 := by
      intro X
      have hX : X = ∑ j, bQ.repr X j • Q j := by
        have h := (bQ.sum_repr X).symm
        simpa [hbQ_apply] using h
      rw [hX, Matrix.mul_sum, trace_sum_eq]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [Matrix.mul_smul, Matrix.trace_smul, hD_tr_Q j, smul_zero]
    have hD0 : D = 0 := by
      ext a b
      let E : Matrix (Fin d) (Fin d) K := fun r s => if r = b ∧ s = a then 1 else 0
      have htrE := hD_tr_all E
      have hcalc : Matrix.trace (D * E) = D a b := by
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
        dsimp only [E]
        rw [Finset.sum_eq_single a]
        · rw [Finset.sum_eq_single b]
          · simp
          · intro k _ hkb; simp [hkb]
          · intro hb; exact absurd (Finset.mem_univ b) hb
        · intro r _ hra
          refine Finset.sum_eq_zero fun k _ => ?_
          simp [hra]
        · intro ha; exact absurd (Finset.mem_univ a) ha
      rw [hcalc] at htrE
      exact htrE
    have hQeq : Q i0 = Q i1 := sub_eq_zero.mp hD0
    exact hi01 (hli.injective hQeq)
  have hd2_pos : 0 < d ^ 2 := by nlinarith
  let z0 : Fin (d ^ 2) := ⟨0, hd2_pos⟩
  let lam0 : K := lam z0
  have hlam_const : ∀ i, lam i = lam0 := by
    intro i
    have h1 := hlam_eq i
    have h2 := hlam_eq z0
    have hdiff : (1 - c) * (lam i - lam0) = 0 := by
      dsimp [lam0]
      linear_combination h1 - h2
    exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left h1_sub_c_ne)
  have h1_smul : (1 : Matrix (Fin d) (Fin d) K) = lam0 • ∑ j, Q j := by
    rw [h1_eq, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hlam_const j]
  have hlam0_ne : lam0 ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at h1_smul
    have h00 := congrFun (congrFun h1_smul ⟨0, by omega⟩) ⟨0, by omega⟩
    simp at h00
  have hsum_Q : ∑ j, Q j = lam0⁻¹ • (1 : Matrix (Fin d) (Fin d) K) := by
    calc ∑ j, Q j = (lam0⁻¹ * lam0) • ∑ j, Q j := by rw [inv_mul_cancel₀ hlam0_ne, one_smul]
      _ = lam0⁻¹ • (lam0 • ∑ j, Q j) := by rw [smul_smul]
      _ = lam0⁻¹ • 1 := by rw [← h1_smul]
  -- Key operator identity: ∑ i, Q i * X * Q i = (1 - c) • X + (c * lam0⁻¹ * trace X) • 1
  have hOp_eq : ∀ X : Matrix (Fin d) (Fin d) K,
      ∑ i, Q i * X * Q i =
        (1 - c) • X + (c * lam0⁻¹ * Matrix.trace X) • (1 : Matrix (Fin d) (Fin d) K) := by
    have hOnQ : ∀ j, ∑ i, Q i * Q j * Q i =
        (1 - c) • Q j + (c * lam0⁻¹ * Matrix.trace (Q j)) • (1 : Matrix (Fin d) (Fin d) K) := by
      intro j
      have hstep : ∑ i, Q i * Q j * Q i = ∑ i, Matrix.trace (Q i * Q j) • Q i := by
        refine Finset.sum_congr rfl fun i _ => (hQ_props i).2.1 (Q j)
      rw [hstep]
      have hsplit : ∑ i, Matrix.trace (Q i * Q j) • Q i =
          (1 - c) • Q j + c • ∑ i, Q i := by
        have hterm : ∀ i, Matrix.trace (Q i * Q j) • Q i =
            (if i = j then (1 - c) • Q i else 0) + c • Q i := by
          intro i
          rw [hQ_tr_prod i j]
          by_cases hij : i = j
          · subst hij; simp [sub_smul]
          · simp [hij]
        simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
          ← Finset.smul_sum]
      rw [hsplit, hsum_Q, smul_smul, hQ_tr j, mul_one]
    intro X
    have hX : X = ∑ j, bQ.repr X j • Q j := by
      have h := (bQ.sum_repr X).symm
      simpa [hbQ_apply] using h
    conv_lhs => rw [hX]
    simp_rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [Finset.sum_comm]
    have hpull : ∀ j, ∑ i, bQ.repr X j • (Q i * Q j * Q i) =
        bQ.repr X j • ∑ i, Q i * Q j * Q i := fun j => (Finset.smul_sum).symm
    simp_rw [hpull, hOnQ, smul_add, Finset.sum_add_distrib]
    congr 1
    · conv_rhs => rw [hX]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, smul_smul, mul_comm]
    · conv_rhs => rw [hX]
      rw [trace_sum_eq, Finset.mul_sum, Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.trace_smul, smul_eq_mul, smul_smul]
      congr 1
      ring
  -- Evaluate hOp_eq at E_{11} (entry 0,0) and E_{01} (entry 0,1) using rank-1 symmetry
  let p0 : Fin d := ⟨0, by omega⟩
  let p1 : Fin d := ⟨1, by omega⟩
  have hp01 : p0 ≠ p1 := by intro h; have := congrArg Fin.val h; simp [p0, p1] at this
  let E11 : Matrix (Fin d) (Fin d) K := fun r s => if r = p1 ∧ s = p1 then 1 else 0
  let E01 : Matrix (Fin d) (Fin d) K := fun r s => if r = p0 ∧ s = p1 then 1 else 0
  have hE11_tr : Matrix.trace E11 = 1 := by
    simp only [Matrix.trace, Matrix.diag, E11, and_self, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte]
  have hE01_tr : Matrix.trace E01 = 0 := by
    simp only [Matrix.trace, Matrix.diag, E01]
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases hr : r = p0
    · subst hr; simp [hp01]
    · simp [hr]
  have hLHS_E11 : (∑ i, Q i * E11 * Q i) p0 p0 = ∑ i, Q i p0 p1 * Q i p1 p0 := by
    rw [Matrix.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.mul_apply]
    dsimp only [E11]
    rw [Finset.sum_eq_single p1]
    · rw [Finset.sum_eq_single p1]
      · simp
      · intro k _ hkp; simp [hkp]
      · intro hp; exact absurd (Finset.mem_univ p1) hp
    · intro k _ hkp
      have : (∑ x : Fin d, Q i p0 x * (if x = p1 ∧ k = p1 then (1 : K) else 0)) = 0 :=
        Finset.sum_eq_zero fun x _ => by simp [hkp]
      rw [this, zero_mul]
    · intro hp; exact absurd (Finset.mem_univ p1) hp
  have hLHS_E01 : (∑ i, Q i * E01 * Q i) p0 p1 = ∑ i, Q i p0 p0 * Q i p1 p1 := by
    rw [Matrix.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.mul_apply]
    dsimp only [E01]
    rw [Finset.sum_eq_single p1]
    · rw [Finset.sum_eq_single p0]
      · simp
      · intro k _ hkp; simp [hkp]
      · intro hp; exact absurd (Finset.mem_univ p0) hp
    · intro k _ hkp
      have : (∑ x : Fin d, Q i p0 x * (if x = p0 ∧ k = p1 then (1 : K) else 0)) = 0 :=
        Finset.sum_eq_zero fun x _ => by simp [hkp]
      rw [this, zero_mul]
    · intro hp; exact absurd (Finset.mem_univ p1) hp
  have hsym_sum : (∑ i, Q i p0 p1 * Q i p1 p0) = ∑ i, Q i p0 p0 * Q i p1 p1 :=
    Finset.sum_congr rfl fun i _ => (hQ_props i).2.2 p0 p0 p1 p1
  have hval_E11 : (∑ i, Q i * E11 * Q i) p0 p0 = c * lam0⁻¹ := by
    rw [hOp_eq E11]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, hE11_tr]
    simp [E11, hp01]
  have hval_E01 : (∑ i, Q i * E01 * Q i) p0 p1 = 1 - c := by
    rw [hOp_eq E01]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, hE01_tr]
    simp [E01, hp01]
  have hrel_c_lam : c * lam0⁻¹ = 1 - c := by
    rw [← hval_E11, hLHS_E11, hsym_sum, ← hLHS_E01, hval_E01]
  have hc_eq_prod : (1 - c) * lam0 = c := by
    calc (1 - c) * lam0 = (c * lam0⁻¹) * lam0 := by rw [hrel_c_lam]
      _ = c := by rw [mul_assoc, inv_mul_cancel₀ hlam0_ne, mul_one]
  have hc_d1 : c * ((d : K) + 1) = 1 := by
    have hlam0_eq : (1 - c) * lam0 + c * (d : K) = 1 := hlam_eq z0
    rw [hc_eq_prod] at hlam0_eq
    linear_combination hlam0_eq
  have hd1_ne : (d + 1 : K) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hc_d1
    exact zero_ne_one hc_d1
  have hc_val : c = (d + 1 : K)⁻¹ := by
    calc c = c * ((d + 1 : K) * (d + 1 : K)⁻¹) := by rw [mul_inv_cancel₀ hd1_ne, mul_one]
      _ = (c * (d + 1 : K)) * (d + 1 : K)⁻¹ := by ring
      _ = (d + 1 : K)⁻¹ := by rw [hc_d1, one_mul]
  have hlam0_inv : lam0⁻¹ = (d : K) := by
    have h1 := hrel_c_lam
    rw [hc_val] at h1
    have h2 : (d + 1 : K) * ((d + 1 : K)⁻¹ * lam0⁻¹) = (d + 1 : K) * (1 - (d + 1 : K)⁻¹) :=
      congrArg (fun x => (d + 1 : K) * x) h1
    rw [← mul_assoc, mul_inv_cancel₀ hd1_ne, one_mul, mul_sub, mul_one,
      mul_inv_cancel₀ hd1_ne] at h2
    linear_combination h2
  have hd_ne : (d : K) ≠ 0 := by
    rw [← hlam0_inv]
    exact inv_ne_zero hlam0_ne
  have hsum_Q_d : ∑ i, Q i = (d : K) • (1 : Matrix (Fin d) (Fin d) K) := by
    rw [hsum_Q, hlam0_inv]
  -- Congruence G_Q = Cᵀ G_std C and discriminant square condition
  let e : Fin (d ^ 2) ≃ Fin d × Fin d :=
    Fintype.equivOfCardEq (by simp [sq])
  let Cmat : Matrix (Fin (d ^ 2)) (Fin (d ^ 2)) K := fun a i => Q i (e a).1 (e a).2
  let Gstd : Matrix (Fin (d ^ 2)) (Fin (d ^ 2)) K := (stdTraceGram K d).submatrix e e
  have hGstd_det : Gstd.det = (-1 : K) ^ (d * (d - 1) / 2) := by
    change (Matrix.reindex e.symm e.symm (stdTraceGram K d)).det = _
    rw [Matrix.det_reindex_self, det_stdTraceGram]
  have hcong : Cmatᵀ * Gstd * Cmat = equiangularMat (d ^ 2) (1 - c) c := by
    ext r s
    have htr_rs : Matrix.trace (Q r * Q s) = equiangularMat (d ^ 2) (1 - c) c r s := by
      rw [hQ_tr_prod r s]
      by_cases hrs : r = s
      · subst hrs; simp [equiangularMat]
      · simp [equiangularMat, hrs]
    rw [← htr_rs, Matrix.mul_apply]
    simp_rw [Matrix.mul_apply]
    have hsum1 : ∀ b : Fin (d ^ 2),
        (∑ a : Fin (d ^ 2), Cmatᵀ r a * Gstd a b) * Cmat b s =
        (∑ ij : Fin d × Fin d, Q r ij.1 ij.2 * stdTraceGram K d ij (e b)) *
          Q s (e b).1 (e b).2 := by
      intro b
      congr 1
      simp only [Cmat, Gstd, Matrix.submatrix_apply]
      exact e.sum_comp (fun ij => Q r ij.1 ij.2 * stdTraceGram K d ij (e b))
    simp_rw [hsum1]
    rw [e.sum_comp
      (fun kl : Fin d × Fin d =>
        (∑ ij : Fin d × Fin d, Q r ij.1 ij.2 * stdTraceGram K d ij kl) * Q s kl.1 kl.2)]
    rw [Fintype.sum_prod_type]
    have hinner : ∀ k l : Fin d,
        (∑ ij : Fin d × Fin d, Q r ij.1 ij.2 * stdTraceGram K d ij (k, l)) = Q r l k := by
      intro k l
      rw [Finset.sum_eq_single (l, k)]
      · simp [stdTraceGram]
      · intro ij _ hij
        simp only [stdTraceGram]
        split_ifs with h
        · exfalso; apply hij; exact Prod.ext h.2 h.1
        · ring
      · intro hlk; exact absurd (Finset.mem_univ (l, k)) hlk
    simp_rw [hinner]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    rw [Finset.sum_comm]
  have hdet_cong : (equiangularMat (d ^ 2) (1 - c) c).det =
      (-1 : K) ^ (d * (d - 1) / 2) * Cmat.det ^ 2 := by
    rw [← hcong, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hGstd_det]
    ring
  have h1c_eq : 1 - c = (d : K) * (d + 1 : K)⁻¹ := by
    rw [hc_val]
    field_simp [hd1_ne]
    ring
  have hdet_eq : (equiangularMat (d ^ 2) (1 - c) c).det =
      (d : K) ^ (d ^ 2) * ((d + 1 : K)⁻¹) ^ (d ^ 2 - 1) := by
    rw [det_equiangularMat (by nlinarith : 1 ≤ d ^ 2), h1c_eq, hc_val]
    have hfirst : (d : K) * (d + 1 : K)⁻¹ + ((d ^ 2 : ℕ) : K) * (d + 1 : K)⁻¹ = (d : K) := by
      push_cast
      field_simp [hd1_ne]
      ring
    rw [hfirst, mul_pow]
    have hpow : (d : K) * (d : K) ^ (d ^ 2 - 1) = (d : K) ^ (d ^ 2) := by
      rw [← pow_succ', Nat.sub_add_cancel (by nlinarith : 1 ≤ d ^ 2)]
    rw [← mul_assoc, hpow]
  have hdisc_eq : (-1 : K) ^ (d * (d - 1) / 2) * Cmat.det ^ 2 =
      (d : K) ^ (d ^ 2) * ((d + 1 : K)⁻¹) ^ (d ^ 2 - 1) := by
    rw [← hdet_cong, hdet_eq]
  have hsq : IsSquare (if Odd d then (-1 : K) ^ ((d - 1) / 2) * (d : K)
      else (-1 : K) ^ (d / 2) * (d + 1 : K)) := by
    generalize Cmat.det = detC at hdisc_eq
    by_cases hodd : Odd d
    · simp only [hodd, ↓reduceIte]
      rcases hodd with ⟨k, rfl⟩
      have hhalf : (2 * k + 1 - 1) / 2 = k := by omega
      have htri : (2 * k + 1) * (2 * k + 1 - 1) / 2 = 2 * k ^ 2 + k := by
        have h1 : (2 * k + 1) * (2 * k) = 2 * (2 * k ^ 2 + k) := by ring
        rw [Nat.add_sub_cancel, h1, Nat.mul_div_right _ (by decide : 0 < 2)]
      have hsign : (-1 : K) ^ ((2 * k + 1) * (2 * k + 1 - 1) / 2) = (-1 : K) ^ k := by
        rw [htri, pow_add, pow_mul]
        norm_num
      let m : ℕ := 2 * k ^ 2 + 2 * k
      have hd2_eq : (2 * k + 1) ^ 2 = 2 * m + 1 := by dsimp [m]; ring
      have hd2m1_eq : (2 * k + 1) ^ 2 - 1 = 2 * m := by omega
      rw [hhalf]
      refine ⟨detC * ((2 * k + 1 : ℕ) + 1 : K) ^ m * ((2 * k + 1 : ℕ) : K)⁻¹ ^ m, ?_⟩
      rw [hsign, hd2m1_eq, hd2_eq] at hdisc_eq
      have hsign_sq : (-1 : K) ^ k * (-1 : K) ^ k = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]; norm_num
      have hmul :
          (-1 : K) ^ k * ((((2 * k + 1 : ℕ) : K) + 1) ^ m) ^ 2 *
            (((2 * k + 1 : ℕ) : K)⁻¹ ^ m) ^ 2 *
            ((-1 : K) ^ k * detC ^ 2) =
          (-1 : K) ^ k * ((((2 * k + 1 : ℕ) : K) + 1) ^ m) ^ 2 *
            (((2 * k + 1 : ℕ) : K)⁻¹ ^ m) ^ 2 *
            (((2 * k + 1 : ℕ) : K) ^ (2 * m + 1) *
              ((((2 * k + 1 : ℕ) : K) + 1)⁻¹) ^ (2 * m)) :=
        congrArg _ hdisc_eq
      have hL :
          (-1 : K) ^ k * ((((2 * k + 1 : ℕ) : K) + 1) ^ m) ^ 2 *
            (((2 * k + 1 : ℕ) : K)⁻¹ ^ m) ^ 2 *
            ((-1 : K) ^ k * detC ^ 2) =
          (detC * (((2 * k + 1 : ℕ) : K) + 1) ^ m *
            ((2 * k + 1 : ℕ) : K)⁻¹ ^ m) *
          (detC * (((2 * k + 1 : ℕ) : K) + 1) ^ m *
            ((2 * k + 1 : ℕ) : K)⁻¹ ^ m) := by
        calc _ = ((-1 : K) ^ k * (-1 : K) ^ k) *
              (detC * (((2 * k + 1 : ℕ) : K) + 1) ^ m * ((2 * k + 1 : ℕ) : K)⁻¹ ^ m) *
              (detC * (((2 * k + 1 : ℕ) : K) + 1) ^ m * ((2 * k + 1 : ℕ) : K)⁻¹ ^ m) := by ring
          _ = _ := by rw [hsign_sq, one_mul]
      have hR :
          (-1 : K) ^ k * ((((2 * k + 1 : ℕ) : K) + 1) ^ m) ^ 2 *
            (((2 * k + 1 : ℕ) : K)⁻¹ ^ m) ^ 2 *
            (((2 * k + 1 : ℕ) : K) ^ (2 * m + 1) *
              ((((2 * k + 1 : ℕ) : K) + 1)⁻¹) ^ (2 * m)) =
          (-1 : K) ^ k * ((2 * k + 1 : ℕ) : K) := by
        have h1 : (((2 * k + 1 : ℕ) : K) + 1) ^ m * (((2 * k + 1 : ℕ) : K) + 1)⁻¹ ^ m = 1 := by
          rw [← mul_pow, mul_inv_cancel₀ hd1_ne, one_pow]
        have h2 : ((2 * k + 1 : ℕ) : K)⁻¹ ^ m * ((2 * k + 1 : ℕ) : K) ^ m = 1 := by
          rw [← mul_pow, inv_mul_cancel₀ hd_ne, one_pow]
        have hp1 : ((2 * k + 1 : ℕ) : K) ^ (2 * m + 1) =
            ((2 * k + 1 : ℕ) : K) * (((2 * k + 1 : ℕ) : K) ^ m) ^ 2 := by
          rw [pow_succ', pow_mul', sq]
        have hp2 : ((((2 * k + 1 : ℕ) : K) + 1)⁻¹) ^ (2 * m) =
            ((((2 * k + 1 : ℕ) : K) + 1)⁻¹ ^ m) ^ 2 := by
          rw [pow_mul', sq]
        rw [hp1, hp2]
        calc _ = (-1 : K) ^ k * ((2 * k + 1 : ℕ) : K) *
              (((((2 * k + 1 : ℕ) : K) + 1) ^ m * (((2 * k + 1 : ℕ) : K) + 1)⁻¹ ^ m) ^ 2 *
               (((2 * k + 1 : ℕ) : K)⁻¹ ^ m * ((2 * k + 1 : ℕ) : K) ^ m) ^ 2) := by ring
          _ = (-1 : K) ^ k * ((2 * k + 1 : ℕ) : K) := by rw [h1, h2]; ring
      rw [hL, hR] at hmul
      exact hmul.symm
    · simp only [hodd, ↓reduceIte]
      have heven : Even d := Nat.not_odd_iff_even.mp hodd
      rcases heven with ⟨k, rfl⟩
      have hk_pos : 1 ≤ k := by omega
      have hhalf : (k + k) / 2 = k := by omega
      have hsign : (-1 : K) ^ ((k + k) * (k + k - 1) / 2) = (-1 : K) ^ k := by
        have htri : (k + k) * (k + k - 1) / 2 = k * (2 * k - 1) := by
          have h1 : (k + k) * (k + k - 1) = 2 * (k * (2 * k - 1)) := by
            have : k + k = 2 * k := by omega
            rw [this]; ring
          rw [h1, Nat.mul_div_right _ (by decide : 0 < 2)]
        have hparity : k * (2 * k - 1) + k = 2 * k ^ 2 := by
          have h2k : 2 * k - 1 + 1 = 2 * k := by omega
          calc k * (2 * k - 1) + k = k * (2 * k - 1 + 1) := by ring
            _ = k * (2 * k) := by rw [h2k]
            _ = 2 * k ^ 2 := by ring
        have hmul1 : (-1 : K) ^ (k * (2 * k - 1)) * (-1 : K) ^ k = 1 := by
          rw [← pow_add, hparity, pow_mul]; norm_num
        have hsqk : (-1 : K) ^ k * (-1 : K) ^ k = 1 := by
          rw [← pow_add, ← two_mul, pow_mul]; norm_num
        rw [htri]
        calc (-1 : K) ^ (k * (2 * k - 1))
            = (-1 : K) ^ (k * (2 * k - 1)) * ((-1 : K) ^ k * (-1 : K) ^ k) := by
                rw [hsqk, mul_one]
          _ = ((-1 : K) ^ (k * (2 * k - 1)) * (-1 : K) ^ k) * (-1 : K) ^ k := by ring
          _ = (-1 : K) ^ k := by rw [hmul1, one_mul]
      let m : ℕ := 2 * k ^ 2
      have hd2_eq : (k + k) ^ 2 = 2 * m := by dsimp [m]; ring
      have hd2m1_add : (k + k) ^ 2 - 1 + 1 = 2 * m := by
        have : 1 ≤ (k + k) ^ 2 := by nlinarith
        omega
      rw [hhalf]
      refine ⟨detC * ((k + k : ℕ) + 1 : K) ^ m * ((k + k : ℕ) : K)⁻¹ ^ m, ?_⟩
      have hsign_sq : (-1 : K) ^ k * (-1 : K) ^ k = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]; norm_num
      have hinv_step : (((k + k : ℕ) : K) + 1)⁻¹ ^ ((k + k) ^ 2 - 1) =
          (((k + k : ℕ) : K) + 1) * ((((k + k : ℕ) : K) + 1)⁻¹ ^ m) ^ 2 := by
        have hp : (((k + k : ℕ) : K) + 1)⁻¹ ^ ((k + k) ^ 2 - 1 + 1) =
            ((((k + k : ℕ) : K) + 1)⁻¹ ^ m) ^ 2 := by
          rw [hd2m1_add, pow_mul', sq]
        rw [← hp, pow_succ' (((k + k : ℕ) : K) + 1)⁻¹ ((k + k) ^ 2 - 1), ← mul_assoc,
          mul_inv_cancel₀ hd1_ne, one_mul]
      rw [hsign, hinv_step, hd2_eq] at hdisc_eq
      have hmul :
          (-1 : K) ^ k * ((((k + k : ℕ) : K) + 1) ^ m) ^ 2 *
            (((k + k : ℕ) : K)⁻¹ ^ m) ^ 2 *
            ((-1 : K) ^ k * detC ^ 2) =
          (-1 : K) ^ k * ((((k + k : ℕ) : K) + 1) ^ m) ^ 2 *
            (((k + k : ℕ) : K)⁻¹ ^ m) ^ 2 *
            (((k + k : ℕ) : K) ^ (2 * m) *
              ((((k + k : ℕ) : K) + 1) * ((((k + k : ℕ) : K) + 1)⁻¹ ^ m) ^ 2)) :=
        congrArg _ hdisc_eq
      have hL :
          (-1 : K) ^ k * ((((k + k : ℕ) : K) + 1) ^ m) ^ 2 *
            (((k + k : ℕ) : K)⁻¹ ^ m) ^ 2 *
            ((-1 : K) ^ k * detC ^ 2) =
          (detC * (((k + k : ℕ) : K) + 1) ^ m *
            ((k + k : ℕ) : K)⁻¹ ^ m) *
          (detC * (((k + k : ℕ) : K) + 1) ^ m *
            ((k + k : ℕ) : K)⁻¹ ^ m) := by
        calc _ = ((-1 : K) ^ k * (-1 : K) ^ k) *
              (detC * (((k + k : ℕ) : K) + 1) ^ m * ((k + k : ℕ) : K)⁻¹ ^ m) *
              (detC * (((k + k : ℕ) : K) + 1) ^ m * ((k + k : ℕ) : K)⁻¹ ^ m) := by ring
          _ = _ := by rw [hsign_sq, one_mul]
      have hR :
          (-1 : K) ^ k * ((((k + k : ℕ) : K) + 1) ^ m) ^ 2 *
            (((k + k : ℕ) : K)⁻¹ ^ m) ^ 2 *
            (((k + k : ℕ) : K) ^ (2 * m) *
              ((((k + k : ℕ) : K) + 1) * ((((k + k : ℕ) : K) + 1)⁻¹ ^ m) ^ 2)) =
          (-1 : K) ^ k * (((k + k : ℕ) : K) + 1) := by
        have h1 : (((k + k : ℕ) : K) + 1) ^ m * (((k + k : ℕ) : K) + 1)⁻¹ ^ m = 1 := by
          rw [← mul_pow, mul_inv_cancel₀ hd1_ne, one_pow]
        have h2 : ((k + k : ℕ) : K)⁻¹ ^ m * ((k + k : ℕ) : K) ^ m = 1 := by
          rw [← mul_pow, inv_mul_cancel₀ hd_ne, one_pow]
        have hp1 : ((k + k : ℕ) : K) ^ (2 * m) = (((k + k : ℕ) : K) ^ m) ^ 2 := by
          rw [pow_mul', sq]
        rw [hp1]
        calc _ = (-1 : K) ^ k * (((k + k : ℕ) : K) + 1) *
              (((((k + k : ℕ) : K) + 1) ^ m * (((k + k : ℕ) : K) + 1)⁻¹ ^ m) ^ 2 *
               (((k + k : ℕ) : K)⁻¹ ^ m * ((k + k : ℕ) : K) ^ m) ^ 2) := by ring
          _ = (-1 : K) ^ k * (((k + k : ℕ) : K) + 1) := by rw [h1, h2]; ring
      rw [hL, hR] at hmul
      exact hmul.symm
  exact ⟨⟨hd_ne, hd1_ne⟩, hc_val, hsum_Q_d, hsq⟩

/-- **Proposition 15 (Ordered-field nonexistence):** Over any strictly ordered field `K`,
no `d²`-element linearly independent family of rank-one idempotents in `Mat_d(K)` (`d ≥ 2`)
with constant off-diagonal trace exists. -/
theorem no_equiangular_idempotent_basis_orderedField
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {d : ℕ} (hd : 2 ≤ d)
    (Q : Fin (d ^ 2) → Matrix (Fin d) (Fin d) K) (c : K)
    (hli : LinearIndependent K Q)
    (hidem : ∀ i, Q i * Q i = Q i)
    (hrank : ∀ i, (Q i).rank = 1)
    (hequi : ∀ i j, i ≠ j → Matrix.trace (Q i * Q j) = c) :
    False := by
  have ⟨⟨_, hd1_ne⟩, hc_val, _, _⟩ :=
    equiangular_idempotent_basis_discriminant hd Q c hli hidem hrank hequi
  have hQ_tr : ∀ i, Matrix.trace (Q i) = 1 := fun i =>
    (rank_one_idempotent_props (Q i) (hidem i) (hrank i)).1
  have hQ_tr_prod : ∀ i j, Matrix.trace (Q i * Q j) = if i = j then 1 else c := by
    intro i j
    by_cases hij : i = j
    · subst hij; rw [hidem i, hQ_tr i]; simp
    · simp [hij, hequi i j hij]
  have hcard_finrank : Fintype.card (Fin (d ^ 2)) =
      Module.finrank K (Matrix (Fin d) (Fin d) K) := by
    rw [Fintype.card_fin, Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one, sq]
  let bQ : Module.Basis (Fin (d ^ 2)) K (Matrix (Fin d) (Fin d) K) :=
    basisOfLinearIndependentOfCardEqFinrank' Q hli hcard_finrank
  let i0 : Fin d := ⟨0, by omega⟩
  let i1 : Fin d := ⟨1, by omega⟩
  have hi01 : i0 ≠ i1 := by intro h; have := congrArg Fin.val h; simp [i0, i1] at this
  let A : Matrix (Fin d) (Fin d) K :=
    fun r s => (if r = i0 ∧ s = i1 then 1 else 0) - (if r = i1 ∧ s = i0 then 1 else 0)
  have htr_neg : Matrix.trace (A * A) = -2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    have hdiag : ∀ r : Fin d, (∑ k : Fin d, A r k * A k r) =
        (if r = i0 then (-1 : K) else 0) + (if r = i1 then (-1 : K) else 0) := by
      intro r
      by_cases hr0 : r = i0
      · subst hr0
        rw [Finset.sum_eq_single i1]
        · simp [A, hi01, hi01.symm]
        · intro k _ hk1; simp [A, hi01, hk1]
        · intro h1; exact absurd (Finset.mem_univ i1) h1
      · by_cases hr1 : r = i1
        · subst hr1
          rw [Finset.sum_eq_single i0]
          · simp [A, hi01, hi01.symm]
          · intro k _ hk0; simp [A, hi01.symm, hk0]
          · intro h0; exact absurd (Finset.mem_univ i0) h0
        · simp only [hr0, hr1, ↓reduceIte, add_zero]
          refine Finset.sum_eq_zero fun k _ => ?_
          simp [A, hr0, hr1]
    simp only [hdiag, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    norm_num
  let α : Fin (d ^ 2) → K := fun i => bQ.repr A i
  have hA_eq : A = ∑ i, α i • Q i := by
    have h := (bQ.sum_repr A).symm
    simpa [α, bQ] using h
  have htr_nonneg : 0 ≤ Matrix.trace (A * A) := by
    have hexp : Matrix.trace (A * A) =
        (1 - c) * (∑ i, α i * α i) + c * ((∑ i, α i) * (∑ j, α j)) := by
      conv_lhs => rw [hA_eq]
      rw [Matrix.sum_mul, trace_sum_eq]
      simp_rw [Matrix.mul_sum, trace_sum_eq, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.trace_smul, smul_eq_mul, hQ_tr_prod]
      have hterm : ∀ i j : Fin (d ^ 2),
          α i * (α j * (if i = j then (1 : K) else c)) =
            (if j = i then (1 - c) * (α i * α i) else 0) + c * (α i * α j) := by
        intro i j
        by_cases hij : i = j
        · subst hij; simp; ring
        · have hji : j ≠ i := Ne.symm hij
          simp [hij, hji]; ring
      simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      congr 1
      · rw [Finset.mul_sum]
      · rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
    rw [hexp]
    have hd_pos : (0 : K) < (d : K) := by exact_mod_cast (by omega : 0 < d)
    have hd1_pos : (0 : K) < (d + 1 : K) := by linarith
    have hc_pos : 0 < c := by rw [hc_val]; exact inv_pos.mpr hd1_pos
    have h1c_pos : 0 < 1 - c := by
      have : 1 - c = (d : K) * (d + 1 : K)⁻¹ := by
        rw [hc_val]; field_simp [hd1_ne]; ring
      rw [this]
      exact mul_pos hd_pos (inv_pos.mpr hd1_pos)
    have hs1 : 0 ≤ ∑ i, α i * α i := Finset.sum_nonneg fun i _ => mul_self_nonneg (α i)
    have hs2 : 0 ≤ (∑ i, α i) * (∑ j, α j) := mul_self_nonneg (∑ i, α i)
    exact add_nonneg (mul_nonneg (le_of_lt h1c_pos) hs1) (mul_nonneg (le_of_lt hc_pos) hs2)
  linarith

end SemaevRCB
