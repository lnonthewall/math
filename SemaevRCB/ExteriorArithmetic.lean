module

public import SemaevRCB.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Choose.Dvd
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic

@[expose] public section

/-!
# Shared Exterior Volume Tensors in Odd Prime Characteristics (`SemaevRCB.ExteriorArithmetic`)

Formalizes the all-parameter (`p ≥ 1, m ≥ 1`) odd-prime exterior/Pieri obstruction:
1. Subset-indexed exterior volume tensor `Omega_p` on `PSub p` (`p`-subsets of `Fin (2p + 1)`)
   and its `m`-copy mode-shared tensor `U_pm = I_m ⊗₁,₂ Omega_p`, together with shuffle-sign
   identities and `(1,2)`-symmetry for even `p`.
2. Middle Koszul / Pieri flattening `psiFlat` and its `m`-copy block form `psiFlat_pm`, with
   the unconditional pure-tensor rank bound `≤ (2p).choose p` over every field `K`.
3. Odd-graph / Kneser disjointness matrices `kneserMat` (`B_q`, including `B_0 = [1]`),
   integral adjugate identity over every `CommRing` (`kneserMat_mul_adj`), and explicit inverse
   `kneserInv` whenever `1, …, q + 1` are invertible (`kneserMat_mul_inv`, Lemma 11).
4. Signed Kneser block decomposition of `psiFlat p (Omega_p K p)` (Lemma 10), explicit
   blockwise inverse `psiFlatOmegaInv` / `psiFlatOmegaInv_pm` (Corollary 12), and Vandermonde
   coordinate trace formula `psiFlat_Omega_coord_trace` (Proposition 13).
5. All-parameter odd-prime tensor-rank lower bound `shared_exterior_prime_char_rank_ge`
   (Theorem 9) and its `(p = 2, m = 3, char K = 5)` `5`-Pfaffian specialization
   `pfaffian5_shared3_char5_rank_ge_51`.
-/

namespace SemaevRCB

open Matrix BigOperators

/-! ## Section 1: Subset Indexing, Shuffle Signs, `Omega_p`, and `U_pm` -/

/-- `q`-element subsets of a finite type `V`. -/
abbrev QSub (V : Type*) (q : ℕ) := {C : Finset V // C.card = q}

/-- `p`-element subsets of `Fin (2 * p + 1)`. -/
abbrev PSub (p : ℕ) := {I : Finset (Fin (2 * p + 1)) // I.card = p}

theorem card_QSub (V : Type*) [Fintype V] [DecidableEq V] (q : ℕ) :
    Fintype.card (QSub V q) = Nat.choose (Fintype.card V) q := by
  let e : QSub V q ≃ {C // C ∈ (Finset.univ : Finset V).powersetCard q} :=
    { toFun := fun C => ⟨C.1, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, C.2⟩⟩
      invFun := fun C => ⟨C.1, (Finset.mem_powersetCard.mp C.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ]

theorem card_PSub (p : ℕ) : Fintype.card (PSub p) = Nat.choose (2 * p + 1) p := by
  rw [card_QSub (Fin (2 * p + 1)) p, Fintype.card_fin]

/-- Number of inversions between two finite sets in a linear order: pairs `(a, b) ∈ A × B`
with `b < a`. -/
def finsetInv {α : Type*} [LinearOrder α] (A B : Finset α) : ℕ :=
  ((A ×ˢ B).filter (fun ab => ab.2 < ab.1)).card

/-- Shuffle sign `(-1)^{inv(A, B)} ∈ {±1}` of concatenating `A` before `B`. -/
def finsetSign {α : Type*} [LinearOrder α] (A B : Finset α) : ℤ :=
  (-1 : ℤ) ^ finsetInv A B

@[simp]
lemma finsetInv_empty_left {α : Type*} [LinearOrder α] (B : Finset α) :
    finsetInv ∅ B = 0 := by
  simp [finsetInv]

@[simp]
lemma finsetInv_empty_right {α : Type*} [LinearOrder α] (A : Finset α) :
    finsetInv A ∅ = 0 := by
  simp [finsetInv]

@[simp]
lemma finsetSign_empty_left {α : Type*} [LinearOrder α] (B : Finset α) :
    finsetSign ∅ B = 1 := by
  simp [finsetSign]

@[simp]
lemma finsetSign_empty_right {α : Type*} [LinearOrder α] (A : Finset α) :
    finsetSign A ∅ = 1 := by
  simp [finsetSign]

lemma finsetSign_mul_self {α : Type*} [LinearOrder α] (A B : Finset α) :
    finsetSign A B * finsetSign A B = 1 := by
  simp only [finsetSign, ← mul_pow]
  norm_num

lemma finsetInv_union_left {α : Type*} [LinearOrder α] {A B C : Finset α}
    (hAB : Disjoint A B) :
    finsetInv (A ∪ B) C = finsetInv A C + finsetInv B C := by
  unfold finsetInv
  rw [Finset.union_product, Finset.filter_union, Finset.card_union_of_disjoint]
  refine Finset.disjoint_left.mpr fun x hxA hxB => ?_
  rw [Finset.mem_filter, Finset.mem_product] at hxA hxB
  exact Finset.disjoint_left.mp hAB hxA.1.1 hxB.1.1

lemma finsetInv_union_right {α : Type*} [LinearOrder α] {A B C : Finset α}
    (hBC : Disjoint B C) :
    finsetInv A (B ∪ C) = finsetInv A B + finsetInv A C := by
  unfold finsetInv
  rw [Finset.product_union, Finset.filter_union, Finset.card_union_of_disjoint]
  refine Finset.disjoint_left.mpr fun x hxB hxC => ?_
  rw [Finset.mem_filter, Finset.mem_product] at hxB hxC
  exact Finset.disjoint_left.mp hBC hxB.1.2 hxC.1.2

lemma finsetSign_union_left {α : Type*} [LinearOrder α] {A B C : Finset α}
    (hAB : Disjoint A B) :
    finsetSign (A ∪ B) C = finsetSign A C * finsetSign B C := by
  simp only [finsetSign, finsetInv_union_left hAB, pow_add]

lemma finsetSign_union_right {α : Type*} [LinearOrder α] {A B C : Finset α}
    (hBC : Disjoint B C) :
    finsetSign A (B ∪ C) = finsetSign A B * finsetSign A C := by
  simp only [finsetSign, finsetInv_union_right hBC, pow_add]

/-- Associativity of shuffle signs on disjoint sets. -/
lemma finsetSign_assoc {α : Type*} [LinearOrder α] {X Y Z : Finset α}
    (hXY : Disjoint X Y) (hYZ : Disjoint Y Z) :
    finsetSign X Y * finsetSign (X ∪ Y) Z = finsetSign X (Y ∪ Z) * finsetSign Y Z := by
  rw [finsetSign_union_left hXY, finsetSign_union_right hYZ, mul_assoc]

lemma finsetInv_add_comm {α : Type*} [LinearOrder α] {A B : Finset α}
    (hAB : Disjoint A B) :
    finsetInv A B + finsetInv B A = A.card * B.card := by
  unfold finsetInv
  have hswap : ((B ×ˢ A).filter (fun ba => ba.2 < ba.1)).card =
      ((A ×ˢ B).filter (fun ab => ab.1 < ab.2)).card := by
    refine Finset.card_bij (fun ba _ => (ba.2, ba.1)) ?_ ?_ ?_
    · intro ba hba
      simp only [Finset.mem_filter, Finset.mem_product] at hba ⊢
      exact ⟨⟨hba.1.2, hba.1.1⟩, hba.2⟩
    · intro x _ y _ hxy
      exact Prod.ext (congrArg Prod.snd hxy) (congrArg Prod.fst hxy)
    · intro ab hab
      simp only [Finset.mem_filter, Finset.mem_product] at hab
      refine ⟨(ab.2, ab.1), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hab.1.2, hab.1.1⟩, hab.2⟩
  rw [hswap, ← Finset.card_union_of_disjoint]
  · have hunion : (A ×ˢ B).filter (fun ab => ab.2 < ab.1) ∪
        (A ×ˢ B).filter (fun ab => ab.1 < ab.2) = A ×ˢ B := by
      ext ⟨a, b⟩
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro ⟨ha, hb⟩
        have hne : a ≠ b := fun heq => Finset.disjoint_left.mp hAB ha (heq ▸ hb)
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact Or.inr ⟨⟨ha, hb⟩, hlt⟩
        · exact Or.inl ⟨⟨ha, hb⟩, hgt⟩
    rw [hunion, Finset.card_product]
  · refine Finset.disjoint_left.mpr fun x h1 h2 => ?_
    rw [Finset.mem_filter] at h1 h2
    exact lt_asymm h1.2 h2.2

/-- Commutativity parity of shuffle signs on disjoint sets. -/
lemma finsetSign_comm {α : Type*} [LinearOrder α] {A B : Finset α}
    (hAB : Disjoint A B) :
    finsetSign A B * finsetSign B A = (-1 : ℤ) ^ (A.card * B.card) := by
  simp only [finsetSign, ← pow_add, finsetInv_add_comm hAB]

lemma finsetSign_swap {α : Type*} [LinearOrder α] {A B : Finset α}
    (hAB : Disjoint A B) :
    finsetSign B A = (-1 : ℤ) ^ (A.card * B.card) * finsetSign A B := by
  calc finsetSign B A
      = (finsetSign A B * finsetSign A B) * finsetSign B A := by rw [finsetSign_mul_self, one_mul]
    _ = finsetSign A B * (finsetSign A B * finsetSign B A) := by ring
    _ = (-1 : ℤ) ^ (A.card * B.card) * finsetSign A B := by rw [finsetSign_comm hAB]; ring

lemma neg_one_pow_mul_self (n : ℕ) : (-1 : ℤ) ^ (n * n) = (-1 : ℤ) ^ n := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have h1 : Even (k + k) := ⟨k, rfl⟩
    have h2 : Even ((k + k) * (k + k)) := ⟨(k + k) * k, by ring⟩
    rw [h1.neg_one_pow, h2.neg_one_pow]
  · have h1 : Odd (2 * k + 1) := ⟨k, rfl⟩
    have h2 : Odd ((2 * k + 1) * (2 * k + 1)) := ⟨2 * k * k + 2 * k, by ring⟩
    rw [h1.neg_one_pow, h2.neg_one_pow]

/-- Signed exterior-volume coefficient `ε_{I, J, k} ∈ {0, ±1}` for `p`-subsets `I, J` of
`Fin (2p + 1)` and `k ∈ Fin (2p + 1)`: nonzero precisely when `I, J, {k}` partition `univ`. -/
def exteriorSign (p : ℕ) (I J : PSub p) (k : Fin (2 * p + 1)) : ℤ :=
  if Disjoint I.1 J.1 ∧ k ∉ I.1 ∧ k ∉ J.1 then
    finsetSign I.1 J.1 * finsetSign (I.1 ∪ J.1) {k}
  else 0

lemma exteriorSign_partition {p : ℕ} {I J : PSub p} {k : Fin (2 * p + 1)}
    (h : Disjoint I.1 J.1 ∧ k ∉ I.1 ∧ k ∉ J.1) :
    I.1 ∪ J.1 = Finset.univ.erase k := by
  have hk_not : k ∉ I.1 ∪ J.1 := by
    simp [h.2.1, h.2.2]
  have hcard : (insert k (I.1 ∪ J.1)).card = (Finset.univ : Finset (Fin (2 * p + 1))).card := by
    rw [Finset.card_insert_of_notMem hk_not, Finset.card_union_of_disjoint h.1, I.2, J.2,
      Finset.card_univ, Fintype.card_fin]
    omega
  have huniv : insert k (I.1 ∪ J.1) = Finset.univ := Finset.eq_univ_of_card _ hcard
  rw [← huniv, Finset.erase_insert hk_not]

lemma exteriorSign_cond_iff {p : ℕ} {I J : PSub p} {k : Fin (2 * p + 1)} :
    (Disjoint I.1 J.1 ∧ k ∉ I.1 ∧ k ∉ J.1) ↔ I.1 ∪ J.1 = Finset.univ.erase k := by
  constructor
  · exact exteriorSign_partition
  · intro heq
    have hk_not : k ∉ I.1 ∪ J.1 := by
      rw [heq]
      exact Finset.notMem_erase k _
    have hcard_u : (I.1 ∪ J.1).card = 2 * p := by
      rw [heq, Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
      omega
    have hinter_card : (I.1 ∩ J.1).card = 0 := by
      have h := Finset.card_union_add_card_inter I.1 J.1
      rw [hcard_u, I.2, J.2] at h
      omega
    have hdisj : Disjoint I.1 J.1 :=
      Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hinter_card)
    rw [Finset.mem_union, not_or] at hk_not
    exact ⟨hdisj, hk_not.1, hk_not.2⟩

lemma exteriorSign_swap (p : ℕ) (I J : PSub p) (k : Fin (2 * p + 1)) :
    exteriorSign p J I k = (-1 : ℤ) ^ p * exteriorSign p I J k := by
  unfold exteriorSign
  have hcond : (Disjoint J.1 I.1 ∧ k ∉ J.1 ∧ k ∉ I.1) ↔
      (Disjoint I.1 J.1 ∧ k ∉ I.1 ∧ k ∉ J.1) := by
    simp only [disjoint_comm, and_comm]
  by_cases h : Disjoint I.1 J.1 ∧ k ∉ I.1 ∧ k ∉ J.1
  · have h' : Disjoint J.1 I.1 ∧ k ∉ J.1 ∧ k ∉ I.1 := hcond.mpr h
    rw [ite_eq_left_of_eq_true _ _ (eq_true h'), ite_eq_left_of_eq_true _ _ (eq_true h),
      Finset.union_comm J.1 I.1, finsetSign_swap h.1, I.2, J.2, neg_one_pow_mul_self]
    ring
  · have h' : ¬ (Disjoint J.1 I.1 ∧ k ∉ J.1 ∧ k ∉ I.1) := mt hcond.mp h
    rw [ite_eq_right_of_eq_false _ _ (eq_false h'), ite_eq_right_of_eq_false _ _ (eq_false h), mul_zero]

lemma exteriorSign_mul_self {p : ℕ} {I J : PSub p} {k : Fin (2 * p + 1)}
    (h : Disjoint I.1 J.1 ∧ k ∉ I.1 ∧ k ∉ J.1) :
    exteriorSign p I J k * exteriorSign p I J k = 1 := by
  rw [exteriorSign, ite_eq_left_of_eq_true _ _ (eq_true h)]
  calc (finsetSign I.1 J.1 * finsetSign (I.1 ∪ J.1) {k}) *
        (finsetSign I.1 J.1 * finsetSign (I.1 ∪ J.1) {k})
      = (finsetSign I.1 J.1 * finsetSign I.1 J.1) *
        (finsetSign (I.1 ∪ J.1) {k} * finsetSign (I.1 ∪ J.1) {k}) := by ring
    _ = 1 := by rw [finsetSign_mul_self, finsetSign_mul_self, mul_one]

/-- Exterior volume tensor `Ω_p ∈ ∧^p(K^{2p+1}) ⊗ ∧^p(K^{2p+1}) ⊗ K^{2p+1}` indexed by
`p`-subsets of `Fin (2p + 1)`. -/
def Omega_p (K : Type*) [CommRing K] (p : ℕ) :
    Tensor3 K (PSub p) (PSub p) (Fin (2 * p + 1)) :=
  fun I J k => (exteriorSign p I J k : K)

/-- Mode-shared `m`-copy exterior tensor `U_{p,m} = I_m ⊗₁,₂ Ω_p`. -/
def U_pm (K : Type*) [CommRing K] (p m : ℕ) :
    Tensor3 K (Fin m × PSub p) (Fin m × PSub p) (Fin (2 * p + 1)) :=
  fun b₁ b₂ k => if b₁.1 = b₂.1 then Omega_p K p b₁.2 b₂.2 k else 0

/-- When `p` is even (in particular `p = 2`), `Omega_p K p` is `(1,2)`-symmetric. -/
theorem Omega_p_isSym12_of_even {K : Type*} [CommRing K] {p : ℕ} (hp : Even p) :
    ∀ I J k, Omega_p K p I J k = Omega_p K p J I k := by
  intro I J k
  simp only [Omega_p, exteriorSign_swap p I J k, hp.neg_one_pow, one_mul]

/-- When `p` is even (in particular `p = 2`), `U_pm K p m` is `(1,2)`-symmetric. -/
theorem U_pm_isSym12_of_even {K : Type*} [CommRing K] {p m : ℕ} (hp : Even p) :
    ∀ b₁ b₂ k, U_pm K p m b₁ b₂ k = U_pm K p m b₂ b₁ k := by
  intro b₁ b₂ k
  unfold U_pm
  by_cases h : b₁.1 = b₂.1
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true h.symm),
      Omega_p_isSym12_of_even hp]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false (Ne.symm h))]

/-! ## Section 2: Middle Koszul Flattening `psiFlat` and Pure-Tensor Rank Bound -/

/-- Single-copy middle Koszul / Pieri flattening `Ψ_p(X)` indexed by `(J, L)` on rows and
`(S, I)` on columns: `(Ψ_p(X))_{(J,L),(S,I)} = ∑_k X_{I,J,k} ε_{S,L,k}`. -/
def psiFlat {K : Type*} [CommRing K] (p : ℕ)
    (X : Tensor3 K (PSub p) (PSub p) (Fin (2 * p + 1))) :
    Matrix (PSub p × PSub p) (PSub p × PSub p) K :=
  fun row col => ∑ k : Fin (2 * p + 1), X col.2 row.1 k * (exteriorSign p col.1 row.2 k : K)

/-- `m`-copy middle Koszul / Pieri flattening `Ψ_{p,m}(X)` indexed by `(a, J, L)` on rows and
`(b, S, I)` on columns, whose `(a, b)` block is `psiFlat p (fun I J k => X (b, I) (a, J) k)`. -/
def psiFlat_pm {K : Type*} [CommRing K] (p m : ℕ)
    (X : Tensor3 K (Fin m × PSub p) (Fin m × PSub p) (Fin (2 * p + 1))) :
    Matrix (Fin m × PSub p × PSub p) (Fin m × PSub p × PSub p) K :=
  fun row col =>
    psiFlat p (fun I J k => X (col.1, I) (row.1, J) k) row.2 col.2

lemma psiFlat_add {K : Type*} [CommRing K] (p : ℕ)
    (X Y : Tensor3 K (PSub p) (PSub p) (Fin (2 * p + 1))) :
    psiFlat p (fun I J k => X I J k + Y I J k) = psiFlat p X + psiFlat p Y := by
  ext row col
  simp only [psiFlat, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

lemma psiFlat_sum {K ι : Type*} [CommRing K] (p : ℕ)
    (s : Finset ι) (X : ι → Tensor3 K (PSub p) (PSub p) (Fin (2 * p + 1))) :
    psiFlat p (fun I J k => ∑ t ∈ s, X t I J k) = ∑ t ∈ s, psiFlat p (X t) := by
  ext row col
  simp only [psiFlat, Matrix.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

lemma psiFlat_pm_sum {K ι : Type*} [CommRing K] (p m : ℕ)
    (s : Finset ι) (X : ι → Tensor3 K (Fin m × PSub p) (Fin m × PSub p) (Fin (2 * p + 1))) :
    psiFlat_pm p m (fun b₁ b₂ k => ∑ t ∈ s, X t b₁ b₂ k) =
      ∑ t ∈ s, psiFlat_pm p m (X t) := by
  ext row col
  simp only [psiFlat_pm, psiFlat, Matrix.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

/-- Wedge-multiplication matrix `W_w[L, S] = ∑_k w_k ε_{S, L, k}` on `PSub p`. -/
def wedgeMat {K : Type*} [CommRing K] (p : ℕ) (w : Fin (2 * p + 1) → K) :
    Matrix (PSub p) (PSub p) K :=
  fun L S => ∑ k : Fin (2 * p + 1), w k * (exteriorSign p S L k : K)

private lemma sum_skew_eq_zero {α M : Type*} [LinearOrder α] [AddCommGroup M]
    (A : Finset α) (f : α → α → M)
    (hdiag : ∀ a ∈ A, f a a = 0)
    (hskew : ∀ a ∈ A, ∀ b ∈ A, f b a = -f a b) :
    ∑ a ∈ A, ∑ b ∈ A, f a b = 0 := by
  rw [← Finset.sum_product']
  let P_lt := (A ×ˢ A).filter (fun ab => ab.1 < ab.2)
  let P_eq := (A ×ˢ A).filter (fun ab => ab.1 = ab.2)
  let P_gt := (A ×ˢ A).filter (fun ab => ab.2 < ab.1)
  have hpart : A ×ˢ A = P_lt ∪ (P_eq ∪ P_gt) := by
    ext ⟨a, b⟩
    simp only [P_lt, P_eq, P_gt, Finset.mem_union, Finset.mem_filter, Finset.mem_product]
    constructor
    · intro h
      rcases lt_trichotomy a b with h1 | h2 | h3
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr (Or.inl ⟨h, h2⟩)
      · exact Or.inr (Or.inr ⟨h, h3⟩)
    · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hd1 : Disjoint P_lt (P_eq ∪ P_gt) := by
    refine Finset.disjoint_left.mpr fun x h1 h2 => ?_
    simp only [P_lt, P_eq, P_gt, Finset.mem_union, Finset.mem_filter] at h1 h2
    rcases h2 with ⟨_, heq⟩ | ⟨_, hgt⟩
    · exact ne_of_lt h1.2 heq
    · exact lt_asymm h1.2 hgt
  have hd2 : Disjoint P_eq P_gt := by
    refine Finset.disjoint_left.mpr fun x h1 h2 => ?_
    simp only [P_eq, P_gt, Finset.mem_filter] at h1 h2
    exact ne_of_gt h2.2 h1.2
  rw [hpart, Finset.sum_union hd1, Finset.sum_union hd2]
  have heq_zero : ∑ ab ∈ P_eq, f ab.1 ab.2 = 0 := by
    refine Finset.sum_eq_zero fun ab hab => ?_
    simp only [P_eq, Finset.mem_filter, Finset.mem_product] at hab
    rw [hab.2]
    exact hdiag ab.2 hab.1.2
  have hgt_neg : ∑ ab ∈ P_gt, f ab.1 ab.2 = -∑ ab ∈ P_lt, f ab.1 ab.2 := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_bij (fun ab _ => (ab.2, ab.1)) ?_ ?_ ?_ ?_
    · intro ab hab
      simp only [P_gt, P_lt, Finset.mem_filter, Finset.mem_product] at hab ⊢
      exact ⟨⟨hab.1.2, hab.1.1⟩, hab.2⟩
    · intro x _ y _ hxy
      exact Prod.ext (congrArg Prod.snd hxy) (congrArg Prod.fst hxy)
    · intro ab hab
      simp only [P_lt, P_gt, Finset.mem_filter, Finset.mem_product] at hab ⊢
      exact ⟨(ab.2, ab.1), ⟨⟨hab.1.2, hab.1.1⟩, hab.2⟩, rfl⟩
    · intro ab hab
      simp only [P_gt, Finset.mem_filter, Finset.mem_product] at hab
      exact hskew ab.2 hab.1.2 ab.1 hab.1.1
  rw [heq_zero, hgt_neg, zero_add, add_neg_cancel]

private lemma wedge_exterior_skew {p : ℕ} (S₀ : Finset (Fin (2 * p + 1))) (hS₀ : S₀.card + 1 = p)
    (L : PSub p) (j k : Fin (2 * p + 1)) (hj : j ∉ S₀) (hk : k ∉ S₀) :
    finsetSign S₀ {k} *
        exteriorSign p ⟨insert k S₀, by rw [Finset.card_insert_of_notMem hk, hS₀]⟩ L j =
      -(finsetSign S₀ {j} *
        exteriorSign p ⟨insert j S₀, by rw [Finset.card_insert_of_notMem hj, hS₀]⟩ L k) := by
  let Sj : PSub p := ⟨insert j S₀, by rw [Finset.card_insert_of_notMem hj, hS₀]⟩
  let Sk : PSub p := ⟨insert k S₀, by rw [Finset.card_insert_of_notMem hk, hS₀]⟩
  change finsetSign S₀ {k} * exteriorSign p Sk L j = -(finsetSign S₀ {j} * exteriorSign p Sj L k)
  by_cases hjk : j = k
  · subst hjk
    have hmem : j ∈ insert j S₀ := Finset.mem_insert_self j S₀
    simp [Sj, Sk, exteriorSign, hmem]
  · have hcond : (Disjoint Sj.1 L.1 ∧ k ∉ Sj.1 ∧ k ∉ L.1) ↔
        (Disjoint Sk.1 L.1 ∧ j ∉ Sk.1 ∧ j ∉ L.1) := by
      simp only [Sj, Sk, Finset.disjoint_insert_left, Finset.mem_insert, not_or]
      constructor
      · rintro ⟨⟨hjL, hS₀L⟩, ⟨hkj, hkS₀⟩, hkL⟩
        exact ⟨⟨hkL, hS₀L⟩, ⟨Ne.symm hkj, hj⟩, hjL⟩
      · rintro ⟨⟨hkL, hS₀L⟩, ⟨hjk', hjS₀⟩, hjL⟩
        exact ⟨⟨hjL, hS₀L⟩, ⟨Ne.symm hjk', hk⟩, hkL⟩
    by_cases h : Disjoint Sj.1 L.1 ∧ k ∉ Sj.1 ∧ k ∉ L.1
    · have h' : Disjoint Sk.1 L.1 ∧ j ∉ Sk.1 ∧ j ∉ L.1 := hcond.mp h
      rw [exteriorSign, exteriorSign, ite_eq_left_of_eq_true _ _ (eq_true h'),
        ite_eq_left_of_eq_true _ _ (eq_true h)]
      rcases h with ⟨hSjL, _, hkL⟩
      have hjL : j ∉ L.1 := (Finset.disjoint_insert_left.mp hSjL).1
      have hS₀L : Disjoint S₀ L.1 := (Finset.disjoint_insert_left.mp hSjL).2
      have hSj_eq : Sj.1 = S₀ ∪ {j} := by
        ext x; simp [Sj]
      have hSk_eq : Sk.1 = S₀ ∪ {k} := by
        ext x; simp [Sk]
      have hS₀_j : Disjoint S₀ {j} := Finset.disjoint_singleton_right.mpr hj
      have hS₀_k : Disjoint S₀ {k} := Finset.disjoint_singleton_right.mpr hk
      have hj_L : Disjoint {j} L.1 := Finset.disjoint_singleton_left.mpr hjL
      have hk_L : Disjoint {k} L.1 := Finset.disjoint_singleton_left.mpr hkL
      have hSjL_u : Disjoint (S₀ ∪ {j}) L.1 := Finset.disjoint_union_left.mpr ⟨hS₀L, hj_L⟩
      have hSkL_u : Disjoint (S₀ ∪ {k}) L.1 := Finset.disjoint_union_left.mpr ⟨hS₀L, hk_L⟩
      have hj_k : Disjoint ({j} : Finset (Fin (2 * p + 1))) {k} :=
        Finset.disjoint_singleton.mpr hjk
      have hSj_exp : finsetSign S₀ {j} * (finsetSign Sj.1 L.1 * finsetSign (Sj.1 ∪ L.1) {k}) =
          (-1 : ℤ) ^ p * finsetSign S₀ L.1 *
            (finsetSign S₀ {j} * finsetSign S₀ {k}) *
            (finsetSign {j} L.1 * finsetSign {k} L.1) *
            finsetSign {j} {k} := by
        rw [hSj_eq, finsetSign_union_left hS₀_j, finsetSign_union_left hSjL_u,
          finsetSign_union_left hS₀_j, finsetSign_swap hk_L]
        simp only [Finset.card_singleton, L.2, one_mul]
        ring
      have hSk_exp : finsetSign S₀ {k} * (finsetSign Sk.1 L.1 * finsetSign (Sk.1 ∪ L.1) {j}) =
          (-1 : ℤ) ^ p * finsetSign S₀ L.1 *
            (finsetSign S₀ {k} * finsetSign S₀ {j}) *
            (finsetSign {k} L.1 * finsetSign {j} L.1) *
            finsetSign {k} {j} := by
        rw [hSk_eq, finsetSign_union_left hS₀_k, finsetSign_union_left hSkL_u,
          finsetSign_union_left hS₀_k, finsetSign_swap hj_L]
        simp only [Finset.card_singleton, L.2, one_mul]
        ring
      have hjk_flip : finsetSign {k} {j} = -finsetSign {j} {k} := by
        rw [finsetSign_swap hj_k]
        simp
      rw [hSj_exp, hSk_exp, hjk_flip]
      ring
    · have h' : ¬ (Disjoint Sk.1 L.1 ∧ j ∉ Sk.1 ∧ j ∉ L.1) := mt hcond.mpr h
      rw [exteriorSign, exteriorSign, ite_eq_right_of_eq_false _ _ (eq_false h'),
        ite_eq_right_of_eq_false _ _ (eq_false h)]
      ring

private lemma wedgeMat_col_relation {K : Type*} [Field K] {p : ℕ}
    (w : Fin (2 * p + 1) → K) (S₀ : Finset (Fin (2 * p + 1))) (hS₀ : S₀.card + 1 = p)
    (L : PSub p) :
    ∑ j ∈ (S₀ᶜ).attach,
      (finsetSign S₀ {j.1} : K) * w j.1 *
        wedgeMat p w L ⟨insert j.1 S₀, by
          rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp j.2), hS₀]⟩ = 0 := by
  have hexpand : ∀ j ∈ (S₀ᶜ).attach,
      (finsetSign S₀ {j.1} : K) * w j.1 *
        wedgeMat p w L ⟨insert j.1 S₀, by
          rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp j.2), hS₀]⟩ =
      ∑ k ∈ S₀ᶜ,
        (finsetSign S₀ {j.1} : K) *
          (exteriorSign p ⟨insert j.1 S₀, by
            rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp j.2), hS₀]⟩ L k : K) *
          (w j.1 * w k) := by
    intro j _
    unfold wedgeMat
    rw [Finset.mul_sum]
    have hsub_sum :
        (∑ k ∈ S₀ᶜ,
          (finsetSign S₀ {j.1} : K) *
            (exteriorSign p ⟨insert j.1 S₀, by
              rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp j.2), hS₀]⟩ L k : K) *
            (w j.1 * w k)) =
        ∑ k : Fin (2 * p + 1),
          (finsetSign S₀ {j.1} : K) *
            (exteriorSign p ⟨insert j.1 S₀, by
              rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp j.2), hS₀]⟩ L k : K) *
            (w j.1 * w k) := by
      refine Finset.sum_subset (Finset.subset_univ S₀ᶜ) fun k _ hk => ?_
      have hkS₀ : k ∈ S₀ := by simpa [Finset.mem_compl] using hk
      have hk_ins : k ∈ insert j.1 S₀ := Finset.mem_insert_of_mem hkS₀
      simp [exteriorSign, hk_ins]
    rw [hsub_sum]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [Finset.sum_congr rfl hexpand]
  let f : Fin (2 * p + 1) → Fin (2 * p + 1) → K := fun j k =>
    if hj : j ∈ S₀ᶜ then
      (finsetSign S₀ {j} : K) *
        (exteriorSign p ⟨insert j S₀, by
          rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp hj), hS₀]⟩ L k : K) *
        (w j * w k)
    else 0
  have hlhs : (∑ j ∈ (S₀ᶜ).attach, ∑ k ∈ S₀ᶜ,
      (finsetSign S₀ {j.1} : K) *
        (exteriorSign p ⟨insert j.1 S₀, by
          rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp j.2), hS₀]⟩ L k : K) *
        (w j.1 * w k)) = ∑ j ∈ S₀ᶜ, ∑ k ∈ S₀ᶜ, f j k := by
    rw [← Finset.sum_attach (s := S₀ᶜ) (f := fun j => ∑ k ∈ S₀ᶜ, f j k)]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    have hj := j.2
    simp only [f, hj, ↓reduceDIte]
  rw [hlhs]
  refine sum_skew_eq_zero S₀ᶜ f ?_ ?_
  · intro j hj
    have hmem : j ∈ insert j S₀ := Finset.mem_insert_self j S₀
    simp only [f, hj, ↓reduceDIte, exteriorSign, hmem, not_true_eq_false, false_and, and_false,
      ↓reduceIte, Int.cast_zero, mul_zero, zero_mul]
  · intro j hj k hk
    simp only [f, hj, hk, ↓reduceDIte]
    have hsk := wedge_exterior_skew S₀ hS₀ L j k
      (Finset.mem_compl.mp hj) (Finset.mem_compl.mp hk)
    have hskK := congrArg (Int.cast (R := K)) hsk
    push_cast at hskK
    rw [hskK]
    ring

private lemma card_PSub_notMem (p : ℕ) (k₀ : Fin (2 * p + 1)) :
    Fintype.card {S : PSub p // k₀ ∉ S.1} = Nat.choose (2 * p) p := by
  let e : {S : PSub p // k₀ ∉ S.1} ≃
      {A // A ∈ (Finset.univ.erase k₀ : Finset (Fin (2 * p + 1))).powersetCard p} :=
    { toFun := fun S =>
        ⟨S.1.1, Finset.mem_powersetCard.mpr
          ⟨fun x hx => Finset.mem_erase.mpr ⟨fun h => S.2 (h ▸ hx), Finset.mem_univ x⟩, S.1.2⟩⟩
      invFun := fun A =>
        ⟨⟨A.1, (Finset.mem_powersetCard.mp A.2).2⟩,
          fun hk => (Finset.mem_erase.mp ((Finset.mem_powersetCard.mp A.2).1 hk)).1 rfl⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_coe, Finset.card_powersetCard,
    Finset.card_erase_of_mem (Finset.mem_univ k₀), Finset.card_univ, Fintype.card_fin]
  simp

private lemma wedgeMat_factor_of_ne_zero {K : Type*} [Field K] (p : ℕ)
    (w : Fin (2 * p + 1) → K) {k₀ : Fin (2 * p + 1)} (hk₀ : w k₀ ≠ 0) :
    ∃ c : {S : PSub p // k₀ ∉ S.1} → PSub p → K,
      ∀ L S : PSub p, wedgeMat p w L S =
        ∑ S' : {S : PSub p // k₀ ∉ S.1}, wedgeMat p w L S'.1 * c S' S := by
  let T := {S : PSub p // k₀ ∉ S.1}
  let c : T → PSub p → K := fun S' S =>
    if _hk : k₀ ∈ S.1 then
      let S₀ := S.1.erase k₀
      ∑ j ∈ (S₀ᶜ).erase k₀,
        if insert j S₀ = S'.1.1 then
          -(finsetSign S₀ {k₀} : K) * (finsetSign S₀ {j} : K) * (w j * (w k₀)⁻¹)
        else 0
    else
      if S'.1 = S then 1 else 0
  refine ⟨c, fun L S => ?_⟩
  by_cases hk : k₀ ∈ S.1
  · let S₀ := S.1.erase k₀
    have hS₀ : S₀.card + 1 = p := by
      have hcard := Finset.card_erase_add_one hk
      rw [S.2] at hcard
      exact hcard
    have hk₀_mem : k₀ ∈ S₀ᶜ := Finset.mem_compl.mpr (Finset.notMem_erase k₀ S.1)
    have hrel := wedgeMat_col_relation w S₀ hS₀ L
    let g : Fin (2 * p + 1) → K := fun j =>
      if hj : j ∈ S₀ᶜ then
        (finsetSign S₀ {j} : K) * w j *
          wedgeMat p w L ⟨insert j S₀, by
            rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp hj), hS₀]⟩
      else 0
    have hrel' : ∑ j ∈ S₀ᶜ, g j = 0 := by
      rw [← Finset.sum_attach (s := S₀ᶜ) (f := g)]
      refine Eq.trans ?_ hrel
      refine Finset.sum_congr rfl fun j _ => ?_
      have hj := j.2
      simp only [g, hj, ↓reduceDIte]
    rw [← Finset.add_sum_erase _ _ hk₀_mem] at hrel'
    have hS_ins : (⟨insert k₀ S₀, by
        rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp hk₀_mem), hS₀]⟩ : PSub p) = S :=
      Subtype.ext (Finset.insert_erase hk)
    have hgk₀ : g k₀ = (finsetSign S₀ {k₀} : K) * w k₀ * wedgeMat p w L S := by
      simp only [g, hk₀_mem, ↓reduceDIte, hS_ins]
    have hsig_sq : (finsetSign S₀ {k₀} : K) * (finsetSign S₀ {k₀} : K) = 1 := by
      rw [← Int.cast_mul, finsetSign_mul_self, Int.cast_one]
    have hW_eq : wedgeMat p w L S =
        ∑ j ∈ (S₀ᶜ).erase k₀,
          (-(finsetSign S₀ {k₀} : K) * (w k₀)⁻¹) * g j := by
      have h1 : (finsetSign S₀ {k₀} : K) * w k₀ * wedgeMat p w L S =
          -(∑ j ∈ (S₀ᶜ).erase k₀, g j) := by
        rw [← hgk₀]
        exact eq_neg_of_add_eq_zero_left hrel'
      have h2 := congrArg (fun z => ((finsetSign S₀ {k₀} : K) * (w k₀)⁻¹) * z) h1
      have hlhs : ((finsetSign S₀ {k₀} : K) * (w k₀)⁻¹) *
          ((finsetSign S₀ {k₀} : K) * w k₀ * wedgeMat p w L S) = wedgeMat p w L S := by
        calc ((finsetSign S₀ {k₀} : K) * (w k₀)⁻¹) *
              ((finsetSign S₀ {k₀} : K) * w k₀ * wedgeMat p w L S)
            = ((finsetSign S₀ {k₀} : K) * (finsetSign S₀ {k₀} : K)) *
              ((w k₀)⁻¹ * w k₀) * wedgeMat p w L S := by ring
          _ = wedgeMat p w L S := by rw [hsig_sq, inv_mul_cancel₀ hk₀, one_mul, one_mul]
      rw [hlhs, mul_neg, ← neg_mul, Finset.mul_sum] at h2
      simpa [neg_mul] using h2
    rw [hW_eq]
    calc ∑ j ∈ (S₀ᶜ).erase k₀, (-(finsetSign S₀ {k₀} : K) * (w k₀)⁻¹) * g j
        = ∑ j ∈ (S₀ᶜ).erase k₀,
            ∑ S' : T,
              if insert j S₀ = S'.1.1 then
                wedgeMat p w L S'.1 *
                  (-(finsetSign S₀ {k₀} : K) * (finsetSign S₀ {j} : K) * (w j * (w k₀)⁻¹))
              else 0 := by
          refine Finset.sum_congr rfl fun j hj => ?_
          have hj_ne : j ≠ k₀ := (Finset.mem_erase.mp hj).1
          have hj_mem : j ∈ S₀ᶜ := (Finset.mem_erase.mp hj).2
          let SjT : T :=
            ⟨⟨insert j S₀, by
                rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp hj_mem), hS₀]⟩,
              by
                intro hmem
                rcases Finset.mem_insert.mp hmem with rfl | hmem'
                · exact hj_ne rfl
                · exact Finset.notMem_erase k₀ S.1 hmem'⟩
          have hsum_single :
              (∑ S' : T, if insert j S₀ = S'.1.1 then
                  wedgeMat p w L S'.1 *
                    (-(finsetSign S₀ {k₀} : K) * (finsetSign S₀ {j} : K) * (w j * (w k₀)⁻¹))
                else 0) =
              wedgeMat p w L SjT.1 *
                (-(finsetSign S₀ {k₀} : K) * (finsetSign S₀ {j} : K) * (w j * (w k₀)⁻¹)) := by
            rw [Finset.sum_eq_single SjT]
            · simp [SjT]
            · intro S' _ hne
              have hne_val : insert j S₀ ≠ S'.1.1 := fun heq =>
                hne (Subtype.ext (Subtype.ext heq.symm))
              simp only [hne_val, ↓reduceIte]
            · intro habs; exact absurd (Finset.mem_univ SjT) habs
          rw [hsum_single]
          simp only [g, hj_mem, ↓reduceDIte, SjT]
          ring
      _ = ∑ S' : T, wedgeMat p w L S'.1 * c S' S := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun S' _ => ?_
          simp only [c, hk, ↓reduceDIte, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          dsimp only [S₀]
          split_ifs <;> ring
  · let ST : T := ⟨S, hk⟩
    have hsum : ∑ S' : T, wedgeMat p w L S'.1 * c S' S = wedgeMat p w L ST.1 := by
      rw [Finset.sum_eq_single ST]
      · simp [c, hk, ST]
      · intro S' _ hne
        have hne' : S'.1 ≠ S := fun h => hne (Subtype.ext h)
        simp [c, hk, hne']
      · intro habs; exact absurd (Finset.mem_univ ST) habs
    simpa [ST] using hsum.symm

private lemma matrix_rank_mul_le_left_local {K M₁ M₂ N : Type*} [Field K]
    [Fintype M₁] [Fintype M₂] [Fintype N]
    (A : Matrix M₁ N K) (B : Matrix N M₂ K) :
    (A * B).rank ≤ A.rank := by
  have hsub : LinearMap.range (A * B).mulVecLin ≤ LinearMap.range A.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    refine ⟨B.mulVecLin v, ?_⟩
    simp [Matrix.mulVecLin_mul]
  exact Submodule.finrank_mono hsub

private lemma matrix_rank_mul_le_card_inner {K M₁ M₂ N : Type*} [Field K]
    [Fintype M₁] [Fintype M₂] [Fintype N]
    (A : Matrix M₁ N K) (B : Matrix N M₂ K) :
    (A * B).rank ≤ Fintype.card N := by
  have h1 : (A * B).rank ≤ A.rank := matrix_rank_mul_le_left_local A B
  have h2 : A.rank ≤ Module.finrank K (N → K) := LinearMap.finrank_range_le A.mulVecLin
  rw [Module.finrank_pi] at h2
  simpa using le_trans h1 h2

/-- Over every field `K`, `psiFlat p` maps every pure tensor `u ⊗ v ⊗ w` to a matrix of rank at
most `(2p).choose p`. -/
theorem psiFlat_pure_rank_le {K : Type*} [Field K] (p : ℕ)
    (u v : PSub p → K) (w : Fin (2 * p + 1) → K) :
    (psiFlat p (rankOneTensor u v w)).rank ≤ Nat.choose (2 * p) p := by
  by_cases hw : w = 0
  · have hzero : psiFlat p (rankOneTensor u v w) = 0 := by
      ext row col
      simp [psiFlat, rankOneTensor, hw]
    rw [hzero, Matrix.rank_zero]
    exact Nat.zero_le _
  · have hex : ∃ k₀, w k₀ ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hw (funext hall)
    rcases hex with ⟨k₀, hk₀⟩
    obtain ⟨c, hc⟩ := wedgeMat_factor_of_ne_zero p w hk₀
    let T := {S : PSub p // k₀ ∉ S.1}
    let A : Matrix (PSub p × PSub p) T K := fun row S' => v row.1 * wedgeMat p w row.2 S'.1
    let B : Matrix T (PSub p × PSub p) K := fun S' col => u col.2 * c S' col.1
    have hfac : psiFlat p (rankOneTensor u v w) = A * B := by
      ext ⟨J, L⟩ ⟨S, I⟩
      rw [Matrix.mul_apply]
      calc psiFlat p (rankOneTensor u v w) (J, L) (S, I)
          = v J * u I * wedgeMat p w L S := by
              simp only [psiFlat, rankOneTensor, wedgeMat, Finset.mul_sum]
              refine Finset.sum_congr rfl fun k _ => by ring
        _ = v J * u I * ∑ S' : T, wedgeMat p w L S'.1 * c S' S := by rw [hc L S]
        _ = ∑ S' : T, A (J, L) S' * B S' (S, I) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun S' _ => by dsimp [A, B]; ring
    rw [hfac]
    calc (A * B).rank ≤ Fintype.card T := matrix_rank_mul_le_card_inner A B
      _ = Nat.choose (2 * p) p := card_PSub_notMem p k₀

/-- Over every field `K`, `psiFlat_pm p m` maps every pure tensor `u ⊗ v ⊗ w` to a matrix of rank
at most `(2p).choose p` (independent of `m`). -/
theorem psiFlat_pm_pure_rank_le {K : Type*} [Field K] (p m : ℕ)
    (u v : Fin m × PSub p → K) (w : Fin (2 * p + 1) → K) :
    (psiFlat_pm p m (rankOneTensor u v w)).rank ≤ Nat.choose (2 * p) p := by
  by_cases hw : w = 0
  · have hzero : psiFlat_pm p m (rankOneTensor u v w) = 0 := by
      ext row col
      simp [psiFlat_pm, psiFlat, rankOneTensor, hw]
    rw [hzero, Matrix.rank_zero]
    exact Nat.zero_le _
  · have hex : ∃ k₀, w k₀ ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hw (funext hall)
    rcases hex with ⟨k₀, hk₀⟩
    obtain ⟨c, hc⟩ := wedgeMat_factor_of_ne_zero p w hk₀
    let T := {S : PSub p // k₀ ∉ S.1}
    let A : Matrix (Fin m × PSub p × PSub p) T K :=
      fun row S' => v (row.1, row.2.1) * wedgeMat p w row.2.2 S'.1
    let B : Matrix T (Fin m × PSub p × PSub p) K :=
      fun S' col => u (col.1, col.2.2) * c S' col.2.1
    have hfac : psiFlat_pm p m (rankOneTensor u v w) = A * B := by
      ext ⟨a, J, L⟩ ⟨b, S, I⟩
      rw [Matrix.mul_apply]
      calc psiFlat_pm p m (rankOneTensor u v w) (a, J, L) (b, S, I)
          = v (a, J) * u (b, I) * wedgeMat p w L S := by
              simp only [psiFlat_pm, psiFlat, rankOneTensor, wedgeMat, Finset.mul_sum]
              refine Finset.sum_congr rfl fun k _ => by ring
        _ = v (a, J) * u (b, I) * ∑ S' : T, wedgeMat p w L S'.1 * c S' S := by rw [hc L S]
        _ = ∑ S' : T, A (a, J, L) S' * B S' (b, S, I) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun S' _ => by dsimp [A, B]; ring
    rw [hfac]
    calc (A * B).rank ≤ Fintype.card T := matrix_rank_mul_le_card_inner A B
      _ = Nat.choose (2 * p) p := card_PSub_notMem p k₀

/-! ## Section 3: Odd-Graph / Kneser Disjointness Matrix and Explicit Inverse (Lemma 11) -/

/-- The odd-graph / Kneser disjointness matrix `B_q` on `q`-subsets of `V`:
`(B_q)_{C, D} = 1` if `Disjoint C D` and `0` otherwise. At `q = 0`, `B_0 = [1]`. -/
def kneserMat (R : Type*) [CommRing R] {V : Type*} [DecidableEq V] (q : ℕ) :
    Matrix (QSub V q) (QSub V q) R :=
  fun C D => if Disjoint C.1 D.1 then 1 else 0

/-- Integral scaled inverse `(q + 1)! · B_q⁻¹` with `(C, D)` entry
`(-1)^h · h! · (q - h)!`, where `h = |C ∩ D|`. -/
def kneserAdjMat (R : Type*) [CommRing R] {V : Type*} [DecidableEq V] (q : ℕ) :
    Matrix (QSub V q) (QSub V q) R :=
  fun C D =>
    let h := (C.1 ∩ D.1).card
    (-1 : R) ^ h * ((h.factorial * (q - h).factorial : ℕ) : R)

/-- Explicit Kneser inverse `B_q⁻¹` over a field `K` (Lemma 11):
`(B_q⁻¹)_{C, D} = (-1)^h / ((q + 1) · C(q, h))`, where `h = |C ∩ D|`. -/
def kneserInv (K : Type*) [Field K] {V : Type*} [DecidableEq V] (q : ℕ) :
    Matrix (QSub V q) (QSub V q) K :=
  fun C D =>
    let h := (C.1 ∩ D.1).card
    (-1 : K) ^ h * (((q + 1 : K) * (Nat.choose q h : K))⁻¹)

lemma kneserMat_transpose (R : Type*) [CommRing R] {V : Type*} [DecidableEq V] (q : ℕ) :
    (kneserMat R (V := V) q).transpose = kneserMat R (V := V) q := by
  ext C D
  simp [kneserMat, disjoint_comm]

lemma kneserAdjMat_transpose (R : Type*) [CommRing R] {V : Type*} [DecidableEq V] (q : ℕ) :
    (kneserAdjMat R (V := V) q).transpose = kneserAdjMat R (V := V) q := by
  ext C D
  simp [kneserAdjMat, Finset.inter_comm]

/-- **Universal integral Kneser inverse identity (Lemma 11 over `ℤ` / any `CommRing`):**
For any finite type `V` with `|V| = 2q + 1` (including `q = 0`, where `B_0 = [1]`),
`B_q * kneserAdjMat = (q + 1)! • 1` and `kneserAdjMat * B_q = (q + 1)! • 1`. -/
theorem kneserMat_mul_adj (R : Type*) [CommRing R] {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} (hV : Fintype.card V = 2 * q + 1) :
    kneserMat R (V := V) q * kneserAdjMat R (V := V) q = ((q + 1).factorial : R) • 1 ∧
    kneserAdjMat R (V := V) q * kneserMat R (V := V) q = ((q + 1).factorial : R) • 1 := by
  have hmul : kneserMat R (V := V) q * kneserAdjMat R (V := V) q =
      ((q + 1).factorial : R) • 1 := by
    ext C E
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
    have hCc_card : C.1ᶜ.card = q + 1 := by
      rw [Finset.card_compl, C.2, hV]
      omega
    have hsum_filter :
        ∑ D : QSub V q, kneserMat R (V := V) q C D * kneserAdjMat R (V := V) q D E =
        ∑ D ∈ Finset.univ.filter (fun D : QSub V q => Disjoint C.1 D.1),
          kneserAdjMat R (V := V) q D E := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun D _ => ?_
      simp [kneserMat]
    rw [hsum_filter]
    let term : V → R := fun x =>
      let h := ((C.1ᶜ.erase x) ∩ E.1).card
      (-1 : R) ^ h * ((h.factorial * (q - h).factorial : ℕ) : R)
    have hbij :
        (∑ D ∈ Finset.univ.filter (fun D : QSub V q => Disjoint C.1 D.1),
          kneserAdjMat R (V := V) q D E) = ∑ x ∈ C.1ᶜ, term x := by
      symm
      refine Finset.sum_bij
        (fun x hx => ⟨C.1ᶜ.erase x, by
          rw [Finset.card_erase_of_mem hx, hCc_card]; omega⟩) ?_ ?_ ?_ ?_
      · intro x _
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact Finset.disjoint_left.mpr fun z hzC hzE =>
          (Finset.mem_compl.mp (Finset.erase_subset x C.1ᶜ hzE)) hzC
      · intro x _ y hy hxy
        have heq : C.1ᶜ.erase x = C.1ᶜ.erase y := congrArg Subtype.val hxy
        by_contra hne
        have hy_mem : y ∈ C.1ᶜ.erase x := Finset.mem_erase.mpr ⟨Ne.symm hne, hy⟩
        rw [heq] at hy_mem
        exact Finset.notMem_erase y C.1ᶜ hy_mem
      · intro D hD
        have hdisj : Disjoint C.1 D.1 := (Finset.mem_filter.mp hD).2
        have hsub : D.1 ⊆ C.1ᶜ := Finset.subset_compl_iff_disjoint_left.mpr hdisj
        have hsdiff_card : (C.1ᶜ \ D.1).card = 1 := by
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hCc_card, D.2]
          omega
        rcases Finset.card_eq_one.mp hsdiff_card with ⟨x, hx⟩
        have hx_in : x ∈ C.1ᶜ \ D.1 := hx ▸ Finset.mem_singleton_self x
        have hx_Cc : x ∈ C.1ᶜ := (Finset.mem_sdiff.mp hx_in).1
        refine ⟨x, hx_Cc, Subtype.ext ?_⟩
        ext z
        simp only [Finset.mem_erase]
        constructor
        · rintro ⟨hzx, hzCc⟩
          by_contra hzD
          have hz_sdiff : z ∈ C.1ᶜ \ D.1 := Finset.mem_sdiff.mpr ⟨hzCc, hzD⟩
          rw [hx, Finset.mem_singleton] at hz_sdiff
          exact hzx hz_sdiff
        · intro hzD
          refine ⟨?_, hsub hzD⟩
          intro hzx
          subst hzx
          exact (Finset.mem_sdiff.mp hx_in).2 hzD
      · intro _ _
        rfl
    rw [hbij]
    have hsplit : C.1ᶜ = (E.1 \ C.1) ∪ (C.1ᶜ \ E.1) := by
      ext z
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_compl]
      tauto
    have hdisj_split : Disjoint (E.1 \ C.1) (C.1ᶜ \ E.1) := by
      refine Finset.disjoint_left.mpr fun z h1 h2 => ?_
      exact (Finset.mem_sdiff.mp h2).2 (Finset.mem_sdiff.mp h1).1
    have hcard_union : (E.1 \ C.1).card + (C.1ᶜ \ E.1).card = q + 1 := by
      rw [← Finset.card_union_of_disjoint hdisj_split, ← hsplit, hCc_card]
    let m := (E.1 \ C.1).card
    have hm_le : m ≤ q := by
      calc m ≤ E.1.card := Finset.card_le_card Finset.sdiff_subset
        _ = q := E.2
    rw [hsplit, Finset.sum_union hdisj_split]
    have hpart1 : (∑ x ∈ E.1 \ C.1, term x) =
        (m : R) * ((-1 : R) ^ (m - 1) * (((m - 1).factorial * (q - (m - 1)).factorial : ℕ) : R)) := by
      have hterm : ∀ x ∈ E.1 \ C.1, ((C.1ᶜ.erase x) ∩ E.1).card = m - 1 := by
        intro x hx
        have heq : (C.1ᶜ.erase x) ∩ E.1 = (E.1 \ C.1).erase x := by
          ext z
          simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_compl, Finset.mem_sdiff]
          tauto
        rw [heq, Finset.card_erase_of_mem hx]
      calc ∑ x ∈ E.1 \ C.1, term x
          = ∑ _x ∈ E.1 \ C.1,
              (-1 : R) ^ (m - 1) * (((m - 1).factorial * (q - (m - 1)).factorial : ℕ) : R) := by
              refine Finset.sum_congr rfl fun x hx => ?_
              simp only [term, hterm x hx]
        _ = (m : R) * ((-1 : R) ^ (m - 1) *
              (((m - 1).factorial * (q - (m - 1)).factorial : ℕ) : R)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
    have hpart2 : (∑ x ∈ C.1ᶜ \ E.1, term x) =
        ((q + 1 - m : ℕ) : R) * ((-1 : R) ^ m * ((m.factorial * (q - m).factorial : ℕ) : R)) := by
      have hterm : ∀ x ∈ C.1ᶜ \ E.1, ((C.1ᶜ.erase x) ∩ E.1).card = m := by
        intro x hx
        have hxE : x ∉ E.1 := (Finset.mem_sdiff.mp hx).2
        have heq : (C.1ᶜ.erase x) ∩ E.1 = E.1 \ C.1 := by
          ext z
          simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_compl, Finset.mem_sdiff]
          constructor
          · rintro ⟨⟨_, hzC⟩, hzE⟩; exact ⟨hzE, hzC⟩
          · rintro ⟨hzE, hzC⟩; exact ⟨⟨fun hzx => hxE (hzx ▸ hzE), hzC⟩, hzE⟩
        rw [heq]
      have hcard2 : (C.1ᶜ \ E.1).card = q + 1 - m := by omega
      calc ∑ x ∈ C.1ᶜ \ E.1, term x
          = ∑ _x ∈ C.1ᶜ \ E.1,
              (-1 : R) ^ m * ((m.factorial * (q - m).factorial : ℕ) : R) := by
              refine Finset.sum_congr rfl fun x hx => ?_
              simp only [term, hterm x hx]
        _ = ((q + 1 - m : ℕ) : R) *
              ((-1 : R) ^ m * ((m.factorial * (q - m).factorial : ℕ) : R)) := by
              rw [Finset.sum_const, hcard2, nsmul_eq_mul]
    rw [hpart1, hpart2]
    by_cases hCE : C = E
    · subst hCE
      have hm0 : m = 0 := by simp [m]
      simp only [hm0, ↓reduceIte, Nat.cast_zero, zero_mul, zero_add, Nat.sub_zero, pow_zero,
        one_mul, Nat.factorial_zero, smul_eq_mul, mul_one]
      have hnat := (Nat.factorial_succ q).symm
      have hR := congrArg (Nat.cast (R := R)) hnat
      push_cast at hR
      simpa using hR
    · simp only [hCE, ↓reduceIte, smul_zero]
      have hm_pos : 1 ≤ m := by
        by_contra hlt
        have hm0 : m = 0 := by omega
        have hsdiff_empty : E.1 \ C.1 = ∅ := Finset.card_eq_zero.mp hm0
        have hsub : E.1 ⊆ C.1 := Finset.sdiff_eq_empty_iff_subset.mp hsdiff_empty
        have heq_set : E.1 = C.1 := Finset.eq_of_subset_of_card_le hsub (by rw [C.2, E.2])
        exact hCE (Subtype.ext heq_set.symm)
      set r := m - 1
      have hm_eq : m = r + 1 := by omega
      rw [hm_eq]
      have hfac1 : (r + 1) * (r.factorial * (q - r).factorial) =
          (r + 1).factorial * (q - r).factorial := by
        rw [Nat.factorial_succ]
        ring
      have hfac2 : (q + 1 - (r + 1)) * ((r + 1).factorial * (q - (r + 1)).factorial) =
          (r + 1).factorial * (q - r).factorial := by
        have h1 : q + 1 - (r + 1) = (q - (r + 1)) + 1 := by omega
        have h2 : q - r = (q - (r + 1)) + 1 := by omega
        rw [h1, h2, Nat.factorial_succ (q - (r + 1))]
        ring
      have h1R : ((r + 1 : ℕ) : R) * (((r.factorial * (q - r).factorial : ℕ) : R)) =
          (((r + 1).factorial * (q - r).factorial : ℕ) : R) := by
        have h := congrArg (Nat.cast (R := R)) hfac1
        simpa [Nat.cast_mul] using h
      have h2R : ((q + 1 - (r + 1) : ℕ) : R) *
            ((((r + 1).factorial * (q - (r + 1)).factorial : ℕ) : R)) =
          (((r + 1).factorial * (q - r).factorial : ℕ) : R) := by
        have h := congrArg (Nat.cast (R := R)) hfac2
        simpa [Nat.cast_mul] using h
      calc ((r + 1 : ℕ) : R) * ((-1 : R) ^ r * ((r.factorial * (q - r).factorial : ℕ) : R)) +
            ((q + 1 - (r + 1) : ℕ) : R) *
              ((-1 : R) ^ (r + 1) * (((r + 1).factorial * (q - (r + 1)).factorial : ℕ) : R))
          = (-1 : R) ^ r * (((r + 1 : ℕ) : R) * ((r.factorial * (q - r).factorial : ℕ) : R)) +
            (-(-1 : R) ^ r) *
              (((q + 1 - (r + 1) : ℕ) : R) *
                (((r + 1).factorial * (q - (r + 1)).factorial : ℕ) : R)) := by
              rw [pow_succ]; ring
        _ = 0 := by rw [h1R, h2R]; ring
  refine ⟨hmul, ?_⟩
  have htr := congrArg Matrix.transpose hmul
  simpa [Matrix.transpose_mul, kneserMat_transpose, kneserAdjMat_transpose] using htr

lemma factorial_cast_ne_zero {K : Type*} [Field K] {n : ℕ}
    (hunit : ∀ j : ℕ, 1 ≤ j → j ≤ n → (j : K) ≠ 0) :
    ((n.factorial : ℕ) : K) ≠ 0 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.factorial_succ, Nat.cast_mul]
    exact mul_ne_zero (hunit (k + 1) (by omega) (le_refl _))
      (ih fun j h1 h2 => hunit j h1 (by omega))

lemma kneserInv_eq_smul_adj {K : Type*} [Field K] {V : Type*} [DecidableEq V] {q : ℕ}
    (hunit : ∀ j : ℕ, 1 ≤ j → j ≤ q + 1 → (j : K) ≠ 0) :
    kneserInv K (V := V) q = (((q + 1).factorial : K)⁻¹) • kneserAdjMat K (V := V) q := by
  have hfac_ne : (((q + 1).factorial : ℕ) : K) ≠ 0 := factorial_cast_ne_zero hunit
  ext C D
  simp only [kneserInv, kneserAdjMat, Matrix.smul_apply, smul_eq_mul]
  set h := (C.1 ∩ D.1).card
  have hle : h ≤ q := le_trans (Finset.card_le_card Finset.inter_subset_left) C.2.le
  have hnat : (q + 1) * Nat.choose q h * (h.factorial * (q - h).factorial) = (q + 1).factorial := by
    rw [Nat.factorial_succ]
    have hc := Nat.choose_mul_factorial_mul_factorial hle
    calc (q + 1) * Nat.choose q h * (h.factorial * (q - h).factorial)
        = (q + 1) * (Nat.choose q h * h.factorial * (q - h).factorial) := by ring
      _ = (q + 1) * q.factorial := by rw [hc]
  have hK : ((q + 1 : K) * (Nat.choose q h : K)) * ((h.factorial * (q - h).factorial : ℕ) : K) =
      (((q + 1).factorial : ℕ) : K) := by
    have h' := congrArg (Nat.cast (R := K)) hnat
    simpa [Nat.cast_mul, Nat.cast_add] using h'
  have hden_ne : (q + 1 : K) * (Nat.choose q h : K) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hK
    exact hfac_ne hK.symm
  have hinv_eq : (((q + 1 : K) * (Nat.choose q h : K))⁻¹) =
      (((q + 1).factorial : ℕ) : K)⁻¹ * ((h.factorial * (q - h).factorial : ℕ) : K) := by
    apply mul_left_cancel₀ hden_ne
    rw [mul_inv_cancel₀ hden_ne]
    symm
    calc ((q + 1 : K) * (Nat.choose q h : K)) *
          ((((q + 1).factorial : ℕ) : K)⁻¹ * ((h.factorial * (q - h).factorial : ℕ) : K))
        = (((q + 1).factorial : ℕ) : K)⁻¹ *
          (((q + 1 : K) * (Nat.choose q h : K)) * ((h.factorial * (q - h).factorial : ℕ) : K)) := by
            ring
      _ = (((q + 1).factorial : ℕ) : K)⁻¹ * (((q + 1).factorial : ℕ) : K) := by rw [hK]
      _ = 1 := inv_mul_cancel₀ hfac_ne
  rw [hinv_eq]
  ring

/-- **Lemma 11 (`kneserMat_mul_inv`):** Over any field `K` in which `1, …, q + 1` are nonzero,
the odd-graph / Kneser disjointness matrix `B_q` on `q`-subsets of a `(2q + 1)`-element set
(including `q = 0`, where `B_0 = [1]`) has explicit two-sided inverse `kneserInv K q`. -/
theorem kneserMat_mul_inv (K : Type*) [Field K] {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} (hV : Fintype.card V = 2 * q + 1)
    (hunit : ∀ j : ℕ, 1 ≤ j → j ≤ q + 1 → (j : K) ≠ 0) :
    kneserMat K (V := V) q * kneserInv K (V := V) q = 1 ∧
    kneserInv K (V := V) q * kneserMat K (V := V) q = 1 := by
  have hfac_ne : (((q + 1).factorial : ℕ) : K) ≠ 0 := factorial_cast_ne_zero hunit
  rcases kneserMat_mul_adj K (V := V) hV with ⟨hl, hr⟩
  rw [kneserInv_eq_smul_adj hunit]
  constructor
  · rw [Matrix.mul_smul, hl, smul_smul, inv_mul_cancel₀ hfac_ne, one_smul]
  · rw [Matrix.smul_mul, hr, smul_smul, inv_mul_cancel₀ hfac_ne, one_smul]

/-! ## Section 4: Signed Kneser Blocks (Lemma 10), Explicit Inverse (Corollary 12), and Trace (Proposition 13) -/

/-- Diagonal sign `d(A, B) = finsetSign ((A \ B) ∪ (B \ A)) (A ∩ B) ∈ {±1}` conjugating
`psiFlat p (Omega_p K p)` into signed Kneser blocks. -/
def pairDiagSign {p : ℕ} (A B : PSub p) : ℤ :=
  finsetSign ((A.1 \ B.1) ∪ (B.1 \ A.1)) (A.1 ∩ B.1)

lemma pairDiagSign_mul_self {p : ℕ} (A B : PSub p) :
    pairDiagSign A B * pairDiagSign A B = 1 :=
  finsetSign_mul_self _ _

/-- Diagonal `±1` matrix `D` with `(A, B)` diagonal entry `pairDiagSign A B`. -/
def diagSignMat (K : Type*) [CommRing K] (p : ℕ) :
    Matrix (PSub p × PSub p) (PSub p × PSub p) K :=
  Matrix.diagonal fun ab => (pairDiagSign ab.1 ab.2 : K)

lemma diagSignMat_mul_self (K : Type*) [CommRing K] (p : ℕ) :
    diagSignMat K p * diagSignMat K p = 1 := by
  ext a b
  simp only [diagSignMat, Matrix.mul_diagonal, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs with h
  · subst h
    rw [← Int.cast_mul, pairDiagSign_mul_self, Int.cast_one]
  · simp

private lemma exteriorSign_pair_invariants {p : ℕ} {I J S L : PSub p} {k : Fin (2 * p + 1)}
    (hIJ : Disjoint I.1 J.1 ∧ k ∉ I.1 ∧ k ∉ J.1)
    (hSL : Disjoint S.1 L.1 ∧ k ∉ S.1 ∧ k ∉ L.1) :
    J.1 \ L.1 = S.1 \ I.1 ∧
    L.1 \ J.1 = I.1 \ S.1 ∧
    Disjoint (J.1 ∩ L.1) (S.1 ∩ I.1) ∧
    exteriorSign p I J k * exteriorSign p S L k =
      (-1 : ℤ) ^ (J.1 \ L.1).card * pairDiagSign J L * pairDiagSign S I := by
  have hpartIJ : I.1 ∪ J.1 = Finset.univ.erase k := exteriorSign_partition hIJ
  have hpartSL : S.1 ∪ L.1 = Finset.univ.erase k := exteriorSign_partition hSL
  have hunion_eq : I.1 ∪ J.1 = S.1 ∪ L.1 := hpartIJ.trans hpartSL.symm
  have hmemIJ : ∀ x : Fin (2 * p + 1), x ≠ k → (x ∈ I.1 ↔ x ∉ J.1) := by
    intro x hxk
    have hmem : x ∈ I.1 ∪ J.1 := by
      rw [hpartIJ]; exact Finset.mem_erase.mpr ⟨hxk, Finset.mem_univ x⟩
    constructor
    · intro hxI hxJ; exact Finset.disjoint_left.mp hIJ.1 hxI hxJ
    · intro hxJ; rcases Finset.mem_union.mp hmem with h | h; exact h; exact absurd h hxJ
  have hmemSL : ∀ x : Fin (2 * p + 1), x ≠ k → (x ∈ S.1 ↔ x ∉ L.1) := by
    intro x hxk
    have hmem : x ∈ S.1 ∪ L.1 := by
      rw [hpartSL]; exact Finset.mem_erase.mpr ⟨hxk, Finset.mem_univ x⟩
    constructor
    · intro hxS hxL; exact Finset.disjoint_left.mp hSL.1 hxS hxL
    · intro hxL; rcases Finset.mem_union.mp hmem with h | h; exact h; exact absurd h hxL
  have hP_eq : J.1 \ L.1 = S.1 \ I.1 := by
    ext x
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨hxJ, hxL⟩
      have hxk : x ≠ k := fun h => hIJ.2.2 (h ▸ hxJ)
      exact ⟨(hmemSL x hxk).mpr hxL, fun hxI => (hmemIJ x hxk).mp hxI hxJ⟩
    · rintro ⟨hxS, hxI⟩
      have hxk : x ≠ k := fun h => hSL.2.1 (h ▸ hxS)
      exact ⟨by_contra fun hxJ => hxI ((hmemIJ x hxk).mpr hxJ), (hmemSL x hxk).mp hxS⟩
  have hQ_eq : L.1 \ J.1 = I.1 \ S.1 := by
    ext x
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨hxL, hxJ⟩
      have hxk : x ≠ k := fun h => hSL.2.2 (h ▸ hxL)
      exact ⟨(hmemIJ x hxk).mpr hxJ, fun hxS => (hmemSL x hxk).mp hxS hxL⟩
    · rintro ⟨hxI, hxS⟩
      have hxk : x ≠ k := fun h => hIJ.2.1 (h ▸ hxI)
      exact ⟨by_contra fun hxL => hxS ((hmemSL x hxk).mpr hxL), (hmemIJ x hxk).mp hxI⟩
  have hCD_disj : Disjoint (J.1 ∩ L.1) (S.1 ∩ I.1) := by
    refine Finset.disjoint_left.mpr fun x h1 h2 => ?_
    exact Finset.disjoint_left.mp hIJ.1 (Finset.mem_inter.mp h2).2 (Finset.mem_inter.mp h1).1
  refine ⟨hP_eq, hQ_eq, hCD_disj, ?_⟩
  let P := J.1 \ L.1
  let Q := L.1 \ J.1
  let C := J.1 ∩ L.1
  let D := S.1 ∩ I.1
  have hPQ : Disjoint P Q := by
    refine Finset.disjoint_left.mpr fun x h1 h2 => ?_
    exact (Finset.mem_sdiff.mp h1).2 (Finset.mem_sdiff.mp h2).1
  have hPC : Disjoint P C := by
    refine Finset.disjoint_left.mpr fun x h1 h2 => ?_
    exact (Finset.mem_sdiff.mp h1).2 (Finset.mem_inter.mp h2).2
  have hQC : Disjoint Q C := by
    refine Finset.disjoint_left.mpr fun x h1 h2 => ?_
    exact (Finset.mem_sdiff.mp h1).2 (Finset.mem_inter.mp h2).1
  have hPD : Disjoint P D := by
    refine Finset.disjoint_left.mpr fun x h1 h2 => ?_
    change x ∈ J.1 \ L.1 at h1
    rw [hP_eq] at h1
    exact (Finset.mem_sdiff.mp h1).2 (Finset.mem_inter.mp h2).2
  have hQD : Disjoint Q D := by
    refine Finset.disjoint_left.mpr fun x h1 h2 => ?_
    change x ∈ L.1 \ J.1 at h1
    rw [hQ_eq] at h1
    exact (Finset.mem_sdiff.mp h1).2 (Finset.mem_inter.mp h2).1
  have hJ_eq : J.1 = P ∪ C := (Finset.sdiff_union_inter J.1 L.1).symm
  have hL_eq : L.1 = Q ∪ C := by
    dsimp only [Q, C]
    rw [Finset.inter_comm J.1 L.1]
    exact (Finset.sdiff_union_inter L.1 J.1).symm
  have hS_eq : S.1 = P ∪ D := by
    dsimp only [P, D]
    rw [hP_eq]
    exact (Finset.sdiff_union_inter S.1 I.1).symm
  have hI_eq : I.1 = Q ∪ D := by
    dsimp only [Q, D]
    rw [hQ_eq, Finset.inter_comm S.1 I.1]
    exact (Finset.sdiff_union_inter I.1 S.1).symm
  have hP_card_eq_Q : P.card = Q.card := by
    have h1 : P.card + C.card = p := by
      have := Finset.card_sdiff_add_card_inter J.1 L.1
      rw [J.2] at this; exact this
    have h2 : Q.card + C.card = p := by
      have := Finset.card_sdiff_add_card_inter L.1 J.1
      rw [Finset.inter_comm, L.2] at this; exact this
    omega
  have hPQ_D : Disjoint (P ∪ Q) D := Finset.disjoint_union_left.mpr ⟨hPD, hQD⟩
  have hDPQ_even : Even ((P ∪ Q).card * D.card) := by
    rw [Finset.card_union_of_disjoint hPQ, ← hP_card_eq_Q]
    exact ⟨P.card * D.card, by ring⟩
  have hD_PQ : finsetSign D (P ∪ Q) = finsetSign (P ∪ Q) D := by
    rw [finsetSign_swap hPQ_D, hDPQ_even.neg_one_pow, one_mul]
  have hpair_JL : pairDiagSign J L = finsetSign P C * finsetSign Q C := by
    unfold pairDiagSign
    exact finsetSign_union_left hPQ
  have hpair_SI : pairDiagSign S I = finsetSign D P * finsetSign D Q := by
    unfold pairDiagSign
    rw [← hP_eq, ← hQ_eq, ← hD_PQ, finsetSign_union_right hPQ]
  rw [exteriorSign, exteriorSign, ite_eq_left_of_eq_true _ _ (eq_true hIJ),
    ite_eq_left_of_eq_true _ _ (eq_true hSL), hunion_eq]
  have hksq : finsetSign (S.1 ∪ L.1) {k} * finsetSign (S.1 ∪ L.1) {k} = 1 :=
    finsetSign_mul_self _ _
  have hIJ_sign : finsetSign I.1 J.1 =
      finsetSign Q P * finsetSign Q C * finsetSign D P * finsetSign D C := by
    rw [hI_eq, hJ_eq, finsetSign_union_left hQD, finsetSign_union_right hPC,
      finsetSign_union_right hPC]
    ring
  have hSL_sign : finsetSign S.1 L.1 =
      finsetSign P Q * finsetSign P C * finsetSign D Q * finsetSign D C := by
    rw [hS_eq, hL_eq, finsetSign_union_left hPD, finsetSign_union_right hQC,
      finsetSign_union_right hQC]
    ring
  have hPQ_comm : finsetSign Q P * finsetSign P Q = (-1 : ℤ) ^ P.card := by
    rw [mul_comm, finsetSign_comm hPQ, ← hP_card_eq_Q, neg_one_pow_mul_self]
  have hDC_sq : finsetSign D C * finsetSign D C = 1 := finsetSign_mul_self D C
  calc (finsetSign I.1 J.1 * finsetSign (S.1 ∪ L.1) {k}) *
        (finsetSign S.1 L.1 * finsetSign (S.1 ∪ L.1) {k})
      = (finsetSign I.1 J.1 * finsetSign S.1 L.1) *
        (finsetSign (S.1 ∪ L.1) {k} * finsetSign (S.1 ∪ L.1) {k}) := by ring
    _ = finsetSign I.1 J.1 * finsetSign S.1 L.1 := by rw [hksq, mul_one]
    _ = (finsetSign Q P * finsetSign P Q) *
        (finsetSign P C * finsetSign Q C) *
        (finsetSign D P * finsetSign D Q) *
        (finsetSign D C * finsetSign D C) := by
          rw [hIJ_sign, hSL_sign]; ring
    _ = (-1 : ℤ) ^ P.card * pairDiagSign J L * pairDiagSign S I := by
          rw [hPQ_comm, hDC_sq, ← hpair_JL, ← hpair_SI, mul_one]

/-- Entrywise formula for `psiFlat p (Omega_p K p)` (Lemma 10): nonzero iff
`J \ L = S \ I`, `L \ J = I \ S`, and `Disjoint (J ∩ L) (S ∩ I)`, in which case it equals
`(-1)^{|J \ L|} · d(J, L) · d(S, I)`. -/
theorem psiFlat_Omega_apply {K : Type*} [CommRing K] (p : ℕ) (J L S I : PSub p) :
    psiFlat p (Omega_p K p) (J, L) (S, I) =
      if J.1 \ L.1 = S.1 \ I.1 ∧ L.1 \ J.1 = I.1 \ S.1 ∧ Disjoint (J.1 ∩ L.1) (S.1 ∩ I.1) then
        ((-1 : ℤ) ^ (J.1 \ L.1).card * pairDiagSign J L * pairDiagSign S I : K)
      else 0 := by
  unfold psiFlat Omega_p
  by_cases hcond :
      J.1 \ L.1 = S.1 \ I.1 ∧ L.1 \ J.1 = I.1 \ S.1 ∧ Disjoint (J.1 ∩ L.1) (S.1 ∩ I.1)
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hcond)]
    rcases hcond with ⟨hP, hQ, hCD⟩
    have hdisjIJ : Disjoint I.1 J.1 := by
      refine Finset.disjoint_left.mpr fun x hxI hxJ => ?_
      by_cases hxS : x ∈ S.1
      · have hxD : x ∈ S.1 ∩ I.1 := Finset.mem_inter.mpr ⟨hxS, hxI⟩
        by_cases hxL : x ∈ L.1
        · exact Finset.disjoint_left.mp hCD (Finset.mem_inter.mpr ⟨hxJ, hxL⟩) hxD
        · have hxP : x ∈ J.1 \ L.1 := Finset.mem_sdiff.mpr ⟨hxJ, hxL⟩
          rw [hP] at hxP
          exact (Finset.mem_sdiff.mp hxP).2 hxI
      · have hxQ : x ∈ I.1 \ S.1 := Finset.mem_sdiff.mpr ⟨hxI, hxS⟩
        rw [← hQ] at hxQ
        exact (Finset.mem_sdiff.mp hxQ).2 hxJ
    have hdisjSL : Disjoint S.1 L.1 := by
      refine Finset.disjoint_left.mpr fun x hxS hxL => ?_
      by_cases hxI : x ∈ I.1
      · have hxD : x ∈ S.1 ∩ I.1 := Finset.mem_inter.mpr ⟨hxS, hxI⟩
        by_cases hxJ : x ∈ J.1
        · exact Finset.disjoint_left.mp hCD (Finset.mem_inter.mpr ⟨hxJ, hxL⟩) hxD
        · have hxQ : x ∈ L.1 \ J.1 := Finset.mem_sdiff.mpr ⟨hxL, hxJ⟩
          rw [hQ] at hxQ
          exact (Finset.mem_sdiff.mp hxQ).2 hxS
      · have hxP : x ∈ S.1 \ I.1 := Finset.mem_sdiff.mpr ⟨hxS, hxI⟩
        rw [← hP] at hxP
        exact (Finset.mem_sdiff.mp hxP).2 hxL
    have hunion_eq : I.1 ∪ J.1 = S.1 ∪ L.1 := by
      ext x
      simp only [Finset.mem_union]
      constructor
      · rintro (hxI | hxJ)
        · by_cases hxS : x ∈ S.1
          · exact Or.inl hxS
          · have hxQ : x ∈ I.1 \ S.1 := Finset.mem_sdiff.mpr ⟨hxI, hxS⟩
            rw [← hQ] at hxQ
            exact Or.inr (Finset.mem_sdiff.mp hxQ).1
        · by_cases hxL : x ∈ L.1
          · exact Or.inr hxL
          · have hxP : x ∈ J.1 \ L.1 := Finset.mem_sdiff.mpr ⟨hxJ, hxL⟩
            rw [hP] at hxP
            exact Or.inl (Finset.mem_sdiff.mp hxP).1
      · rintro (hxS | hxL)
        · by_cases hxI : x ∈ I.1
          · exact Or.inl hxI
          · have hxP : x ∈ S.1 \ I.1 := Finset.mem_sdiff.mpr ⟨hxS, hxI⟩
            rw [← hP] at hxP
            exact Or.inr (Finset.mem_sdiff.mp hxP).1
        · by_cases hxJ : x ∈ J.1
          · exact Or.inr hxJ
          · have hxQ : x ∈ L.1 \ J.1 := Finset.mem_sdiff.mpr ⟨hxL, hxJ⟩
            rw [hQ] at hxQ
            exact Or.inl (Finset.mem_sdiff.mp hxQ).1
    have hcompl_card : (I.1 ∪ J.1)ᶜ.card = 1 := by
      rw [Finset.card_compl, Finset.card_union_of_disjoint hdisjIJ, I.2, J.2, Fintype.card_fin]
      omega
    rcases Finset.card_eq_one.mp hcompl_card with ⟨k₀, hk₀⟩
    have hk₀_not : k₀ ∉ I.1 ∪ J.1 := by
      have hmem : k₀ ∈ (I.1 ∪ J.1)ᶜ := hk₀ ▸ Finset.mem_singleton_self k₀
      exact Finset.mem_compl.mp hmem
    have hIJ₀ : Disjoint I.1 J.1 ∧ k₀ ∉ I.1 ∧ k₀ ∉ J.1 := by
      rw [Finset.mem_union, not_or] at hk₀_not
      exact ⟨hdisjIJ, hk₀_not.1, hk₀_not.2⟩
    have hSL₀ : Disjoint S.1 L.1 ∧ k₀ ∉ S.1 ∧ k₀ ∉ L.1 := by
      have hk₀_not' : k₀ ∉ S.1 ∪ L.1 := hunion_eq ▸ hk₀_not
      rw [Finset.mem_union, not_or] at hk₀_not'
      exact ⟨hdisjSL, hk₀_not'.1, hk₀_not'.2⟩
    rw [Finset.sum_eq_single k₀]
    · have hsign := (exteriorSign_pair_invariants hIJ₀ hSL₀).2.2.2
      have hK := congrArg (Int.cast (R := K)) hsign
      simpa [Int.cast_mul] using hK
    · intro k _ hkne
      have hk_in : k ∈ I.1 ∪ J.1 := by
        by_contra hnot
        have hmem : k ∈ (I.1 ∪ J.1)ᶜ := Finset.mem_compl.mpr hnot
        rw [hk₀, Finset.mem_singleton] at hmem
        exact hkne hmem
      have hzero : exteriorSign p I J k = 0 := by
        rcases Finset.mem_union.mp hk_in with h | h <;> simp [exteriorSign, h]
      simp [hzero]
    · intro habs; exact absurd (Finset.mem_univ k₀) habs
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hcond)]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hIJ : Disjoint I.1 J.1 ∧ k ∉ I.1 ∧ k ∉ J.1
    · by_cases hSL : Disjoint S.1 L.1 ∧ k ∉ S.1 ∧ k ∉ L.1
      · rcases exteriorSign_pair_invariants hIJ hSL with ⟨h1, h2, h3, _⟩
        exact absurd ⟨h1, h2, h3⟩ hcond
      · simp [exteriorSign, hSL]
    · simp [exteriorSign, hIJ]

/-- **Lemma 10 (`psiFlat_Omega_signed_kneser_block`):** After conjugating `psiFlat p (Omega_p K p)`
by the diagonal `±1` matrix `diagSignMat K p`, the matrix is block-diagonal across disjoint
pairs `(P, Q)` of `(p - q)`-subsets, and the `(P, Q)` block (indexed by `q`-subsets of
`R = (P ∪ Q)ᶜ`, `|R| = 2q + 1`, including `q = 0` where `B_0 = [1]`) equals
`(-1)^{p - q} • kneserMat K q`. -/
theorem psiFlat_Omega_signed_kneser_block (K : Type*) [CommRing K] (p : ℕ) :
    (∀ J L S I : PSub p,
      ¬ (J.1 \ L.1 = S.1 \ I.1 ∧ L.1 \ J.1 = I.1 \ S.1) →
      (diagSignMat K p * psiFlat p (Omega_p K p) * diagSignMat K p) (J, L) (S, I) = 0) ∧
    (∀ (q : ℕ) (_hq : q ≤ p) (P Q : Finset (Fin (2 * p + 1)))
      (_hPQ : Disjoint P Q) (hP : P.card = p - q) (hQ : Q.card = p - q),
      let V := {x : Fin (2 * p + 1) // x ∈ (P ∪ Q)ᶜ}
      let lift : Finset V → Finset (Fin (2 * p + 1)) :=
        fun A => A.map ⟨Subtype.val, Subtype.val_injective⟩
      let emb : QSub V q → PSub p × PSub p := fun C =>
        (⟨P ∪ lift C.1, by
            have hd : Disjoint P (lift C.1) := Finset.disjoint_left.mpr fun x hxP hxC => by
              rcases Finset.mem_map.mp hxC with ⟨y, _, rfl⟩
              exact (Finset.mem_compl.mp y.2) (Finset.mem_union_left Q hxP)
            rw [Finset.card_union_of_disjoint hd, Finset.card_map, hP, C.2]
            omega⟩,
         ⟨Q ∪ lift C.1, by
            have hd : Disjoint Q (lift C.1) := Finset.disjoint_left.mpr fun x hxQ hxC => by
              rcases Finset.mem_map.mp hxC with ⟨y, _, rfl⟩
              exact (Finset.mem_compl.mp y.2) (Finset.mem_union_right P hxQ)
            rw [Finset.card_union_of_disjoint hd, Finset.card_map, hQ, C.2]
            omega⟩)
      (diagSignMat K p * psiFlat p (Omega_p K p) * diagSignMat K p).submatrix emb emb =
        ((-1 : K) ^ (p - q)) • kneserMat K (V := V) q) := by
  have hconj : ∀ J L S I : PSub p,
      (diagSignMat K p * psiFlat p (Omega_p K p) * diagSignMat K p) (J, L) (S, I) =
      if J.1 \ L.1 = S.1 \ I.1 ∧ L.1 \ J.1 = I.1 \ S.1 ∧ Disjoint (J.1 ∩ L.1) (S.1 ∩ I.1) then
        (-1 : K) ^ (J.1 \ L.1).card
      else 0 := by
    intro J L S I
    simp only [diagSignMat, Matrix.diagonal_mul, Matrix.mul_diagonal, psiFlat_Omega_apply]
    split_ifs with h
    · have h1 : (pairDiagSign J L : K) * (pairDiagSign J L : K) = 1 := by
        rw [← Int.cast_mul, pairDiagSign_mul_self, Int.cast_one]
      have h2 : (pairDiagSign S I : K) * (pairDiagSign S I : K) = 1 := by
        rw [← Int.cast_mul, pairDiagSign_mul_self, Int.cast_one]
      push_cast
      calc (pairDiagSign J L : K) *
              ((-1 : K) ^ (J.1 \ L.1).card * (pairDiagSign J L : K) * (pairDiagSign S I : K)) *
              (pairDiagSign S I : K)
          = (-1 : K) ^ (J.1 \ L.1).card *
              ((pairDiagSign J L : K) * (pairDiagSign J L : K)) *
              ((pairDiagSign S I : K) * (pairDiagSign S I : K)) := by ring
        _ = (-1 : K) ^ (J.1 \ L.1).card := by rw [h1, h2, mul_one, mul_one]
    · simp
  constructor
  · intro J L S I hne
    rw [hconj]
    have hnot : ¬ (J.1 \ L.1 = S.1 \ I.1 ∧ L.1 \ J.1 = I.1 \ S.1 ∧ Disjoint (J.1 ∩ L.1) (S.1 ∩ I.1)) :=
      fun h => hne ⟨h.1, h.2.1⟩
    simp only [hnot, ↓reduceIte]
  · intro q _hq P Q hPQ hP hQ
    dsimp only
    ext C D
    simp only [Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul, kneserMat]
    rw [hconj]
    have hdisjP : ∀ A : Finset {x : Fin (2 * p + 1) // x ∈ (P ∪ Q)ᶜ},
        Disjoint P (A.map ⟨Subtype.val, Subtype.val_injective⟩) := fun A =>
      Finset.disjoint_left.mpr fun x hxP hxA => by
        rcases Finset.mem_map.mp hxA with ⟨y, _, rfl⟩
        exact (Finset.mem_compl.mp y.2) (Finset.mem_union_left Q hxP)
    have hdisjQ : ∀ A : Finset {x : Fin (2 * p + 1) // x ∈ (P ∪ Q)ᶜ},
        Disjoint Q (A.map ⟨Subtype.val, Subtype.val_injective⟩) := fun A =>
      Finset.disjoint_left.mpr fun x hxQ hxA => by
        rcases Finset.mem_map.mp hxA with ⟨y, _, rfl⟩
        exact (Finset.mem_compl.mp y.2) (Finset.mem_union_right P hxQ)
    have hsdiff1 : ∀ A : Finset {x : Fin (2 * p + 1) // x ∈ (P ∪ Q)ᶜ},
        (P ∪ A.map ⟨Subtype.val, Subtype.val_injective⟩) \
          (Q ∪ A.map ⟨Subtype.val, Subtype.val_injective⟩) = P := fun A => by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hxP | hxA, hnot⟩
        · exact hxP
        · exact absurd (Or.inr hxA) hnot
      · intro hxP
        exact ⟨Or.inl hxP, fun h => h.elim (Finset.disjoint_left.mp hPQ hxP)
          (Finset.disjoint_left.mp (hdisjP A) hxP)⟩
    have hsdiff2 : ∀ A : Finset {x : Fin (2 * p + 1) // x ∈ (P ∪ Q)ᶜ},
        (Q ∪ A.map ⟨Subtype.val, Subtype.val_injective⟩) \
          (P ∪ A.map ⟨Subtype.val, Subtype.val_injective⟩) = Q := fun A => by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hxQ | hxA, hnot⟩
        · exact hxQ
        · exact absurd (Or.inr hxA) hnot
      · intro hxQ
        exact ⟨Or.inl hxQ, fun h => h.elim (Finset.disjoint_right.mp hPQ hxQ)
          (Finset.disjoint_left.mp (hdisjQ A) hxQ)⟩
    have hinter : ∀ A : Finset {x : Fin (2 * p + 1) // x ∈ (P ∪ Q)ᶜ},
        (P ∪ A.map ⟨Subtype.val, Subtype.val_injective⟩) ∩
          (Q ∪ A.map ⟨Subtype.val, Subtype.val_injective⟩) =
        A.map ⟨Subtype.val, Subtype.val_injective⟩ := fun A => by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hxP | hxA, hxQ | hxA'⟩
        · exact absurd hxQ (Finset.disjoint_left.mp hPQ hxP)
        · exact hxA'
        · exact hxA
        · exact hxA
      · intro hxA
        exact ⟨Or.inr hxA, Or.inr hxA⟩
    have hdisj_lift :
        Disjoint (C.1.map ⟨Subtype.val, Subtype.val_injective⟩)
          (D.1.map ⟨Subtype.val, Subtype.val_injective⟩) ↔ Disjoint C.1 D.1 := by
      simp only [Finset.disjoint_left, Finset.mem_map, Function.Embedding.coeFn_mk]
      constructor
      · intro h y hyC hyD
        exact h ⟨y, hyC, rfl⟩ ⟨y, hyD, rfl⟩
      · rintro h x ⟨y, hyC, rfl⟩ ⟨z, hyD, hzy⟩
        have hyz : y = z := Subtype.ext hzy.symm
        exact h hyC (hyz ▸ hyD)
    simp only [hsdiff1, hsdiff2, hinter, hP, true_and, hdisj_lift]
    split_ifs <;> simp

/-- Explicit blockwise inverse `(Ψ_p(Ω_p))⁻¹` over a field `K` (Corollary 12). -/
def psiFlatOmegaInv (K : Type*) [Field K] (p : ℕ) :
    Matrix (PSub p × PSub p) (PSub p × PSub p) K :=
  fun row col =>
    if row.1.1 \ row.2.1 = col.1.1 \ col.2.1 ∧ row.2.1 \ row.1.1 = col.2.1 \ col.1.1 then
      let q := (row.1.1 ∩ row.2.1).card
      let h := ((row.1.1 ∩ row.2.1) ∩ (col.1.1 ∩ col.2.1)).card
      ((-1 : ℤ) ^ (row.1.1 \ row.2.1).card * pairDiagSign row.1 row.2 * pairDiagSign col.1 col.2 : K) *
        ((-1 : K) ^ h * (((q + 1 : K) * (Nat.choose q h : K))⁻¹))
    else 0

/-- Explicit blockwise inverse `(Ψ_{p,m}(U_{p,m}))⁻¹ = I_m ⊗ (Ψ_p(Ω_p))⁻¹`. -/
def psiFlatOmegaInv_pm (K : Type*) [Field K] (p m : ℕ) :
    Matrix (Fin m × PSub p × PSub p) (Fin m × PSub p × PSub p) K :=
  fun row col => if row.1 = col.1 then psiFlatOmegaInv K p row.2 col.2 else 0

/-- **Corollary 12 (`psiFlat_Omega_invertible`):** Over any field `K` in which `1, …, p + 1`
are nonzero, `psiFlat p (Omega_p K p)` is invertible with explicit two-sided inverse
`psiFlatOmegaInv K p`. -/
theorem psiFlat_Omega_invertible (K : Type*) [Field K] (p : ℕ)
    (hunit : ∀ j : ℕ, 1 ≤ j → j ≤ p + 1 → (j : K) ≠ 0) :
    psiFlat p (Omega_p K p) * psiFlatOmegaInv K p = 1 ∧
    psiFlatOmegaInv K p * psiFlat p (Omega_p K p) = 1 := by
  have hmul : psiFlat p (Omega_p K p) * psiFlatOmegaInv K p = 1 := by
    ext ⟨J, L⟩ ⟨J', L'⟩
    rw [Matrix.mul_apply, Matrix.one_apply]
    by_cases hPQ : J.1 \ L.1 = J'.1 \ L'.1 ∧ L.1 \ J.1 = L'.1 \ J'.1
    · rcases hPQ with ⟨hP_eq, hQ_eq⟩
      let P := J.1 \ L.1
      let Q := L.1 \ J.1
      let q := (J.1 ∩ L.1).card
      have hq_le : q ≤ p := le_trans (Finset.card_le_card Finset.inter_subset_left) J.2.le
      have hP_card : P.card + q = p := by
        have := Finset.card_sdiff_add_card_inter J.1 L.1
        rw [J.2] at this; exact this
      have hQ_card : Q.card + q = p := by
        have := Finset.card_sdiff_add_card_inter L.1 J.1
        rw [Finset.inter_comm, L.2] at this; exact this
      have hdisjPQ : Disjoint P Q := by
        refine Finset.disjoint_left.mpr fun x h1 h2 => ?_
        exact (Finset.mem_sdiff.mp h1).2 (Finset.mem_sdiff.mp h2).1
      let R := (P ∪ Q)ᶜ
      have hR_card : R.card = 2 * q + 1 := by
        rw [Finset.card_compl, Finset.card_union_of_disjoint hdisjPQ, Fintype.card_fin]
        omega
      let V := {x : Fin (2 * p + 1) // x ∈ R}
      have hV_card : Fintype.card V = 2 * q + 1 := by
        rw [Fintype.card_coe, hR_card]
      let lift : Finset V → Finset (Fin (2 * p + 1)) :=
        fun A => A.map ⟨Subtype.val, Subtype.val_injective⟩
      have hdisjP : ∀ A : Finset V, Disjoint P (lift A) := fun A =>
        Finset.disjoint_left.mpr fun x hxP hxA => by
          rcases Finset.mem_map.mp hxA with ⟨y, _, rfl⟩
          exact (Finset.mem_compl.mp y.2) (Finset.mem_union_left Q hxP)
      have hdisjQ : ∀ A : Finset V, Disjoint Q (lift A) := fun A =>
        Finset.disjoint_left.mpr fun x hxQ hxA => by
          rcases Finset.mem_map.mp hxA with ⟨y, _, rfl⟩
          exact (Finset.mem_compl.mp y.2) (Finset.mem_union_right P hxQ)
      have hlift_inter : ∀ A B : Finset V, lift (A ∩ B) = lift A ∩ lift B := fun A B => by
        ext x
        simp only [lift, Finset.mem_map, Finset.mem_inter, Function.Embedding.coeFn_mk]
        constructor
        · rintro ⟨y, ⟨hyA, hyB⟩, rfl⟩; exact ⟨⟨y, hyA, rfl⟩, ⟨y, hyB, rfl⟩⟩
        · rintro ⟨⟨y, hyA, rfl⟩, ⟨z, hyB, hzy⟩⟩
          have hyz : y = z := Subtype.ext hzy.symm
          exact ⟨y, ⟨hyA, hyz ▸ hyB⟩, rfl⟩
      have hlift_disj : ∀ A B : Finset V, Disjoint (lift A) (lift B) ↔ Disjoint A B := fun A B => by
        simp only [lift, Finset.disjoint_left, Finset.mem_map, Function.Embedding.coeFn_mk]
        constructor
        · intro h y hyA hyB; exact h ⟨y, hyA, rfl⟩ ⟨y, hyB, rfl⟩
        · rintro h x ⟨y, hyA, rfl⟩ ⟨z, hyB, hzy⟩
          exact h hyA ((Subtype.ext hzy.symm : y = z) ▸ hyB)
      have hC_sub : J.1 ∩ L.1 ⊆ R := fun x hx => by
        rw [Finset.mem_compl, Finset.mem_union, not_or]
        exact ⟨fun hxP => (Finset.mem_sdiff.mp hxP).2 (Finset.mem_inter.mp hx).2,
          fun hxQ => (Finset.mem_sdiff.mp hxQ).2 (Finset.mem_inter.mp hx).1⟩
      have hC'_sub : J'.1 ∩ L'.1 ⊆ R := fun x hx => by
        rw [Finset.mem_compl, Finset.mem_union, not_or]
        exact ⟨fun hxP => by
            change x ∈ J.1 \ L.1 at hxP
            rw [hP_eq] at hxP; exact (Finset.mem_sdiff.mp hxP).2 (Finset.mem_inter.mp hx).2,
          fun hxQ => by
            change x ∈ L.1 \ J.1 at hxQ
            rw [hQ_eq] at hxQ; exact (Finset.mem_sdiff.mp hxQ).2 (Finset.mem_inter.mp hx).1⟩
      have hC'_card : (J'.1 ∩ L'.1).card = q := by
        have h1 := Finset.card_sdiff_add_card_inter J'.1 L'.1
        rw [← hP_eq, J'.2] at h1
        change P.card + (J'.1 ∩ L'.1).card = p at h1
        omega
      let toV : ∀ (A : Finset (Fin (2 * p + 1))), A ⊆ R → Finset V :=
        fun A hA => A.attach.map ⟨fun x : {y // y ∈ A} => (⟨x.1, hA x.2⟩ : V), fun _ _ h =>
          Subtype.ext (congrArg (Subtype.val : V → Fin (2 * p + 1)) h)⟩
      have hlift_toV : ∀ (A : Finset (Fin (2 * p + 1))) (hA : A ⊆ R), lift (toV A hA) = A := by
        intro A hA
        ext x
        simp only [lift, toV, Finset.mem_map, Finset.mem_attach, Function.Embedding.coeFn_mk,
          true_and, Subtype.exists]
        constructor
        · rintro ⟨w, _, ⟨y, hy, heq⟩, rfl⟩
          have hyw : y = w := congrArg (Subtype.val : V → Fin (2 * p + 1)) heq
          exact hyw ▸ hy
        · intro hx; exact ⟨x, hA hx, ⟨x, hx, rfl⟩, rfl⟩
      have hcard_toV : ∀ (A : Finset (Fin (2 * p + 1))) (hA : A ⊆ R), (toV A hA).card = A.card := by
        intro A hA
        rw [← Finset.card_map ⟨Subtype.val, Subtype.val_injective⟩]
        exact congrArg Finset.card (hlift_toV A hA)
      let C_V : QSub V q := ⟨toV (J.1 ∩ L.1) hC_sub, by rw [hcard_toV]⟩
      let C'_V : QSub V q := ⟨toV (J'.1 ∩ L'.1) hC'_sub, by rw [hcard_toV, hC'_card]⟩
      let block := Finset.univ.filter (fun SI : PSub p × PSub p =>
        SI.1.1 \ SI.2.1 = P ∧ SI.2.1 \ SI.1.1 = Q)
      have hsum_block :
          ∑ SI : PSub p × PSub p,
            psiFlat p (Omega_p K p) (J, L) SI * psiFlatOmegaInv K p SI (J', L') =
          ∑ SI ∈ block,
            psiFlat p (Omega_p K p) (J, L) SI * psiFlatOmegaInv K p SI (J', L') := by
        symm
        refine Finset.sum_subset (Finset.subset_univ block) fun SI _ hnot => ?_
        have hne : ¬ (SI.1.1 \ SI.2.1 = P ∧ SI.2.1 \ SI.1.1 = Q) := by
          simpa [block] using hnot
        have hzero : psiFlat p (Omega_p K p) (J, L) SI = 0 := by
          rw [psiFlat_Omega_apply]
          have hnot' : ¬ (J.1 \ L.1 = SI.1.1 \ SI.2.1 ∧ L.1 \ J.1 = SI.2.1 \ SI.1.1 ∧
              Disjoint (J.1 ∩ L.1) (SI.1.1 ∩ SI.2.1)) :=
            fun h => hne ⟨h.1.symm, h.2.1.symm⟩
          exact ite_eq_right_of_eq_false _ _ (eq_false hnot')
        rw [hzero, zero_mul]
      rw [hsum_block]
      have hbij :
          (∑ SI ∈ block,
            psiFlat p (Omega_p K p) (J, L) SI * psiFlatOmegaInv K p SI (J', L')) =
          (pairDiagSign J L : K) * (pairDiagSign J' L' : K) *
            ∑ D_V : QSub V q, kneserMat K (V := V) q C_V D_V * kneserInv K (V := V) q D_V C'_V := by
        rw [Finset.mul_sum]
        symm
        refine Finset.sum_bij
          (fun (D_V : QSub V q) _ =>
            (⟨P ∪ lift D_V.1, by
                rw [Finset.card_union_of_disjoint (hdisjP D_V.1), Finset.card_map, D_V.2, hP_card]⟩,
             ⟨Q ∪ lift D_V.1, by
                rw [Finset.card_union_of_disjoint (hdisjQ D_V.1), Finset.card_map, D_V.2, hQ_card]⟩))
          ?_ ?_ ?_ ?_
        · intro D_V _
          simp only [block, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · ext x; simp only [Finset.mem_sdiff, Finset.mem_union]
            constructor
            · rintro ⟨hxP | hxD, hnot⟩
              · exact hxP
              · exact absurd (Or.inr hxD) hnot
            · intro hxP
              exact ⟨Or.inl hxP, fun h => h.elim (Finset.disjoint_left.mp hdisjPQ hxP)
                (Finset.disjoint_left.mp (hdisjP D_V.1) hxP)⟩
          · ext x; simp only [Finset.mem_sdiff, Finset.mem_union]
            constructor
            · rintro ⟨hxQ | hxD, hnot⟩
              · exact hxQ
              · exact absurd (Or.inr hxD) hnot
            · intro hxQ
              exact ⟨Or.inl hxQ, fun h => h.elim (Finset.disjoint_right.mp hdisjPQ hxQ)
                (Finset.disjoint_left.mp (hdisjQ D_V.1) hxQ)⟩
        · intro D₁ _ D₂ _ hEq
          have h1 : P ∪ lift D₁.1 = P ∪ lift D₂.1 :=
            congrArg (fun x : PSub p × PSub p => x.1.1) hEq
          have hlift_eq : lift D₁.1 = lift D₂.1 := by
            ext x
            constructor
            · intro hx
              have hmem : x ∈ P ∪ lift D₂.1 := h1 ▸ Finset.mem_union_right P hx
              rcases Finset.mem_union.mp hmem with hxP | hx2
              · exact absurd hx (Finset.disjoint_left.mp (hdisjP D₁.1) hxP)
              · exact hx2
            · intro hx
              have hmem : x ∈ P ∪ lift D₁.1 := h1.symm ▸ Finset.mem_union_right P hx
              rcases Finset.mem_union.mp hmem with hxP | hx1
              · exact absurd hx (Finset.disjoint_left.mp (hdisjP D₂.1) hxP)
              · exact hx1
          exact Subtype.ext (Finset.map_injective ⟨Subtype.val, Subtype.val_injective⟩ hlift_eq)
        · intro ⟨S, I⟩ hSI
          simp only [block, Finset.mem_filter, Finset.mem_univ, true_and] at hSI
          rcases hSI with ⟨hSP, hIQ⟩
          have hD_sub : S.1 ∩ I.1 ⊆ R := fun x hx => by
            rw [Finset.mem_compl, Finset.mem_union, not_or]
            exact ⟨fun hxP => by
                rw [← hSP] at hxP; exact (Finset.mem_sdiff.mp hxP).2 (Finset.mem_inter.mp hx).2,
              fun hxQ => by
                rw [← hIQ] at hxQ; exact (Finset.mem_sdiff.mp hxQ).2 (Finset.mem_inter.mp hx).1⟩
          have hD_card : (S.1 ∩ I.1).card = q := by
            have h1 := Finset.card_sdiff_add_card_inter S.1 I.1
            rw [hSP, S.2] at h1
            omega
          let D_V : QSub V q := ⟨toV (S.1 ∩ I.1) hD_sub, by rw [hcard_toV, hD_card]⟩
          refine ⟨D_V, Finset.mem_univ D_V, ?_⟩
          refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
          · dsimp only [D_V]
            rw [hlift_toV, ← hSP]
            exact Finset.sdiff_union_inter S.1 I.1
          · dsimp only [D_V]
            rw [hlift_toV, ← hIQ, Finset.inter_comm S.1 I.1]
            exact Finset.sdiff_union_inter I.1 S.1
        · intro D_V _
          let S_D : PSub p := ⟨P ∪ lift D_V.1, by
            rw [Finset.card_union_of_disjoint (hdisjP D_V.1), Finset.card_map, D_V.2, hP_card]⟩
          let I_D : PSub p := ⟨Q ∪ lift D_V.1, by
            rw [Finset.card_union_of_disjoint (hdisjQ D_V.1), Finset.card_map, D_V.2, hQ_card]⟩
          have hSP : S_D.1 \ I_D.1 = P := by
            ext x; simp only [S_D, I_D, Finset.mem_sdiff, Finset.mem_union]
            constructor
            · rintro ⟨hxP | hxD, hnot⟩
              · exact hxP
              · exact absurd (Or.inr hxD) hnot
            · intro hxP
              exact ⟨Or.inl hxP, fun h => h.elim (Finset.disjoint_left.mp hdisjPQ hxP)
                (Finset.disjoint_left.mp (hdisjP D_V.1) hxP)⟩
          have hIQ : I_D.1 \ S_D.1 = Q := by
            ext x; simp only [S_D, I_D, Finset.mem_sdiff, Finset.mem_union]
            constructor
            · rintro ⟨hxQ | hxD, hnot⟩
              · exact hxQ
              · exact absurd (Or.inr hxD) hnot
            · intro hxQ
              exact ⟨Or.inl hxQ, fun h => h.elim (Finset.disjoint_right.mp hdisjPQ hxQ)
                (Finset.disjoint_left.mp (hdisjQ D_V.1) hxQ)⟩
          have hSI_inter : S_D.1 ∩ I_D.1 = lift D_V.1 := by
            ext x; simp only [S_D, I_D, Finset.mem_inter, Finset.mem_union]
            constructor
            · rintro ⟨hxP | hxD, hxQ | hxD'⟩
              · exact absurd hxQ (Finset.disjoint_left.mp hdisjPQ hxP)
              · exact hxD'
              · exact hxD
              · exact hxD
            · intro hxD; exact ⟨Or.inr hxD, Or.inr hxD⟩
          have hq_eq : (S_D.1 ∩ I_D.1).card = q := by
            rw [hSI_inter, Finset.card_map, D_V.2]
          have hh_eq : ((S_D.1 ∩ I_D.1) ∩ (J'.1 ∩ L'.1)).card = (D_V.1 ∩ C'_V.1).card := by
            have hC'_lift : J'.1 ∩ L'.1 = lift C'_V.1 := (hlift_toV _ hC'_sub).symm
            rw [hSI_inter, hC'_lift, ← hlift_inter, Finset.card_map]
          have hdisj_eq : Disjoint (J.1 ∩ L.1) (S_D.1 ∩ I_D.1) ↔ Disjoint C_V.1 D_V.1 := by
            have hC_lift : J.1 ∩ L.1 = lift C_V.1 := (hlift_toV _ hC_sub).symm
            rw [hSI_inter, hC_lift, hlift_disj]
          change (pairDiagSign J L : K) * (pairDiagSign J' L' : K) *
              (kneserMat K (V := V) q C_V D_V * kneserInv K (V := V) q D_V C'_V) =
            psiFlat p (Omega_p K p) (J, L) (S_D, I_D) *
              psiFlatOmegaInv K p (S_D, I_D) (J', L')
          rw [psiFlat_Omega_apply]
          unfold psiFlatOmegaInv kneserMat kneserInv
          have hcond_inv : S_D.1 \ I_D.1 = J'.1 \ L'.1 ∧ I_D.1 \ S_D.1 = L'.1 \ J'.1 :=
            ⟨hSP.trans hP_eq, hIQ.trans hQ_eq⟩
          rw [ite_eq_left_of_eq_true _ _ (eq_true hcond_inv)]
          by_cases hd : Disjoint C_V.1 D_V.1
          · have hcond_M : J.1 \ L.1 = S_D.1 \ I_D.1 ∧ L.1 \ J.1 = I_D.1 \ S_D.1 ∧
                Disjoint (J.1 ∩ L.1) (S_D.1 ∩ I_D.1) :=
              ⟨hSP.symm, hIQ.symm, hdisj_eq.mpr hd⟩
            rw [ite_eq_left_of_eq_true _ _ (eq_true hd),
              ite_eq_left_of_eq_true _ _ (eq_true hcond_M), one_mul]
            simp only [hq_eq, hh_eq, hSP]
            have hsigSI : (pairDiagSign S_D I_D : K) * (pairDiagSign S_D I_D : K) = 1 := by
              rw [← Int.cast_mul, pairDiagSign_mul_self, Int.cast_one]
            have hpow_sq : ((-1 : K) ^ P.card) * ((-1 : K) ^ P.card) = 1 := by
              rw [← mul_pow]; norm_num
            push_cast
            calc (pairDiagSign J L : K) * (pairDiagSign J' L' : K) *
                  ((-1 : K) ^ (D_V.1 ∩ C'_V.1).card *
                    ((↑q + 1) * ↑(q.choose (D_V.1 ∩ C'_V.1).card))⁻¹)
                = ((pairDiagSign J L : K) * (pairDiagSign J' L' : K)) *
                  (((-1 : K) ^ P.card) * ((-1 : K) ^ P.card)) *
                  ((pairDiagSign S_D I_D : K) * (pairDiagSign S_D I_D : K)) *
                  ((-1 : K) ^ (D_V.1 ∩ C'_V.1).card *
                    ((↑q + 1) * ↑(q.choose (D_V.1 ∩ C'_V.1).card))⁻¹) := by
                      rw [hpow_sq, hsigSI, mul_one, mul_one]
              _ = (-1 : K) ^ P.card * (pairDiagSign J L : K) * (pairDiagSign S_D I_D : K) *
                  ((-1 : K) ^ P.card * (pairDiagSign S_D I_D : K) * (pairDiagSign J' L' : K) *
                    ((-1 : K) ^ (D_V.1 ∩ C'_V.1).card *
                      ((↑q + 1) * ↑(q.choose (D_V.1 ∩ C'_V.1).card))⁻¹)) := by
                      ring
          · have hcond_M : ¬ (J.1 \ L.1 = S_D.1 \ I_D.1 ∧ L.1 \ J.1 = I_D.1 \ S_D.1 ∧
                Disjoint (J.1 ∩ L.1) (S_D.1 ∩ I_D.1)) :=
              fun h => hd (hdisj_eq.mp h.2.2)
            rw [ite_eq_right_of_eq_false _ _ (eq_false hd),
              ite_eq_right_of_eq_false _ _ (eq_false hcond_M)]
            simp only [zero_mul, mul_zero]
      rw [hbij]
      have hunit_q : ∀ j : ℕ, 1 ≤ j → j ≤ q + 1 → (j : K) ≠ 0 :=
        fun j h1 h2 => hunit j h1 (by omega)
      have hkinv := congrFun (congrFun (kneserMat_mul_inv K (V := V) hV_card hunit_q).1 C_V) C'_V
      rw [Matrix.mul_apply, Matrix.one_apply] at hkinv
      rw [hkinv]
      have hiff : C_V = C'_V ↔ (J, L) = (J', L') := by
        constructor
        · intro hCC
          have hlift_eq : lift C_V.1 = lift C'_V.1 := congrArg (fun x : QSub V q => lift x.1) hCC
          rw [hlift_toV _ hC_sub, hlift_toV _ hC'_sub] at hlift_eq
          refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
          · rw [← Finset.sdiff_union_inter J.1 L.1, ← Finset.sdiff_union_inter J'.1 L'.1,
              hP_eq, hlift_eq]
          · rw [← Finset.sdiff_union_inter L.1 J.1, ← Finset.sdiff_union_inter L'.1 J'.1,
              hQ_eq, Finset.inter_comm L.1 J.1, Finset.inter_comm L'.1 J'.1, hlift_eq]
        · intro hEq
          rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
          exact Subtype.ext rfl
      by_cases hEq : (J, L) = (J', L')
      · rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
        have hCC : C_V = C'_V := hiff.mpr rfl
        simp only [hCC, ↓reduceIte, mul_one]
        rw [← Int.cast_mul, pairDiagSign_mul_self, Int.cast_one]
      · have hCC : C_V ≠ C'_V := mt hiff.mp hEq
        simp only [hCC, hEq, ↓reduceIte, mul_zero]
    · have hne : (J, L) ≠ (J', L') := by
        intro hEq
        rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
        exact hPQ ⟨rfl, rfl⟩
      simp only [hne, ↓reduceIte]
      refine Finset.sum_eq_zero fun SI _ => ?_
      rw [psiFlat_Omega_apply]
      unfold psiFlatOmegaInv
      by_cases h1 : J.1 \ L.1 = SI.1.1 \ SI.2.1 ∧ L.1 \ J.1 = SI.2.1 \ SI.1.1
      · have h2 : ¬ (SI.1.1 \ SI.2.1 = J'.1 \ L'.1 ∧ SI.2.1 \ SI.1.1 = L'.1 \ J'.1) :=
          fun h => hPQ ⟨h1.1.trans h.1, h1.2.trans h.2⟩
        simp only [h2, ↓reduceIte, mul_zero]
      · have h1' : ¬ (J.1 \ L.1 = SI.1.1 \ SI.2.1 ∧ L.1 \ J.1 = SI.2.1 \ SI.1.1 ∧
            Disjoint (J.1 ∩ L.1) (SI.1.1 ∩ SI.2.1)) := fun h => h1 ⟨h.1, h.2.1⟩
        simp only [h1', ↓reduceIte, zero_mul]
  refine ⟨hmul, ?_⟩
  have htr_M : (psiFlat p (Omega_p K p)).transpose = psiFlat p (Omega_p K p) := by
    ext ⟨J, L⟩ ⟨S, I⟩
    rw [Matrix.transpose_apply, psiFlat_Omega_apply, psiFlat_Omega_apply]
    have hiff : (S.1 \ I.1 = J.1 \ L.1 ∧ I.1 \ S.1 = L.1 \ J.1 ∧ Disjoint (S.1 ∩ I.1) (J.1 ∩ L.1)) ↔
        (J.1 \ L.1 = S.1 \ I.1 ∧ L.1 \ J.1 = I.1 \ S.1 ∧ Disjoint (J.1 ∩ L.1) (S.1 ∩ I.1)) := by
      simp only [eq_comm, disjoint_comm]
    by_cases h : J.1 \ L.1 = S.1 \ I.1 ∧ L.1 \ J.1 = I.1 \ S.1 ∧ Disjoint (J.1 ∩ L.1) (S.1 ∩ I.1)
    · have h' := hiff.mpr h
      rw [ite_eq_left_of_eq_true _ _ (eq_true h'), ite_eq_left_of_eq_true _ _ (eq_true h), h.1]
      push_cast; ring
    · have h' := mt hiff.mp h
      rw [ite_eq_right_of_eq_false _ _ (eq_false h'), ite_eq_right_of_eq_false _ _ (eq_false h)]
  have htr_inv : (psiFlatOmegaInv K p).transpose = psiFlatOmegaInv K p := by
    ext ⟨J, L⟩ ⟨S, I⟩
    rw [Matrix.transpose_apply]
    unfold psiFlatOmegaInv
    have hiff : (S.1 \ I.1 = J.1 \ L.1 ∧ I.1 \ S.1 = L.1 \ J.1) ↔
        (J.1 \ L.1 = S.1 \ I.1 ∧ L.1 \ J.1 = I.1 \ S.1) := by
      simp only [eq_comm]
    by_cases h : J.1 \ L.1 = S.1 \ I.1 ∧ L.1 \ J.1 = I.1 \ S.1
    · have h' := hiff.mpr h
      rw [ite_eq_left_of_eq_true _ _ (eq_true h'), ite_eq_left_of_eq_true _ _ (eq_true h)]
      have hq_eq : (S.1 ∩ I.1).card = (J.1 ∩ L.1).card := by
        have h1 := Finset.card_sdiff_add_card_inter S.1 I.1
        have h2 := Finset.card_sdiff_add_card_inter J.1 L.1
        rw [S.2] at h1; rw [J.2, h.1] at h2; omega
      rw [h.1, hq_eq, Finset.inter_comm (S.1 ∩ I.1) (J.1 ∩ L.1)]
      push_cast; ring
    · have h' := mt hiff.mp h
      rw [ite_eq_right_of_eq_false _ _ (eq_false h'), ite_eq_right_of_eq_false _ _ (eq_false h)]
  have htr := congrArg Matrix.transpose hmul
  simpa [Matrix.transpose_mul, htr_M, htr_inv] using htr

lemma psiFlat_pm_U_apply (K : Type*) [CommRing K] (p m : ℕ)
    (row col : Fin m × PSub p × PSub p) :
    psiFlat_pm p m (U_pm K p m) row col =
      if row.1 = col.1 then psiFlat p (Omega_p K p) row.2 col.2 else 0 := by
  rcases row with ⟨a, J, L⟩
  rcases col with ⟨b, S, I⟩
  unfold psiFlat_pm psiFlat U_pm
  by_cases hab : a = b
  · subst hab
    simp only [↓reduceIte]
  · have hba : b ≠ a := Ne.symm hab
    simp only [hab, hba, ↓reduceIte, zero_mul, Finset.sum_const_zero]

/-- `m`-copy invertibility of `psiFlat_pm p m (U_pm K p m)` whenever `1, …, p + 1` are nonzero. -/
theorem psiFlat_pm_U_invertible (K : Type*) [Field K] (p m : ℕ)
    (hunit : ∀ j : ℕ, 1 ≤ j → j ≤ p + 1 → (j : K) ≠ 0) :
    psiFlat_pm p m (U_pm K p m) * psiFlatOmegaInv_pm K p m = 1 ∧
    psiFlatOmegaInv_pm K p m * psiFlat_pm p m (U_pm K p m) = 1 := by
  rcases psiFlat_Omega_invertible K p hunit with ⟨hl, hr⟩
  constructor
  · ext ⟨a, row⟩ ⟨b, col⟩
    rw [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply]
    simp_rw [psiFlat_pm_U_apply]
    by_cases hab : a = b
    · subst hab
      have hsum : (∑ c : Fin m, ∑ mid : PSub p × PSub p,
            (if a = c then psiFlat p (Omega_p K p) row mid else 0) *
              psiFlatOmegaInv_pm K p m (c, mid) (a, col)) =
          ∑ mid : PSub p × PSub p,
            psiFlat p (Omega_p K p) row mid * psiFlatOmegaInv K p mid col := by
        rw [Finset.sum_eq_single a]
        · simp [psiFlatOmegaInv_pm]
        · intro c _ hca
          simp [Ne.symm hca]
        · intro habs; exact absurd (Finset.mem_univ a) habs
      rw [hsum, ← Matrix.mul_apply, hl, Matrix.one_apply]
      simp
    · have hzero : (∑ c : Fin m, ∑ mid : PSub p × PSub p,
            (if a = c then psiFlat p (Omega_p K p) row mid else 0) *
              psiFlatOmegaInv_pm K p m (c, mid) (b, col)) = 0 := by
        refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun mid _ => ?_
        by_cases hac : a = c
        · subst hac
          simp [psiFlatOmegaInv_pm, hab]
        · simp [hac]
      have hne : (a, row) ≠ (b, col) := fun h => hab (congrArg Prod.fst h)
      rw [hzero, ite_eq_right_of_eq_false _ _ (eq_false hne)]
  · ext ⟨a, row⟩ ⟨b, col⟩
    rw [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply]
    simp_rw [psiFlat_pm_U_apply]
    by_cases hab : a = b
    · subst hab
      have hsum : (∑ c : Fin m, ∑ mid : PSub p × PSub p,
            psiFlatOmegaInv_pm K p m (a, row) (c, mid) *
              (if c = a then psiFlat p (Omega_p K p) mid col else 0)) =
          ∑ mid : PSub p × PSub p,
            psiFlatOmegaInv K p row mid * psiFlat p (Omega_p K p) mid col := by
        rw [Finset.sum_eq_single a]
        · simp [psiFlatOmegaInv_pm]
        · intro c _ hca
          simp [psiFlatOmegaInv_pm, Ne.symm hca]
        · intro habs; exact absurd (Finset.mem_univ a) habs
      rw [hsum, ← Matrix.mul_apply, hr, Matrix.one_apply]
      simp
    · have hzero : (∑ c : Fin m, ∑ mid : PSub p × PSub p,
            psiFlatOmegaInv_pm K p m (a, row) (c, mid) *
              (if c = b then psiFlat p (Omega_p K p) mid col else 0)) = 0 := by
        refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun mid _ => ?_
        by_cases hac : a = c
        · subst hac
          simp [hab]
        · simp [psiFlatOmegaInv_pm, hac]
      have hne : (a, row) ≠ (b, col) := fun h => hab (congrArg Prod.fst h)
      rw [hzero, ite_eq_right_of_eq_false _ _ (eq_false hne)]

private lemma vandermonde_inv_sum {K α : Type*} [Field K] [DecidableEq α] {p : ℕ}
    (hunit : ∀ j : ℕ, 1 ≤ j → j ≤ p + 1 → (j : K) ≠ 0)
    (I J : Finset α) (hIJ : Disjoint I J) (hI : I.card = p) (hJ : J.card = p) :
    ∑ S ∈ (I ∪ J).powersetCard p, (((S ∩ I).card + 1 : K)⁻¹) =
      (Nat.choose (2 * p + 1) p : K) / (p + 1 : K) := by
  have hmaps : ∀ S ∈ (I ∪ J).powersetCard p, (S ∩ I).card ∈ Finset.range (p + 1) := by
    intro S _
    rw [Finset.mem_range]
    have hle : (S ∩ I).card ≤ p := le_trans (Finset.card_le_card Finset.inter_subset_right) hI.le
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfiber : ∀ q ∈ Finset.range (p + 1),
      (∑ S ∈ ((I ∪ J).powersetCard p).filter (fun S => (S ∩ I).card = q),
        (((S ∩ I).card + 1 : K)⁻¹)) =
      ((Nat.choose p q * Nat.choose p (p - q) : ℕ) : K) * ((q + 1 : K)⁻¹) := by
    intro q hq
    have hq_le : q ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
    have hconst :
        (∑ S ∈ ((I ∪ J).powersetCard p).filter (fun S => (S ∩ I).card = q),
          (((S ∩ I).card + 1 : K)⁻¹)) =
        ((( ((I ∪ J).powersetCard p).filter (fun S => (S ∩ I).card = q) ).card : ℕ) : K) *
          ((q + 1 : K)⁻¹) := by
      calc ∑ S ∈ ((I ∪ J).powersetCard p).filter (fun S => (S ∩ I).card = q),
              (((S ∩ I).card + 1 : K)⁻¹)
          = ∑ _S ∈ ((I ∪ J).powersetCard p).filter (fun S => (S ∩ I).card = q),
              ((q + 1 : K)⁻¹) := by
              refine Finset.sum_congr rfl fun S hS => ?_
              rw [(Finset.mem_filter.mp hS).2]
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    rw [hconst]
    congr 1
    have hcard_fiber :
        (((I ∪ J).powersetCard p).filter (fun S => (S ∩ I).card = q)).card =
        Nat.choose p q * Nat.choose p (p - q) := by
      have hprod_card : (I.powersetCard q ×ˢ J.powersetCard (p - q)).card =
          Nat.choose p q * Nat.choose p (p - q) := by
        rw [Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard, hI, hJ]
      rw [← hprod_card]
      symm
      refine Finset.card_bij (fun AB _ => AB.1 ∪ AB.2) ?_ ?_ ?_
      · intro ⟨A, B⟩ hAB
        simp only [Finset.mem_product, Finset.mem_powersetCard] at hAB
        rcases hAB with ⟨⟨hAI, hAc⟩, ⟨hBJ, hBc⟩⟩
        have hdisjAB : Disjoint A B := hIJ.mono hAI hBJ
        have hinterI : (A ∪ B) ∩ I = A := by
          ext x; simp only [Finset.mem_inter, Finset.mem_union]
          constructor
          · rintro ⟨hxA | hxB, hxI⟩
            · exact hxA
            · exact absurd (hBJ hxB) (Finset.disjoint_left.mp hIJ hxI)
          · intro hxA; exact ⟨Or.inl hxA, hAI hxA⟩
        simp only [Finset.mem_filter, Finset.mem_powersetCard]
        refine ⟨⟨Finset.union_subset_union hAI hBJ, ?_⟩, by rw [hinterI, hAc]⟩
        rw [Finset.card_union_of_disjoint hdisjAB, hAc, hBc]
        omega
      · intro ⟨A₁, B₁⟩ h1 ⟨A₂, B₂⟩ h2 hEq
        simp only [Finset.mem_product, Finset.mem_powersetCard] at h1 h2
        have hA : A₁ = A₂ := by
          ext x
          have hx := Finset.ext_iff.mp hEq x
          simp only [Finset.mem_union] at hx
          constructor
          · intro hx1
            rcases hx.mp (Or.inl hx1) with hx2 | hxB2
            · exact hx2
            · exact absurd (h2.2.1 hxB2) (Finset.disjoint_left.mp hIJ (h1.1.1 hx1))
          · intro hx2
            rcases hx.mpr (Or.inl hx2) with hx1 | hxB1
            · exact hx1
            · exact absurd (h1.2.1 hxB1) (Finset.disjoint_left.mp hIJ (h2.1.1 hx2))
        have hB : B₁ = B₂ := by
          ext x
          have hx := Finset.ext_iff.mp hEq x
          simp only [Finset.mem_union] at hx
          constructor
          · intro hx1
            rcases hx.mp (Or.inr hx1) with hxA2 | hx2
            · exact absurd (h1.2.1 hx1) (Finset.disjoint_left.mp hIJ (h2.1.1 hxA2))
            · exact hx2
          · intro hx2
            rcases hx.mpr (Or.inr hx2) with hxA1 | hx1
            · exact absurd (h2.2.1 hx2) (Finset.disjoint_left.mp hIJ (h1.1.1 hxA1))
            · exact hx1
        exact Prod.ext hA hB
      · intro S hS
        simp only [Finset.mem_filter, Finset.mem_powersetCard] at hS
        rcases hS with ⟨⟨hSsub, hSc⟩, hSIc⟩
        have hSsplit : S = (S ∩ I) ∪ (S ∩ J) := by
          ext x
          simp only [Finset.mem_union, Finset.mem_inter]
          constructor
          · intro hx
            rcases Finset.mem_union.mp (hSsub hx) with hxI | hxJ
            · exact Or.inl ⟨hx, hxI⟩
            · exact Or.inr ⟨hx, hxJ⟩
          · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
        have hdisjS : Disjoint (S ∩ I) (S ∩ J) :=
          hIJ.mono Finset.inter_subset_right Finset.inter_subset_right
        have hSJc : (S ∩ J).card = p - q := by
          have hc := congrArg Finset.card hSsplit
          rw [hSc, Finset.card_union_of_disjoint hdisjS, hSIc] at hc
          omega
        refine ⟨(S ∩ I, S ∩ J), ?_, hSsplit.symm⟩
        simp only [Finset.mem_product, Finset.mem_powersetCard]
        exact ⟨⟨Finset.inter_subset_right, hSIc⟩, ⟨Finset.inter_subset_right, hSJc⟩⟩
    exact congrArg (Nat.cast (R := K)) hcard_fiber
  rw [Finset.sum_congr rfl hfiber]
  have hp1_ne : (p + 1 : K) ≠ 0 := by
    simpa [Nat.cast_add] using hunit (p + 1) (by omega) (le_refl _)
  rw [eq_div_iff hp1_ne, Finset.sum_mul]
  have hterm_eq : ∀ q ∈ Finset.range (p + 1),
      ((Nat.choose p q * Nat.choose p (p - q) : ℕ) : K) * ((q + 1 : K)⁻¹) * (p + 1 : K) =
      ((Nat.choose (p + 1) (q + 1) * Nat.choose p (p - q) : ℕ) : K) := by
    intro q hq
    have hq_le : q ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
    have hq1_ne : (q + 1 : K) ≠ 0 := by
      simpa [Nat.cast_add] using hunit (q + 1) (by omega) (by omega)
    have habs : (p + 1) * Nat.choose p q = (q + 1) * Nat.choose (p + 1) (q + 1) := by
      have h := Nat.add_one_mul_choose_eq p q
      linarith
    have habsK : (p + 1 : K) * (Nat.choose p q : K) =
        (q + 1 : K) * (Nat.choose (p + 1) (q + 1) : K) := by
      have h := congrArg (Nat.cast (R := K)) habs
      simpa [Nat.cast_mul, Nat.cast_add] using h
    push_cast
    calc (Nat.choose p q : K) * (Nat.choose p (p - q) : K) * (q + 1 : K)⁻¹ * (p + 1 : K)
        = ((p + 1 : K) * (Nat.choose p q : K)) * (q + 1 : K)⁻¹ * (Nat.choose p (p - q) : K) := by
            ring
      _ = ((q + 1 : K) * (Nat.choose (p + 1) (q + 1) : K)) * (q + 1 : K)⁻¹ *
            (Nat.choose p (p - q) : K) := by rw [habsK]
      _ = ((q + 1 : K) * (q + 1 : K)⁻¹) *
            ((Nat.choose (p + 1) (q + 1) : K) * (Nat.choose p (p - q) : K)) := by ring
      _ = (Nat.choose (p + 1) (q + 1) : K) * (Nat.choose p (p - q) : K) := by
            rw [mul_inv_cancel₀ hq1_ne, one_mul]
  rw [Finset.sum_congr rfl hterm_eq]
  have hvand : ∑ q ∈ Finset.range (p + 1), Nat.choose (p + 1) (q + 1) * Nat.choose p (p - q) =
      Nat.choose (2 * p + 1) p := by
    have hfull : ∑ r ∈ Finset.range (p + 2), Nat.choose (p + 1) r * Nat.choose p (p + 1 - r) =
        Nat.choose ((p + 1) + p) (p + 1) := by
      simpa [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] using
        (Nat.add_choose_eq (p + 1) p (p + 1)).symm
    rw [Finset.sum_range_succ'] at hfull
    have hzero : Nat.choose (p + 1) 0 * Nat.choose p (p + 1) = 0 := by
      rw [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self p), mul_zero]
    simp only [Nat.sub_zero, hzero, add_zero, Nat.add_sub_add_right] at hfull
    have hsymm : Nat.choose ((p + 1) + p) (p + 1) = Nat.choose (2 * p + 1) p := by
      have h2p : (p + 1) + p = 2 * p + 1 := by omega
      rw [h2p, ← Nat.choose_symm (by omega : p ≤ 2 * p + 1)]
      congr 1; omega
    exact hfull.trans hsymm
  have hvandK := congrArg (Nat.cast (R := K)) hvand
  simpa using hvandK

/-- **Proposition 13 (`psiFlat_Omega_coord_trace`):** Over any field `K` in which `1, …, p + 1`
are nonzero, for every 3-tensor `X` on `PSub p × PSub p × Fin (2p + 1)`,
`Tr(Ψ_p(X) · Ψ_p(Ω_p)⁻¹) = (C(2p + 1, p) / (p + 1)) · ∑_{I, J, k} ε_{I, J, k} X_{I, J, k}`. -/
theorem psiFlat_Omega_coord_trace {K : Type*} [Field K] (p : ℕ)
    (hunit : ∀ j : ℕ, 1 ≤ j → j ≤ p + 1 → (j : K) ≠ 0)
    (X : Tensor3 K (PSub p) (PSub p) (Fin (2 * p + 1))) :
    Matrix.trace (psiFlat p X * psiFlatOmegaInv K p) =
      ((Nat.choose (2 * p + 1) p : K) / (p + 1 : K)) *
        ∑ I : PSub p, ∑ J : PSub p, ∑ k : Fin (2 * p + 1),
          (exteriorSign p I J k : K) * X I J k := by
  have hexpand :
      Matrix.trace (psiFlat p X * psiFlatOmegaInv K p) =
      ∑ I : PSub p, ∑ J : PSub p, ∑ k : Fin (2 * p + 1),
        (∑ S : PSub p, ∑ L : PSub p,
          (exteriorSign p S L k : K) * psiFlatOmegaInv K p (S, I) (J, L)) * X I J k := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, psiFlat, Fintype.sum_prod_type]
    conv_lhs => simp only [Finset.sum_mul]
    calc ∑ J : PSub p, ∑ L : PSub p, ∑ S : PSub p, ∑ I : PSub p, ∑ k : Fin (2 * p + 1),
            X I J k * (exteriorSign p S L k : K) * psiFlatOmegaInv K p (S, I) (J, L)
        = ∑ J : PSub p, ∑ S : PSub p, ∑ I : PSub p, ∑ k : Fin (2 * p + 1), ∑ L : PSub p,
            X I J k * (exteriorSign p S L k : K) * psiFlatOmegaInv K p (S, I) (J, L) := by
            refine Finset.sum_congr rfl fun J _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun S _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun I _ => ?_
            rw [Finset.sum_comm]
      _ = ∑ J : PSub p, ∑ I : PSub p, ∑ k : Fin (2 * p + 1), ∑ S : PSub p, ∑ L : PSub p,
            X I J k * (exteriorSign p S L k : K) * psiFlatOmegaInv K p (S, I) (J, L) := by
            refine Finset.sum_congr rfl fun J _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun I _ => ?_
            rw [Finset.sum_comm]
      _ = ∑ I : PSub p, ∑ J : PSub p, ∑ k : Fin (2 * p + 1),
            (∑ S : PSub p, ∑ L : PSub p,
              (exteriorSign p S L k : K) * psiFlatOmegaInv K p (S, I) (J, L)) * X I J k := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun I _ =>
              Finset.sum_congr rfl fun J _ =>
              Finset.sum_congr rfl fun k _ => ?_
            symm
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun S _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun L _ => by ring
  rw [hexpand, Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hcoeff :
      (∑ S : PSub p, ∑ L : PSub p,
        (exteriorSign p S L k : K) * psiFlatOmegaInv K p (S, I) (J, L)) =
      ((Nat.choose (2 * p + 1) p : K) / (p + 1 : K)) * (exteriorSign p I J k : K) := by
    by_cases hIJ : Disjoint I.1 J.1 ∧ k ∉ I.1 ∧ k ∉ J.1
    · have hpartIJ : I.1 ∪ J.1 = Finset.univ.erase k := exteriorSign_partition hIJ
      have hinner : ∀ S : PSub p,
          (∑ L : PSub p, (exteriorSign p S L k : K) * psiFlatOmegaInv K p (S, I) (J, L)) =
          if k ∉ S.1 then
            (exteriorSign p I J k : K) * (((S.1 ∩ I.1).card + 1 : K)⁻¹)
          else 0 := by
        intro S
        by_cases hkS : k ∉ S.1
        · rw [ite_eq_left_of_eq_true _ _ (eq_true hkS)]
          have hS_sub : S.1 ⊆ Finset.univ.erase k := fun x hx =>
            Finset.mem_erase.mpr ⟨fun h => hkS (h ▸ hx), Finset.mem_univ x⟩
          have hLS_card : ((Finset.univ.erase k) \ S.1).card = p := by
            rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hS_sub,
              Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin, S.2]
            omega
          let L_S : PSub p := ⟨(Finset.univ.erase k) \ S.1, hLS_card⟩
          have hSL : Disjoint S.1 L_S.1 ∧ k ∉ S.1 ∧ k ∉ L_S.1 := by
            rw [exteriorSign_cond_iff]
            dsimp only [L_S]
            exact Finset.union_sdiff_of_subset hS_sub
          rw [Finset.sum_eq_single L_S]
          · rcases exteriorSign_pair_invariants hIJ hSL with ⟨hP, hQ, _, hsign⟩
            have hsign_SL :
                exteriorSign p S L_S k *
                  ((-1 : ℤ) ^ (J.1 \ L_S.1).card * pairDiagSign S I * pairDiagSign J L_S) =
                exteriorSign p I J k := by
              calc exteriorSign p S L_S k *
                    ((-1 : ℤ) ^ (J.1 \ L_S.1).card * pairDiagSign S I * pairDiagSign J L_S)
                  = exteriorSign p S L_S k *
                    ((-1 : ℤ) ^ (J.1 \ L_S.1).card * pairDiagSign J L_S * pairDiagSign S I) := by
                      ring
                _ = exteriorSign p S L_S k * (exteriorSign p I J k * exteriorSign p S L_S k) := by
                      rw [← hsign]
                _ = exteriorSign p I J k * (exteriorSign p S L_S k * exteriorSign p S L_S k) := by
                      ring
                _ = exteriorSign p I J k := by rw [exteriorSign_mul_self hSL, mul_one]
            have hsign_SL_K :
                (exteriorSign p S L_S k : K) *
                  ((-1 : ℤ) ^ (J.1 \ L_S.1).card * pairDiagSign S I * pairDiagSign J L_S : K) =
                (exteriorSign p I J k : K) := by
              have h := congrArg (Int.cast (R := K)) hsign_SL
              simpa [Int.cast_mul] using h
            have hinter_zero : ((S.1 ∩ I.1) ∩ (J.1 ∩ L_S.1)).card = 0 := by
              have hemp : (S.1 ∩ I.1) ∩ (J.1 ∩ L_S.1) = ∅ := by
                ext x
                simp only [Finset.mem_inter, Finset.notMem_empty, iff_false]
                rintro ⟨⟨_, hxI⟩, ⟨hxJ, _⟩⟩
                exact Finset.disjoint_left.mp hIJ.1 hxI hxJ
              rw [hemp, Finset.card_empty]
            unfold psiFlatOmegaInv
            simp only [hP.symm, hQ.symm, and_self, ↓reduceIte, hinter_zero, pow_zero,
              Nat.choose_zero_right, Nat.cast_one, mul_one, one_mul]
            rw [← mul_assoc, hsign_SL_K]
          · intro L _ hne
            have hnotSL : ¬ (Disjoint S.1 L.1 ∧ k ∉ S.1 ∧ k ∉ L.1) := by
              intro hSL'
              have hpart' := exteriorSign_partition hSL'
              have hLeq : L.1 = L_S.1 := by
                ext x
                simp only [L_S, Finset.mem_sdiff]
                constructor
                · intro hxL
                  have hxk : x ≠ k := fun h => hSL'.2.2 (h ▸ hxL)
                  exact ⟨Finset.mem_erase.mpr ⟨hxk, Finset.mem_univ x⟩,
                    fun hxS => Finset.disjoint_left.mp hSL'.1 hxS hxL⟩
                · rintro ⟨hxk, hxS⟩
                  rw [← hpart'] at hxk
                  rcases Finset.mem_union.mp hxk with h | h
                  · exact absurd h hxS
                  · exact h
              exact hne (Subtype.ext hLeq)
            simp [exteriorSign, hnotSL]
          · intro habs; exact absurd (Finset.mem_univ L_S) habs
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hkS)]
          have hkS' : k ∈ S.1 := by_contra hkS
          refine Finset.sum_eq_zero fun L _ => ?_
          simp [exteriorSign, hkS']
      simp_rw [hinner]
      have hsum_filt :
          (∑ S : PSub p,
            if k ∉ S.1 then (exteriorSign p I J k : K) * (((S.1 ∩ I.1).card + 1 : K)⁻¹) else 0) =
          (exteriorSign p I J k : K) *
            ∑ S ∈ (Finset.univ.erase k).powersetCard p, (((S ∩ I.1).card + 1 : K)⁻¹) := by
        rw [← Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_bij (fun S _ => S.1) ?_ ?_ ?_ ?_
        · intro S hS
          have hkS : k ∉ S.1 := (Finset.mem_filter.mp hS).2
          exact Finset.mem_powersetCard.mpr
            ⟨fun x hx => Finset.mem_erase.mpr ⟨fun h => hkS (h ▸ hx), Finset.mem_univ x⟩, S.2⟩
        · intro S₁ _ S₂ _ hEq; exact Subtype.ext hEq
        · intro A hA
          rcases Finset.mem_powersetCard.mp hA with ⟨hAsub, hAc⟩
          have hkA : k ∉ A := fun hk => (Finset.mem_erase.mp (hAsub hk)).1 rfl
          exact ⟨⟨A, hAc⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkA⟩, rfl⟩
        · intro _ _; rfl
      rw [hsum_filt, ← hpartIJ, vandermonde_inv_sum hunit I.1 J.1 hIJ.1 I.2 J.2, mul_comm]
    · simp only [exteriorSign, hIJ, ↓reduceIte, Int.cast_zero, mul_zero]
      refine Finset.sum_eq_zero fun S _ => Finset.sum_eq_zero fun L _ => ?_
      by_cases hSL : Disjoint S.1 L.1 ∧ k ∉ S.1 ∧ k ∉ L.1
      · by_cases hPQ : S.1 \ I.1 = J.1 \ L.1 ∧ I.1 \ S.1 = L.1 \ J.1
        · exfalso
          apply hIJ
          have hpartSL := exteriorSign_partition hSL
          have hkI : k ∉ I.1 := by
            intro hkI
            have hmem : k ∈ I.1 \ S.1 := Finset.mem_sdiff.mpr ⟨hkI, hSL.2.1⟩
            rw [hPQ.2] at hmem
            exact hSL.2.2 (Finset.mem_sdiff.mp hmem).1
          have hkJ : k ∉ J.1 := by
            intro hkJ
            have hmem : k ∈ J.1 \ L.1 := Finset.mem_sdiff.mpr ⟨hkJ, hSL.2.2⟩
            rw [← hPQ.1] at hmem
            exact hSL.2.1 (Finset.mem_sdiff.mp hmem).1
          have hdisj : Disjoint I.1 J.1 := by
            refine Finset.disjoint_left.mpr fun x hxI hxJ => ?_
            have hxk : x ≠ k := fun h => hkI (h ▸ hxI)
            have hxSL : x ∈ S.1 ∪ L.1 := by
              rw [hpartSL]; exact Finset.mem_erase.mpr ⟨hxk, Finset.mem_univ x⟩
            rcases Finset.mem_union.mp hxSL with hxS | hxL
            · have hxnotL : x ∉ L.1 := Finset.disjoint_left.mp hSL.1 hxS
              have hmem : x ∈ J.1 \ L.1 := Finset.mem_sdiff.mpr ⟨hxJ, hxnotL⟩
              rw [← hPQ.1] at hmem
              exact (Finset.mem_sdiff.mp hmem).2 hxI
            · have hxnotS : x ∉ S.1 := Finset.disjoint_right.mp hSL.1 hxL
              have hmem : x ∈ I.1 \ S.1 := Finset.mem_sdiff.mpr ⟨hxI, hxnotS⟩
              rw [hPQ.2] at hmem
              exact (Finset.mem_sdiff.mp hmem).2 hxJ
          exact ⟨hdisj, hkI, hkJ⟩
        · simp [psiFlatOmegaInv, hPQ]
      · simp [hSL]
  rw [hcoeff]
  ring

/-- `m`-copy coordinate trace formula for `psiFlat_pm p m X * psiFlatOmegaInv_pm K p m`. -/
theorem psiFlat_pm_coord_trace {K : Type*} [Field K] (p m : ℕ)
    (hunit : ∀ j : ℕ, 1 ≤ j → j ≤ p + 1 → (j : K) ≠ 0)
    (X : Tensor3 K (Fin m × PSub p) (Fin m × PSub p) (Fin (2 * p + 1))) :
    Matrix.trace (psiFlat_pm p m X * psiFlatOmegaInv_pm K p m) =
      ((Nat.choose (2 * p + 1) p : K) / (p + 1 : K)) *
        ∑ a : Fin m, ∑ I : PSub p, ∑ J : PSub p, ∑ k : Fin (2 * p + 1),
          (exteriorSign p I J k : K) * X (a, I) (a, J) k := by
  have htr :
      Matrix.trace (psiFlat_pm p m X * psiFlatOmegaInv_pm K p m) =
      ∑ a : Fin m,
        Matrix.trace (psiFlat p (fun I J k => X (a, I) (a, J) k) * psiFlatOmegaInv K p) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun J _ => ?_
    refine Finset.sum_congr rfl fun L _ => ?_
    rw [Finset.sum_eq_single a]
    · simp [psiFlat_pm, psiFlatOmegaInv_pm]
    · intro b _ hba
      simp [psiFlatOmegaInv_pm, hba]
    · intro habs; exact absurd (Finset.mem_univ a) habs
  rw [htr, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact psiFlat_Omega_coord_trace p hunit (fun I J k => X (a, I) (a, J) k)

/-! ## Section 5: All-Parameter Odd-Prime Rank Bound (Theorem 9) and `char K = 5` 5-Pfaffian Theorem -/

private lemma idempotent_trace_eq_rank {K M : Type*} [Field K] [Fintype M] [DecidableEq M]
    (P : Matrix M M K) (hP : P * P = P) :
    Matrix.trace P = (P.rank : K) := by
  let f : Module.End K (M → K) := P.mulVecLin
  have hf_idem : ∀ x : M → K, f (f x) = f x := by
    intro x
    change P *ᵥ (P *ᵥ x) = P *ᵥ x
    rw [Matrix.mulVec_mulVec, hP]
  let U : Submodule K (M → K) := LinearMap.range f
  let W : Submodule K (M → K) := LinearMap.ker f
  have hcompl : IsCompl U W := by
    rw [isCompl_iff]
    constructor
    · rw [disjoint_iff, Submodule.eq_bot_iff]
      rintro y ⟨⟨z, rfl⟩, hyW⟩
      have h0 : f (f z) = 0 := hyW
      rw [hf_idem] at h0
      exact h0
    · rw [codisjoint_iff, Submodule.eq_top_iff']
      intro x
      have hdecomp : x = f x + (x - f x) := by abel
      rw [hdecomp]
      refine Submodule.add_mem_sup ⟨x, rfl⟩ ?_
      change f (x - f x) = 0
      rw [map_sub, hf_idem, sub_self]
  let bU := Module.finBasis K U
  let bW := Module.finBasis K W
  let e : (U × W) ≃ₗ[K] (M → K) := Submodule.prodEquivOfIsCompl U W hcompl
  let b := (bU.prod bW).map e
  have hb_inl : ∀ i : Fin (Module.finrank K U), f (b (Sum.inl i)) = b (Sum.inl i) := by
    intro i
    have hmem : b (Sum.inl i) ∈ U := by
      have hval : b (Sum.inl i) = (bU i : M → K) := by
        simp [b, e, Module.Basis.map_apply, Module.Basis.prod_apply]
      rw [hval]
      exact (bU i).2
    rcases hmem with ⟨z, hz⟩
    rw [← hz, hf_idem]
  have hb_inr : ∀ j : Fin (Module.finrank K W), f (b (Sum.inr j)) = 0 := by
    intro j
    have hmem : b (Sum.inr j) ∈ W := by
      have hval : b (Sum.inr j) = (bW j : M → K) := by
        simp [b, e, Module.Basis.map_apply, Module.Basis.prod_apply]
      rw [hval]
      exact (bW j).2
    exact hmem
  have htr_std : LinearMap.trace K (M → K) f = Matrix.trace P := by
    rw [LinearMap.trace_eq_matrix_trace K (Pi.basisFun K M) f]
    congr 1
    ext i j
    simp [f, Matrix.mulVec_single]
  have htr_b : LinearMap.trace K (M → K) f = Matrix.trace (LinearMap.toMatrix b b f) :=
    LinearMap.trace_eq_matrix_trace K b f
  rw [← htr_std, htr_b, Matrix.trace, Fintype.sum_sum_type]
  have h1 : ∑ i : Fin (Module.finrank K U), Matrix.diag (LinearMap.toMatrix b b f) (Sum.inl i) =
      (Module.finrank K U : K) := by
    have hterm : ∀ i, Matrix.diag (LinearMap.toMatrix b b f) (Sum.inl i) = 1 := by
      intro i
      simp [Matrix.diag, LinearMap.toMatrix_apply, hb_inl i, Module.Basis.repr_self]
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    simp
  have h2 : ∑ j : Fin (Module.finrank K W), Matrix.diag (LinearMap.toMatrix b b f) (Sum.inr j) = 0 := by
    have hterm : ∀ j, Matrix.diag (LinearMap.toMatrix b b f) (Sum.inr j) = 0 := by
      intro j
      simp [Matrix.diag, LinearMap.toMatrix_apply, hb_inr j]
    rw [Finset.sum_congr rfl fun j _ => hterm j]
    simp
  rw [h1, h2, add_zero]
  rfl

private lemma saturated_sum_one_trace_obstruction {K M : Type*} [Field K]
    [Fintype M] [DecidableEq M] [Nonempty M]
    {r κ : ℕ} (hκ_ne : (κ : K) ≠ 0)
    (A : Fin r → Matrix M M K)
    (hsum : ∑ t : Fin r, A t = 1)
    (hrank : ∀ t : Fin r, (A t).rank ≤ κ)
    (htrace : ∀ t : Fin r, Matrix.trace (A t) = 0) :
    Fintype.card M / κ + 1 ≤ r := by
  have hcard_le : Fintype.card M ≤ r * κ := by
    calc Fintype.card M
        = (1 : Matrix M M K).rank := Matrix.rank_one.symm
      _ = (∑ t : Fin r, A t).rank := by rw [hsum]
      _ ≤ ∑ t : Fin r, (A t).rank := matrix_rank_sum_le Finset.univ A
      _ ≤ ∑ _t : Fin r, κ := Finset.sum_le_sum fun t _ => hrank t
      _ = r * κ := by simp
  by_contra hlt
  have hle_div : r ≤ Fintype.card M / κ := by omega
  have hrκ_le : r * κ ≤ Fintype.card M :=
    le_trans (Nat.mul_le_mul_right κ hle_div) (Nat.div_mul_le_self (Fintype.card M) κ)
  have hrκ_eq : r * κ = Fintype.card M := le_antisymm hrκ_le hcard_le
  have hM_pos : 0 < Fintype.card M := Fintype.card_pos
  have hr_pos : 0 < r := by
    by_contra hr0
    have hr_eq : r = 0 := by omega
    rw [hr_eq, zero_mul] at hrκ_eq
    omega
  let t₀ : Fin r := ⟨0, hr_pos⟩
  let P : Matrix M M K := A t₀
  let Q : Matrix M M K := ∑ t ∈ Finset.univ.erase t₀, A t
  have hPQ : P + Q = 1 := by
    rw [← hsum]
    exact Finset.add_sum_erase Finset.univ A (Finset.mem_univ t₀)
  have hP_le : P.rank ≤ κ := hrank t₀
  have hQ_le : Q.rank ≤ (r - 1) * κ := by
    calc Q.rank ≤ ∑ t ∈ Finset.univ.erase t₀, (A t).rank :=
          matrix_rank_sum_le (Finset.univ.erase t₀) A
      _ ≤ ∑ _t ∈ Finset.univ.erase t₀, κ := Finset.sum_le_sum fun t _ => hrank t
      _ = (r - 1) * κ := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ t₀),
            Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hsum_ge : Fintype.card M ≤ P.rank + Q.rank := by
    calc Fintype.card M
        = (1 : Matrix M M K).rank := Matrix.rank_one.symm
      _ = (P + Q).rank := by rw [hPQ]
      _ ≤ P.rank + Q.rank := matrix_rank_add_le P Q
  have hsplit_nat : κ + (r - 1) * κ = Fintype.card M := by
    rw [← hrκ_eq]
    cases r with
    | zero => omega
    | succ r' => simp [Nat.add_mul, Nat.add_comm]
  have hP_eq : P.rank = κ := by omega
  have hPQ_rank : P.rank + Q.rank = Fintype.card M := by omega
  let U : Submodule K (M → K) := LinearMap.range P.mulVecLin
  let W : Submodule K (M → K) := LinearMap.range Q.mulVecLin
  have hsup_top : U ⊔ W = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    have hx : x = P *ᵥ x + Q *ᵥ x := by
      calc x = (1 : Matrix M M K) *ᵥ x := (Matrix.one_mulVec x).symm
        _ = (P + Q) *ᵥ x := by rw [hPQ]
        _ = P *ᵥ x + Q *ᵥ x := Matrix.add_mulVec P Q x
    rw [hx]
    exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩
  have hinf_bot : U ⊓ W = ⊥ := by
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq U W
    rw [hsup_top, finrank_top, Module.finrank_pi] at hdim
    change Fintype.card M + Module.finrank K ↥(U ⊓ W) = P.rank + Q.rank at hdim
    have hzero : Module.finrank K ↥(U ⊓ W) = 0 := by omega
    exact Submodule.finrank_eq_zero.mp hzero
  have hQ_sub : Q = 1 - P := eq_sub_of_add_eq' hPQ
  have hPQ_comm : P * Q = Q * P := by
    rw [hQ_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
  have hPQ_zero : P * Q = 0 := by
    ext i j
    have hv : (P * Q) *ᵥ Pi.single j (1 : K) = 0 := by
      have hU : (P * Q) *ᵥ Pi.single j (1 : K) ∈ U :=
        ⟨Q *ᵥ Pi.single j (1 : K), Matrix.mulVec_mulVec (Pi.single j (1 : K)) P Q⟩
      have hW : (P * Q) *ᵥ Pi.single j (1 : K) ∈ W :=
        ⟨P *ᵥ Pi.single j (1 : K), by
          rw [hPQ_comm]
          exact Matrix.mulVec_mulVec (Pi.single j (1 : K)) Q P⟩
      have hmem : (P * Q) *ᵥ Pi.single j (1 : K) ∈ (⊥ : Submodule K (M → K)) := by
        rw [← hinf_bot]
        exact ⟨hU, hW⟩
      exact (Submodule.mem_bot K).mp hmem
    have hij := congrFun hv i
    simpa [Matrix.mulVec_single] using hij
  have hPP : P * P = P := by
    rw [hQ_sub, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hPQ_zero
    exact hPQ_zero.symm
  have htrP : Matrix.trace P = (κ : K) := by
    rw [idempotent_trace_eq_rank P hPP, hP_eq]
  exact hκ_ne (htrP.symm.trans (htrace t₀))

/-- **Theorem 9 (`shared_exterior_prime_char_rank_ge`):** For all `p ≥ 1`, `m ≥ 1` such that
`2p + 1` is prime, and every field `K` of characteristic `2p + 1`, every tensor-rank
decomposition of `U_{p,m} = I_m ⊗₁,₂ Ω_p` has rank at least
`⌊m · C(2p + 1, p)² / C(2p, p)⌋ + 1`. -/
theorem shared_exterior_prime_char_rank_ge {K : Type*} [Field K]
    {p m : ℕ} (hp : 1 ≤ p) (hm : 1 ≤ m)
    [CharP K (2 * p + 1)] [Fact (Nat.Prime (2 * p + 1))] :
    ∀ r : ℕ, HasTensorRankLe (U_pm K p m) r →
      (m * (Nat.choose (2 * p + 1) p) ^ 2) / Nat.choose (2 * p) p + 1 ≤ r := by
  have hprime : Nat.Prime (2 * p + 1) := Fact.out
  have hunit : ∀ j : ℕ, 1 ≤ j → j ≤ p + 1 → (j : K) ≠ 0 := by
    intro j h1 h2 h0
    have hdvd : (2 * p + 1) ∣ j := (CharP.cast_eq_zero_iff K (2 * p + 1) j).mp h0
    have hle : 2 * p + 1 ≤ j := Nat.le_of_dvd (by omega) hdvd
    omega
  have hchoose_zero : (Nat.choose (2 * p + 1) p : K) = 0 := by
    rw [CharP.cast_eq_zero_iff K (2 * p + 1)]
    exact Nat.Prime.dvd_choose_self hprime (by omega) (by omega)
  have hκ_ne : (Nat.choose (2 * p) p : K) ≠ 0 := by
    intro h0
    have hdvd : (2 * p + 1) ∣ Nat.choose (2 * p) p :=
      (CharP.cast_eq_zero_iff K (2 * p + 1) _).mp h0
    have hfac_eq : Nat.choose (2 * p) p * p.factorial * p.factorial = (2 * p).factorial := by
      have h := Nat.choose_mul_factorial_mul_factorial (by omega : p ≤ 2 * p)
      have hsub : 2 * p - p = p := by omega
      rwa [hsub] at h
    have hdvd_fac : (2 * p + 1) ∣ (2 * p).factorial := by
      rw [← hfac_eq]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hdvd _) _
    have hle : 2 * p + 1 ≤ 2 * p := (Nat.Prime.dvd_factorial hprime).mp hdvd_fac
    omega
  have : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  have : Nonempty (PSub p) := Fintype.card_pos_iff.mp (by
    rw [card_PSub]; exact Nat.choose_pos (by omega))
  have : Nonempty (Fin m × PSub p × PSub p) := inferInstance
  intro r hr
  rcases hr with ⟨u, v, w, hU⟩
  let A : Fin r → Matrix (Fin m × PSub p × PSub p) (Fin m × PSub p × PSub p) K :=
    fun t => psiFlat_pm p m (rankOneTensor (u t) (v t) (w t)) * psiFlatOmegaInv_pm K p m
  have hsum : ∑ t : Fin r, A t = 1 := by
    have hflat_sum : ∑ t : Fin r, psiFlat_pm p m (rankOneTensor (u t) (v t) (w t)) =
        psiFlat_pm p m (U_pm K p m) := by
      rw [← psiFlat_pm_sum]
      congr 1
      funext b₁ b₂ k
      exact (hU b₁ b₂ k).symm
    calc ∑ t : Fin r, A t
        = (∑ t : Fin r, psiFlat_pm p m (rankOneTensor (u t) (v t) (w t))) *
            psiFlatOmegaInv_pm K p m := (Finset.sum_mul _ _ _).symm
      _ = psiFlat_pm p m (U_pm K p m) * psiFlatOmegaInv_pm K p m := by rw [hflat_sum]
      _ = 1 := (psiFlat_pm_U_invertible K p m hunit).1
  have hrank : ∀ t : Fin r, (A t).rank ≤ Nat.choose (2 * p) p := fun t =>
    le_trans (matrix_rank_mul_le_left_local _ _) (psiFlat_pm_pure_rank_le p m (u t) (v t) (w t))
  have htrace : ∀ t : Fin r, Matrix.trace (A t) = 0 := fun t => by
    rw [psiFlat_pm_coord_trace p m hunit, hchoose_zero, zero_div, zero_mul]
  have hbound := saturated_sum_one_trace_obstruction hκ_ne A hsum hrank htrace
  have hcard : Fintype.card (Fin m × PSub p × PSub p) = m * (Nat.choose (2 * p + 1) p) ^ 2 := by
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, card_PSub, sq]
  rwa [hcard] at hbound

/-- **Characteristic-`5` `5`-Pfaffian Theorem (`p = 2, m = 3, char K = 5`):**
Over every field `K` of characteristic `5`, the `(1,2)`-symmetric mode-shared `5`-Pfaffian
tensor `U_{2,3} = I_3 ⊗₁,₂ Ω_2` has both ordinary tensor rank and `(1,2)`-symmetric rank
at least `51` (in particular neither is at most `50`). -/
theorem pfaffian5_shared3_char5_rank_ge_51 (K : Type*) [Field K] [CharP K 5] :
    (∀ b₁ b₂ k, U_pm K 2 3 b₁ b₂ k = U_pm K 2 3 b₂ b₁ k) ∧
    (∀ r : ℕ, HasTensorRankLe (U_pm K 2 3) r → 51 ≤ r) ∧
    ¬ HasTensorRankLe (U_pm K 2 3) 50 ∧
    (∀ r : ℕ, HasSym12RankLe (U_pm K 2 3) r → 51 ≤ r) ∧
    ¬ HasSym12RankLe (U_pm K 2 3) 50 := by
  have : Fact (Nat.Prime (2 * 2 + 1)) := ⟨by decide⟩
  have hge : ∀ r : ℕ, HasTensorRankLe (U_pm K 2 3) r → 51 ≤ r := by
    intro r hr
    have h := shared_exterior_prime_char_rank_ge (K := K) (p := 2) (m := 3)
      (by omega) (by omega) r hr
    have hval : (3 * (Nat.choose (2 * 2 + 1) 2) ^ 2) / Nat.choose (2 * 2) 2 + 1 = 51 := by
      decide
    rwa [hval] at h
  have hn50 : ¬ HasTensorRankLe (U_pm K 2 3) 50 := fun h50 =>
    absurd (hge 50 h50) (by omega)
  have hge_sym : ∀ r : ℕ, HasSym12RankLe (U_pm K 2 3) r → 51 ≤ r :=
    fun r hr => hge r hr.toTensorRankLe
  have hn50_sym : ¬ HasSym12RankLe (U_pm K 2 3) 50 := fun h50 =>
    hn50 h50.toTensorRankLe
  exact ⟨U_pm_isSym12_of_even ⟨1, rfl⟩, hge, hn50, hge_sym, hn50_sym⟩

end SemaevRCB
