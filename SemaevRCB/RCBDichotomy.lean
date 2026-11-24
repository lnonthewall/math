module

public import SemaevRCB.RCBBlockAndPencil
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

@[expose] public section

/-!
# Rank Dichotomy for `I₂ ⊗₁,₂ ε₃` and Projective `j = 0` Addition (`RCBDichotomy`)

Formalizes **Theorem 1.1** (the `char K ≠ 2, 3` dichotomy steps) and its **Proposition 1.3**
transfer to `T_RCB` of Paper 1 (*Arithmetic Rank Dichotomy of the `2 × 3` Maximal-Minors Tensor
and Shared-Input Cross Products*):

Over every field `K` with `char K ≠ 2, 3` (and every `b ∈ Kˣ` for `T_RCB`):
1. **Step 1 (Koszul flattening lower bound):** The `18 × 18` Koszul flattening `Φ` of
   `I₂ ⊗₁,₂ ε₃` maps pure tensors to rank `≤ 2` over any field (including `RatFunc K`) and has
   `det Φ(I₂ ⊗₁,₂ ε₃) = 4 ≠ 0`, yielding the unconditional formal border-rank lower bound `≥ 9`.
2. **Step 2 (Universal formal border rank 9):** Explicit `9`-term `(1,2)`-symmetric polynomial
   degeneration over `K[ε]` proving `HasSym12FormalBorderRankLe (symEps3 K) 9` (and transfer to
   `T_RCB K b` via Proposition 1.3).
3. **Step 3 (Hesse rank-9 construction when `-3 ∈ (Kˣ)²`):** Explicit `9`-term `(1,2)`-symmetric
   Hesse `(9₄, 12₃)` decomposition proving `HasSym12RankLe (symEps3 K) 9` (and `T_RCB K b`)
   whenever `IsSquare (-3 : K)`.
4. **Step 4 (Universal 10-term upper bound):** Explicit `5`-term `ℤ[1/2]` decomposition of `ε₃`
   polarized to a `10`-term `(1,2)`-symmetric decomposition of `symEps3 K` (and `T_RCB K b`).
5. **Step 5 (Arbitrary-field rank-9 obstruction):** Complete formal proof of Section 3.1 (Step 5):
   any `9`-term decomposition of `I₂ ⊗₁,₂ ε₃` over an arbitrary field `K` (`char K ≠ 2, 3`)
   induces zero-slack complementary idempotent projections `P_r P_s = δ_{rs} P_r` on `K¹⁸`
   (without assuming inner-product nondegeneracy on isotropic `w_r`), diagonal `SL₂` alignment
   `V_r = (2 / (3 Δ_r)) U_r J + w_r λ_rᵀ`, pairwise distinct `[w_r] ∈ ℙ²(K)`, off-diagonal
   equiangularity `(ν_rᵀ w_s)(ν_sᵀ w_r) / (Δ_r Δ_s) = 1/4`, and nine rank-`1` idempotents
   `Q_r ∈ Mat₃(K)` with trace Gram matrix `G_Q = (3/4) I₉ + (1/4) J₉` (`det G_Q = 3(81/256)²`)
   congruent to the standard trace form (`det G_std = -1`), forcing `-3 ∈ (Kˣ)²`.
6. **Proposition 1.3 Transfer & Field Corollaries:** Complete dichotomy
   `rk_K(T_RCB) = rk_K^{sym_{1,2}}(T_RCB) = 9` iff `IsSquare (-3 : K)` and `10` otherwise,
   specialized to `ℚ`, `ℝ`, `ℂ`, `AlgebraicClosure K`, and prime fields `𝔽_p` (`p ≥ 5`,
   `p ≡ 1` vs `p ≡ 2 (mod 3)` via quadratic reciprocity). (The `char K = 3` rank-`9` obstruction
   and all-characteristic `char K ≠ 2` dichotomy are completed in `GeneralMinorsAndChar3.lean`.)
-/

namespace SemaevRCB

open Matrix Polynomial BigOperators

/-! ## Section 0: Vector Calculus on `K³` and Square-Matrix Right-Inverse Commutativity -/

/-- Standard algebraic bilinear pairing `xᵀ y = x₀ y₀ + x₁ y₁ + x₂ y₂` on `K³`. -/
def dot3 {K : Type*} [CommRing K] (x y : Fin 3 → K) : K :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2

/-- Standard basis vector `e_m` of `K³`. -/
def stdBasis3 {K : Type*} [CommRing K] (m : Fin 3) : Fin 3 → K :=
  fun i => if i = m then 1 else 0

lemma dot3_comm {K : Type*} [CommRing K] (x y : Fin 3 → K) : dot3 x y = dot3 y x := by
  simp [dot3]; ring

lemma dot3_add_left {K : Type*} [CommRing K] (x₁ x₂ y : Fin 3 → K) :
    dot3 (x₁ + x₂) y = dot3 x₁ y + dot3 x₂ y := by
  simp [dot3]; ring

lemma dot3_add_right {K : Type*} [CommRing K] (x y₁ y₂ : Fin 3 → K) :
    dot3 x (y₁ + y₂) = dot3 x y₁ + dot3 x y₂ := by
  simp [dot3]; ring

lemma dot3_smul_left {K : Type*} [CommRing K] (c : K) (x y : Fin 3 → K) :
    dot3 (c • x) y = c * dot3 x y := by
  simp [dot3]; ring

lemma dot3_smul_right {K : Type*} [CommRing K] (c : K) (x y : Fin 3 → K) :
    dot3 x (c • y) = c * dot3 x y := by
  simp [dot3]; ring

lemma dot3_zero_left {K : Type*} [CommRing K] (y : Fin 3 → K) : dot3 0 y = 0 := by
  simp [dot3]

lemma dot3_zero_right {K : Type*} [CommRing K] (x : Fin 3 → K) : dot3 x 0 = 0 := by
  simp [dot3]

lemma dot3_cross3_self_left {K : Type*} [CommRing K] (w x : Fin 3 → K) :
    dot3 w (cross3 w x) = 0 := by
  simp [dot3, cross3]; ring

lemma dot3_cross3_self_right {K : Type*} [CommRing K] (x w : Fin 3 → K) :
    dot3 w (cross3 x w) = 0 := by
  simp [dot3, cross3]; ring

lemma cross3_self {K : Type*} [CommRing K] (x : Fin 3 → K) : cross3 x x = 0 := by
  funext i; fin_cases i <;> simp [cross3] <;> ring

lemma cross3_anticomm {K : Type*} [CommRing K] (x y : Fin 3 → K) :
    cross3 x y = -cross3 y x := by
  funext i; fin_cases i <;> simp [cross3] <;> ring

lemma cross3_smul_left {K : Type*} [CommRing K] (c : K) (x y : Fin 3 → K) :
    cross3 (c • x) y = c • cross3 x y := by
  funext i; fin_cases i <;> simp [cross3] <;> ring

lemma cross3_smul_right {K : Type*} [CommRing K] (c : K) (x y : Fin 3 → K) :
    cross3 x (c • y) = c • cross3 x y := by
  funext i; fin_cases i <;> simp [cross3] <;> ring

lemma cross3_add_left {K : Type*} [CommRing K] (x₁ x₂ y : Fin 3 → K) :
    cross3 (x₁ + x₂) y = cross3 x₁ y + cross3 x₂ y := by
  funext i; fin_cases i <;> simp [cross3] <;> ring

lemma cross3_add_right {K : Type*} [CommRing K] (x y₁ y₂ : Fin 3 → K) :
    cross3 x (y₁ + y₂) = cross3 x y₁ + cross3 x y₂ := by
  funext i; fin_cases i <;> simp [cross3] <;> ring

/-- Vector triple product `a × (b × c) = (aᵀ c) b - (aᵀ b) c` over any `CommRing`. -/
lemma bac_cab {K : Type*} [CommRing K] (a b c : Fin 3 → K) :
    cross3 a (cross3 b c) = (dot3 a c) • b - (dot3 a b) • c := by
  funext i; fin_cases i <;> simp [cross3, dot3] <;> ring

/-- Scalar triple product cyclic symmetry `(a × b)ᵀ c = aᵀ (b × c)`. -/
lemma dot3_cross3_left {K : Type*} [CommRing K] (a b c : Fin 3 → K) :
    dot3 (cross3 a b) c = dot3 a (cross3 b c) := by
  simp [dot3, cross3]; ring

/-- Lagrange's identity `(a₁ᵀ b₁)(a₂ᵀ b₂) - (a₁ᵀ b₂)(a₂ᵀ b₁) = (a₁ × a₂)ᵀ (b₁ × b₂)`. -/
lemma lagrange_dot3_cross3 {K : Type*} [CommRing K] (a₁ a₂ b₁ b₂ : Fin 3 → K) :
    dot3 a₁ b₁ * dot3 a₂ b₂ - dot3 a₁ b₂ * dot3 a₂ b₁ =
      dot3 (cross3 a₁ a₂) (cross3 b₁ b₂) := by
  simp [dot3, cross3]; ring

/-- Over a field, `w ≠ 0` and `w × x = 0` imply `x ∈ K w` (valid unconditionally, even if `w` is
isotropic with `wᵀ w = 0`). -/
lemma cross3_eq_zero_imp_collinear {K : Type*} [Field K] {w x : Fin 3 → K}
    (hw : w ≠ 0) (hcr : cross3 w x = 0) :
    ∃ c : K, x = c • w := by
  have hc0 := congrFun hcr 0
  have hc1 := congrFun hcr 1
  have hc2 := congrFun hcr 2
  simp only [cross3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Pi.zero_apply] at hc0 hc1 hc2
  by_cases h0 : w 0 ≠ 0
  · refine ⟨x 0 * (w 0)⁻¹, ?_⟩
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, smul_eq_mul]
      rw [mul_assoc, inv_mul_cancel₀ h0, mul_one]
    · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
      have hrel : w 0 * x 1 = x 0 * w 1 := by linear_combination hc2
      calc x 1 = (w 0 * x 1) * (w 0)⁻¹ := by rw [mul_comm (w 0), mul_assoc, mul_inv_cancel₀ h0, mul_one]
        _ = x 0 * (w 0)⁻¹ * w 1 := by rw [hrel]; ring
    · simp only [Fin.reduceFinMk, Fin.isValue, Pi.smul_apply, smul_eq_mul]
      have hrel : w 0 * x 2 = x 0 * w 2 := by linear_combination -hc1
      calc x 2 = (w 0 * x 2) * (w 0)⁻¹ := by rw [mul_comm (w 0), mul_assoc, mul_inv_cancel₀ h0, mul_one]
        _ = x 0 * (w 0)⁻¹ * w 2 := by rw [hrel]; ring
  · push Not at h0
    by_cases h1 : w 1 ≠ 0
    · refine ⟨x 1 * (w 1)⁻¹, ?_⟩
      funext i
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, smul_eq_mul, h0, mul_zero]
        have hrel : w 1 * x 0 = 0 := by rw [h0] at hc2; linear_combination -hc2
        exact (mul_eq_zero.mp hrel).resolve_left h1
      · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
        rw [mul_assoc, inv_mul_cancel₀ h1, mul_one]
      · simp only [Fin.reduceFinMk, Fin.isValue, Pi.smul_apply, smul_eq_mul]
        have hrel : w 1 * x 2 = x 1 * w 2 := by linear_combination hc0
        calc x 2 = (w 1 * x 2) * (w 1)⁻¹ := by rw [mul_comm (w 1), mul_assoc, mul_inv_cancel₀ h1, mul_one]
          _ = x 1 * (w 1)⁻¹ * w 2 := by rw [hrel]; ring
    · push Not at h1
      have h2 : w 2 ≠ 0 := by
        intro h2
        apply hw
        funext i; fin_cases i <;> simp [h0, h1, h2]
      refine ⟨x 2 * (w 2)⁻¹, ?_⟩
      funext i
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, smul_eq_mul, h0, mul_zero]
        have hrel : w 2 * x 0 = 0 := by rw [h0] at hc1; linear_combination hc1
        exact (mul_eq_zero.mp hrel).resolve_left h2
      · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul, h1, mul_zero]
        have hrel : w 2 * x 1 = 0 := by rw [h1] at hc0; linear_combination -hc0
        exact (mul_eq_zero.mp hrel).resolve_left h2
      · simp only [Fin.reduceFinMk, Fin.isValue, Pi.smul_apply, smul_eq_mul]
        rw [mul_assoc, inv_mul_cancel₀ h2, mul_one]

/-- Explicit `2`-element basis `{b₀, b₁}` of `w⊥` for any `w ≠ 0` over an arbitrary field `F`
(without assuming `wᵀ w ≠ 0`), together with linear coordinate functionals `c₀, c₁` and
`b₀ × b₁ = s • w` (`s ≠ 0`). -/
lemma exists_perp_basis_of_ne_zero {F : Type*} [Field F] {w : Fin 3 → F} (hw : w ≠ 0) :
    ∃ (b₀ b₁ : Fin 3 → F) (c₀ c₁ : (Fin 3 → F) → F) (s : F),
      dot3 w b₀ = 0 ∧ dot3 w b₁ = 0 ∧ s ≠ 0 ∧ cross3 b₀ b₁ = s • w ∧
      (∀ x y : Fin 3 → F, c₀ (x + y) = c₀ x + c₀ y ∧ c₁ (x + y) = c₁ x + c₁ y) ∧
      (∀ (a : F) (x : Fin 3 → F), c₀ (a • x) = a * c₀ x ∧ c₁ (a • x) = a * c₁ x) ∧
      (∀ y : Fin 3 → F, dot3 w y = 0 → y = c₀ y • b₀ + c₁ y • b₁) := by
  by_cases h0 : w 0 ≠ 0
  · refine ⟨![-w 2, 0, w 0], ![w 1, -w 0, 0],
      fun y => (w 0)⁻¹ * y 2, fun y => -(w 0)⁻¹ * y 1, w 0,
      by simp [dot3]; ring, by simp [dot3]; ring, h0, ?_, ?_, ?_, ?_⟩
    · funext i; (fin_cases i <;> simp [cross3]); ring
    · intro x y; constructor <;> simp <;> ring
    · intro a x; constructor <;> simp <;> ring
    · intro y hy
      simp only [dot3] at hy
      funext i
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          Matrix.cons_val_zero]
        have hwy : w 1 * y 1 + w 2 * y 2 = -(w 0 * y 0) := by linear_combination hy
        calc y 0 = (w 0)⁻¹ * (w 0 * y 0) := by rw [← mul_assoc, inv_mul_cancel₀ h0, one_mul]
          _ = (w 0)⁻¹ * y 2 * -w 2 + -(w 0)⁻¹ * y 1 * w 1 := by
                linear_combination (w 0)⁻¹ * hwy
      · simp only [Fin.mk_one, Fin.isValue, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          Matrix.cons_val_one, Matrix.cons_val_zero, mul_zero, zero_add]
        calc y 1 = ((w 0)⁻¹ * w 0) * y 1 := by rw [inv_mul_cancel₀ h0, one_mul]
          _ = -(w 0)⁻¹ * y 1 * -w 0 := by ring
      · simp only [Fin.reduceFinMk, Fin.isValue, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          Matrix.cons_val, mul_zero, add_zero]
        calc y 2 = ((w 0)⁻¹ * w 0) * y 2 := by rw [inv_mul_cancel₀ h0, one_mul]
          _ = (w 0)⁻¹ * y 2 * w 0 := by ring
  · push Not at h0
    by_cases h1 : w 1 ≠ 0
    · refine ⟨![0, w 2, -w 1], ![w 1, -w 0, 0],
        fun y => -(w 1)⁻¹ * y 2, fun y => (w 1)⁻¹ * y 0, -w 1,
        by simp [dot3]; ring, by simp [dot3]; ring, neg_ne_zero.mpr h1, ?_, ?_, ?_, ?_⟩
      · funext i; (fin_cases i <;> simp [cross3]); ring
      · intro x y; constructor <;> simp <;> ring
      · intro a x; constructor <;> simp <;> ring
      · intro y hy
        simp only [dot3] at hy
        funext i
        fin_cases i
        · simp only [Fin.zero_eta, Fin.isValue, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
            Matrix.cons_val_zero, mul_zero, zero_add]
          calc y 0 = ((w 1)⁻¹ * w 1) * y 0 := by rw [inv_mul_cancel₀ h1, one_mul]
            _ = (w 1)⁻¹ * y 0 * w 1 := by ring
        · simp only [Fin.mk_one, Fin.isValue, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
            Matrix.cons_val_one, Matrix.cons_val_zero]
          have hwy : w 0 * y 0 + w 2 * y 2 = -(w 1 * y 1) := by linear_combination hy
          calc y 1 = (w 1)⁻¹ * (w 1 * y 1) := by rw [← mul_assoc, inv_mul_cancel₀ h1, one_mul]
            _ = -(w 1)⁻¹ * y 2 * w 2 + (w 1)⁻¹ * y 0 * -w 0 := by
                  linear_combination (w 1)⁻¹ * hwy
        · simp only [Fin.reduceFinMk, Fin.isValue, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
            Matrix.cons_val, mul_zero, add_zero]
          calc y 2 = ((w 1)⁻¹ * w 1) * y 2 := by rw [inv_mul_cancel₀ h1, one_mul]
            _ = -(w 1)⁻¹ * y 2 * -w 1 := by ring
    · push Not at h1
      have h2 : w 2 ≠ 0 := by
        intro h2; apply hw; funext i; fin_cases i <;> simp [h0, h1, h2]
      refine ⟨![-w 2, 0, w 0], ![0, w 2, -w 1],
        fun y => -(w 2)⁻¹ * y 0, fun y => (w 2)⁻¹ * y 1, -w 2,
        by simp [dot3]; ring, by simp [dot3]; ring, neg_ne_zero.mpr h2, ?_, ?_, ?_, ?_⟩
      · funext i; (fin_cases i <;> simp [cross3]); ring
      · intro x y; constructor <;> simp <;> ring
      · intro a x; constructor <;> simp <;> ring
      · intro y hy
        simp only [dot3] at hy
        funext i
        fin_cases i
        · simp only [Fin.zero_eta, Fin.isValue, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
            Matrix.cons_val_zero, mul_zero, add_zero]
          calc y 0 = ((w 2)⁻¹ * w 2) * y 0 := by rw [inv_mul_cancel₀ h2, one_mul]
            _ = -(w 2)⁻¹ * y 0 * -w 2 := by ring
        · simp only [Fin.mk_one, Fin.isValue, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
            Matrix.cons_val_one, Matrix.cons_val_zero, mul_zero, zero_add]
          calc y 1 = ((w 2)⁻¹ * w 2) * y 1 := by rw [inv_mul_cancel₀ h2, one_mul]
            _ = (w 2)⁻¹ * y 1 * w 2 := by ring
        · simp only [Fin.reduceFinMk, Fin.isValue, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
            Matrix.cons_val]
          have hwy : w 0 * y 0 + w 1 * y 1 = -(w 2 * y 2) := by linear_combination hy
          calc y 2 = (w 2)⁻¹ * (w 2 * y 2) := by rw [← mul_assoc, inv_mul_cancel₀ h2, one_mul]
            _ = -(w 2)⁻¹ * y 0 * w 0 + (w 2)⁻¹ * y 1 * -w 1 := by
                  linear_combination (w 2)⁻¹ * hwy

/-- Right-inverse implies left-inverse for matrices indexed by equivalent finite types over any
commutative ring (`A * B = 1 → B * A = 1`). -/
lemma matrix_mul_eq_one_comm_of_equiv {R m n : Type*} [CommRing R]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (e : m ≃ n) {A : Matrix m n R} {B : Matrix n m R} (hAB : A * B = 1) :
    B * A = 1 := by
  let A' : Matrix m m R := A.submatrix id e
  let B' : Matrix m m R := B.submatrix e id
  have hAB' : A' * B' = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [A', B', Matrix.submatrix_apply, id_eq]
    rw [e.sum_comp (fun k => A i k * B k j)]
    rw [← Matrix.mul_apply, hAB]
  have hdet : A'.det * B'.det = 1 := by
    rw [← Matrix.det_mul, hAB', Matrix.det_one]
  let Ai : Matrix m m R := B'.det • A'.adjugate
  have hAi : Ai * A' = 1 := by
    dsimp [Ai]
    rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, mul_comm B'.det A'.det, hdet, one_smul]
  have hB'_eq : B' = Ai := by
    calc B' = (Ai * A') * B' := by rw [hAi, Matrix.one_mul]
      _ = Ai * (A' * B') := by rw [Matrix.mul_assoc]
      _ = Ai := by rw [hAB', Matrix.mul_one]
  have hBA' : B' * A' = 1 := by rw [hB'_eq, hAi]
  ext i j
  have hent := congrFun (congrFun hBA' (e.symm i)) (e.symm j)
  rw [Matrix.mul_apply] at hent ⊢
  simp only [A', B', Matrix.submatrix_apply, id_eq, Equiv.apply_symm_apply] at hent
  simpa [Matrix.one_apply, e.symm.injective.eq_iff] using hent

/-! ## Section 1: Step 1 — 18×18 Koszul Flattening and Border-Rank Lower Bound 9 -/

/-- `9`-element index type `(Fin 3) × (Fin 3)` for `3 × 3` matrix blocks `V ⊗ V`. -/
abbrev Idx9 := Fin 3 × Fin 3

/-- `18`-element index type `(Fin 2) × (Fin 3 × Fin 3)` for `(E ⊗ V) ⊗ V ≅ K¹⁸`. -/
abbrev Idx18 := Fin 2 × Idx9

/-- Coefficient array `c` of the `18 × 18` Koszul flattening `X_C^{∧1}` on
`(K² ⊗ K³) ⊗ (K² ⊗ K³) ⊗ K³` (Equation (3.1) of Paper 1). -/
def koszulCoeff (K : Type*) [CommRing K] :
    Idx18 → Idx18 → (Fin 2 × Fin 3) → (Fin 2 × Fin 3) → Fin 3 → K :=
  fun row col p q k =>
    if p = (col.1, col.2.1) ∧ q = (row.1, row.2.1) then eps3 K k col.2.2 row.2.2 else 0

lemma koszulFlat_apply {K R : Type*} [CommRing K] [CommRing R]
    (φ : K →+* R) (T : Tensor3 R (Fin 2 × Fin 3) (Fin 2 × Fin 3) (Fin 3))
    (row col : Idx18) :
    linearFlattening φ (koszulCoeff K) T row col =
      ∑ k : Fin 3, φ (eps3 K k col.2.2 row.2.2) * T (col.1, col.2.1) (row.1, row.2.1) k := by
  simp only [linearFlattening, koszulCoeff]
  have hinner : ∀ p q : Fin 2 × Fin 3,
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

lemma map_eps3 {K R : Type*} [CommRing K] [CommRing R] (φ : K →+* R) (i j k : Fin 3) :
    φ (eps3 K i j k) = eps3 R i j k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [eps3]

lemma sum_eps3_mul_eq_cross3_stdBasis {R : Type*} [CommRing R] (w : Fin 3 → R) (m l : Fin 3) :
    (∑ k : Fin 3, eps3 R k m l * w k) = cross3 w (stdBasis3 m) l := by
  fin_cases m <;> fin_cases l <;> simp [Fin.sum_univ_three, eps3, cross3, stdBasis3]

/-- Explicit factorization of `X_C^{∧1}(u ⊗ v ⊗ w)` through `Fin 2` over any field `F`:
`linearFlattening φ (koszulCoeff K) (u ⊗ v ⊗ w) = A * B` with `A : Matrix Idx18 (Fin 2) F` and
`B : Matrix (Fin 2) Idx18 F`, together with explicit properties of the columns of `A`. -/
lemma koszul_rankOne_factor {K F : Type*} [CommRing K] [Field F]
    (φ : K →+* F) (u v : Fin 2 × Fin 3 → F) (w : Fin 3 → F) :
    ∃ (b₀ b₁ : Fin 3 → F) (c₀ c₁ : (Fin 3 → F) → F),
      dot3 w b₀ = 0 ∧ dot3 w b₁ = 0 ∧
      (w = 0 → b₀ = 0 ∧ b₁ = 0) ∧
      (w ≠ 0 → ∀ y : Fin 3 → F, dot3 w y = 0 → y = c₀ y • b₀ + c₁ y • b₁) ∧
      linearFlattening φ (koszulCoeff K) (rankOneTensor u v w) =
        (Matrix.of fun (row : Idx18) (t : Fin 2) =>
          v (row.1, row.2.1) * (if t = 0 then b₀ row.2.2 else b₁ row.2.2)) *
        (Matrix.of fun (t : Fin 2) (col : Idx18) =>
          u (col.1, col.2.1) *
            (if t = 0 then c₀ (cross3 w (stdBasis3 col.2.2))
             else c₁ (cross3 w (stdBasis3 col.2.2)))) := by
  by_cases hw : w = 0
  · refine ⟨0, 0, fun _ => 0, fun _ => 0, dot3_zero_right w, dot3_zero_right w,
      fun _ => ⟨rfl, rfl⟩, fun hne => absurd hw hne, ?_⟩
    ext row col
    rw [koszulFlat_apply, Matrix.mul_apply]
    simp [rankOneTensor, hw]
  · obtain ⟨b₀, b₁, c₀, c₁, _, hb₀, hb₁, _, _, _, _, hspan⟩ := exists_perp_basis_of_ne_zero hw
    refine ⟨b₀, b₁, c₀, c₁, hb₀, hb₁, fun h0 => absurd h0 hw, fun _ => hspan, ?_⟩
    ext row col
    rw [koszulFlat_apply, Matrix.mul_apply]
    simp only [Fin.sum_univ_two, Matrix.of_apply, Fin.isValue, ↓reduceIte, one_ne_zero]
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

/-- Every pure tensor `u ⊗ v ⊗ w` over any field `F` (including `RatFunc K`) maps under the
Koszul flattening to a `18 × 18` matrix of rank at most `2`. -/
theorem koszul_rankOne_le_two {K F : Type*} [CommRing K] [Field F]
    (φ : K →+* F) (u v : Fin 2 × Fin 3 → F) (w : Fin 3 → F) :
    (linearFlattening φ (koszulCoeff K) (rankOneTensor u v w)).rank ≤ 2 := by
  obtain ⟨b₀, b₁, c₀, c₁, _, _, _, _, hfac⟩ := koszul_rankOne_factor φ u v w
  let A : Matrix Idx18 (Fin 2) F := Matrix.of fun row t =>
    v (row.1, row.2.1) * (if t = 0 then b₀ row.2.2 else b₁ row.2.2)
  let B : Matrix (Fin 2) Idx18 F := Matrix.of fun t col =>
    u (col.1, col.2.1) *
      (if t = 0 then c₀ (cross3 w (stdBasis3 col.2.2))
       else c₁ (cross3 w (stdBasis3 col.2.2)))
  change (linearFlattening φ (koszulCoeff K) (rankOneTensor u v w)).rank ≤ 2
  rw [hfac]
  change (A * B).rank ≤ 2
  have hsub : LinearMap.range (A * B).mulVecLin ≤ LinearMap.range A.mulVecLin := by
    rintro _ ⟨x, rfl⟩
    exact ⟨B.mulVecLin x, by simp [Matrix.mulVec_mulVec]⟩
  calc (A * B).rank ≤ Module.finrank F (LinearMap.range A.mulVecLin) :=
        Submodule.finrank_mono hsub
    _ ≤ Module.finrank F (Fin 2 → F) := LinearMap.finrank_range_le A.mulVecLin
    _ = 2 := by simp

/-- The `9 × 9` block `Φ : Mat₃(K) → Mat₃(K)`, `Φ(A) = (Tr A) I₃ - Aᵀ` (Equation (3.2)). -/
def koszulPhi9 (K : Type*) [CommRing K] : Matrix Idx9 Idx9 K :=
  fun jl im =>
    (if im.1 = im.2 ∧ jl.1 = jl.2 then 1 else 0) -
    (if im.1 = jl.2 ∧ im.2 = jl.1 then 1 else 0)

/-- Explicit inverse `Φ⁻¹(B) = (1/2)(Tr B) I₃ - Bᵀ` (Equation (3.4)). -/
def koszulPhi9Inv (K : Type*) [Field K] : Matrix Idx9 Idx9 K :=
  fun jl im =>
    (if im.1 = im.2 ∧ jl.1 = jl.2 then (2 : K)⁻¹ else 0) -
    (if im.1 = jl.2 ∧ im.2 = jl.1 then 1 else 0)

lemma koszulFlat_I2_eps3_eq {K : Type*} [CommRing K] :
    linearFlattening (RingHom.id K) (koszulCoeff K) (I2_eps3 K) =
      fun row col => if row.1 = col.1 then koszulPhi9 K row.2 col.2 else 0 := by
  ext ⟨b, j, l⟩ ⟨a, i, m⟩
  rw [koszulFlat_apply]
  simp only [RingHom.id_apply, I2_eps3]
  by_cases hba : a = b
  · subst hba
    simp only [↓reduceIte, koszulPhi9]
    fin_cases j <;> fin_cases l <;> fin_cases i <;> fin_cases m <;>
      simp [Fin.sum_univ_three, eps3]
  · have hne : b ≠ a := Ne.symm hba
    simp [hba, hne]

lemma koszulPhi9_mul_inv {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) :
    koszulPhi9 K * koszulPhi9Inv K = 1 ∧ koszulPhi9Inv K * koszulPhi9 K = 1 := by
  constructor
  · ext ⟨j, l⟩ ⟨i, m⟩
    rw [Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type]
    fin_cases j <;> fin_cases l <;> fin_cases i <;> fin_cases m <;>
      simp [Fin.sum_univ_three, koszulPhi9, koszulPhi9Inv] <;>
      · field_simp [h2]; ring
  · ext ⟨j, l⟩ ⟨i, m⟩
    rw [Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type]
    fin_cases j <;> fin_cases l <;> fin_cases i <;> fin_cases m <;>
      simp [Fin.sum_univ_three, koszulPhi9, koszulPhi9Inv] <;>
      · field_simp [h2]; ring

/-- Explicit block decomposition equivalence `Idx9 ≃ Fin 3 ⊕ (Fin 2 ⊕ (Fin 2 ⊕ Fin 2))` grouping
diagonal pairs `(0,0),(1,1),(2,2)` and off-diagonal transpose pairs `{(0,1),(1,0)}`,
`{(0,2),(2,0)}`, `{(1,2),(2,1)}`. -/
def blockIdx9Equiv : Fin 3 ⊕ (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) ≃ Idx9 where
  toFun
    | .inl 0 => (0, 0)
    | .inl 1 => (1, 1)
    | .inl 2 => (2, 2)
    | .inr (.inl 0) => (0, 1)
    | .inr (.inl 1) => (1, 0)
    | .inr (.inr (.inl 0)) => (0, 2)
    | .inr (.inr (.inl 1)) => (2, 0)
    | .inr (.inr (.inr 0)) => (1, 2)
    | .inr (.inr (.inr 1)) => (2, 1)
  invFun
    | (0, 0) => .inl 0
    | (1, 1) => .inl 1
    | (2, 2) => .inl 2
    | (0, 1) => .inr (.inl 0)
    | (1, 0) => .inr (.inl 1)
    | (0, 2) => .inr (.inr (.inl 0))
    | (2, 0) => .inr (.inr (.inl 1))
    | (1, 2) => .inr (.inr (.inr 0))
    | (2, 1) => .inr (.inr (.inr 1))
  left_inv x := by
    rcases x with i | (i | (i | i)) <;> fin_cases i <;> rfl
  right_inv p := by
    rcases p with ⟨i, j⟩; fin_cases i <;> fin_cases j <;> rfl

/-- `det(Φ) = 2 · (-1)³ = -2` over any commutative ring `K` (Equation (3.3)). -/
theorem det_koszulPhi9 (K : Type*) [CommRing K] : (koszulPhi9 K).det = -2 := by
  rw [← Matrix.det_reindex_self blockIdx9Equiv.symm (koszulPhi9 K)]
  let D3 : Matrix (Fin 3) (Fin 3) K := ![![0, 1, 1], ![1, 0, 1], ![1, 1, 0]]
  let S2 : Matrix (Fin 2) (Fin 2) K := ![![0, -1], ![-1, 0]]
  have hblk : Matrix.reindex blockIdx9Equiv.symm blockIdx9Equiv.symm (koszulPhi9 K) =
      Matrix.fromBlocks D3 0 0
        (Matrix.fromBlocks S2 0 0 (Matrix.fromBlocks S2 0 0 S2)) := by
    ext x y
    rcases x with i | (i | (i | i)) <;> rcases y with j | (j | (j | j)) <;>
      fin_cases i <;> fin_cases j <;>
      simp [blockIdx9Equiv, koszulPhi9, D3, S2, Matrix.fromBlocks]
  rw [hblk, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_fromBlocks_zero₂₁]
  have hD3 : D3.det = 2 := by rw [Matrix.det_fin_three]; simp [D3]; ring
  have hS2 : S2.det = -1 := by rw [Matrix.det_fin_two]; simp [S2]
  rw [hD3, hS2]
  ring

/-- `det(T_C^{∧1}) = (-2)² = 4` over any commutative ring `K` (Step 1 of Theorem 1.1). -/
theorem det_koszulFlat_I2_eps3 (K : Type*) [CommRing K] :
    (linearFlattening (RingHom.id K) (koszulCoeff K) (I2_eps3 K)).det = 4 := by
  let e18 : Idx9 ⊕ Idx9 ≃ Idx18 :=
    { toFun := fun s => match s with | .inl x => (0, x) | .inr x => (1, x)
      invFun := fun p => if p.1 = 0 then .inl p.2 else .inr p.2
      left_inv := fun s => by rcases s with x | x <;> rfl
      right_inv := fun ⟨b, x⟩ => by fin_cases b <;> rfl }
  rw [← Matrix.det_reindex_self e18.symm]
  have hblk : Matrix.reindex e18.symm e18.symm
      (linearFlattening (RingHom.id K) (koszulCoeff K) (I2_eps3 K)) =
      Matrix.fromBlocks (koszulPhi9 K) 0 0 (koszulPhi9 K) := by
    ext x y
    change linearFlattening (RingHom.id K) (koszulCoeff K) (I2_eps3 K) (e18 x) (e18 y) =
      Matrix.fromBlocks (koszulPhi9 K) 0 0 (koszulPhi9 K) x y
    rw [koszulFlat_I2_eps3_eq]
    rcases x with x | x <;> rcases y with y | y <;>
      simp [e18, Matrix.fromBlocks]
  rw [hblk, Matrix.det_fromBlocks_zero₂₁, det_koszulPhi9]
  ring

/-- **Theorem 1.1, Step 1 (`I₂ ⊗₁,₂ ε₃` formal border-rank lower bound `9`):**
Over every field `K` with `char K ≠ 2`, `brk_K(I₂ ⊗₁,₂ ε₃) ≥ 9`. -/
theorem I2_eps3_borderRank_ge_nine {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) :
    (∀ r : ℕ, HasFormalBorderRankLe (I2_eps3 K) r → 9 ≤ r) ∧
    ¬ HasFormalBorderRankLe (I2_eps3 K) 8 := by
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hdet : ((linearFlattening (RingHom.id K) (koszulCoeff K) (I2_eps3 K)).submatrix
      id id).det ≠ 0 := by
    simpa [det_koszulFlat_I2_eps3] using h4
  have hge : ∀ r : ℕ, HasFormalBorderRankLe (I2_eps3 K) r → 9 ≤ r := by
    intro r hr
    have h18 := formalBorderRank_flattening_lower_bound (koszulCoeff K) 2
      (fun u v w => koszul_rankOne_le_two (algebraMap K (RatFunc K)) u v w) id id hdet hr
    have hcard : Fintype.card Idx18 = 18 := by decide
    rw [hcard] at h18
    omega
  exact ⟨hge, fun h8 => absurd (hge 8 h8) (by omega)⟩

/-- Transfer of the Koszul formal border-rank lower bound `9` to `symEps3 K` and `T_RCB K b`. -/
theorem T_RCB_borderRank_ge_nine {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {b : K} (hb : b ≠ 0) :
    (∀ r : ℕ, HasFormalBorderRankLe (T_RCB K b) r → 9 ≤ r) ∧
    (∀ r : ℕ, HasSym12FormalBorderRankLe (T_RCB K b) r → 9 ≤ r) ∧
    ¬ HasFormalBorderRankLe (T_RCB K b) 8 := by
  have heq := T_RCB_equiv_I2_eps3 h2 h3 hb
  have hI := (I2_eps3_borderRank_ge_nine h2).1
  have hge : ∀ r : ℕ, HasFormalBorderRankLe (T_RCB K b) r → 9 ≤ r :=
    fun r hr => hI r ((heq.hasFormalBorderRankLe_iff r).mp hr)
  exact ⟨hge, fun r hr => hge r hr.toFormalBorderRankLe, fun h8 => absurd (hge 8 h8) (by omega)⟩

/-! ## Section 2: Step 2 — Universal `(1,2)`-Symmetric Formal Border Rank 9 -/

/-- Explicit `9`-term `(1,2)`-symmetric formal border-rank degeneration of `symEps3 K` over any
field `K` with `char K ≠ 2` (Step 2 of Theorem 1.1: `t = (-1, 0, 1)`, `c = (1/2, -1, 1/2)`). -/
theorem symEps3_hasSym12FormalBorderRankLe_nine {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) :
    HasSym12FormalBorderRankLe (symEps3 K) 9 := by
  let tVal : Fin 3 → K := ![-1, 0, 1]
  let cVal : Fin 3 → K := ![(2 : K)⁻¹, -1, (2 : K)⁻¹]
  let cyc1 : Fin 3 → Fin 3 := ![1, 2, 0]
  let cyc2 : Fin 3 → Fin 3 := ![2, 0, 1]
  have hstep2_m0 : ∀ x y : K,
      ∑ m : Fin 3, (cVal m * x - cVal m * tVal m * y) = 0 := by
    intro x y
    simp [Fin.sum_univ_three, cVal, tVal]
    field_simp [h2]; ring
  have hstep2_m2 : ∀ u₂ v₂ x y : K,
      ∑ m : Fin 3, -(u₂ * tVal m + v₂ * tVal m ^ 2) * (cVal m * x - cVal m * tVal m * y) =
        u₂ * y - v₂ * x := by
    intro u₂ v₂ x y
    simp [Fin.sum_univ_three, cVal, tVal]
    field_simp [h2]; ring
  let e9 : Fin 9 ≃ Fin 3 × Fin 3 :=
    Fintype.equivOfCardEq (by decide : Fintype.card (Fin 9) = Fintype.card (Fin 3 × Fin 3))
  let A_jm : (Fin 3 × Fin 3) → (Fin 2 × Fin 3) → K := fun ⟨j, m⟩ p =>
    if p.1 = 1 then
      (if p.2 = cyc1 j then (1 : K) else 0) * tVal m +
      (if p.2 = cyc2 j then (1 : K) else 0) * tVal m ^ 2
    else 0
  let B_jm : (Fin 3 × Fin 3) → (Fin 2 × Fin 3) → K := fun ⟨j, _⟩ p =>
    if p.1 = 0 ∧ p.2 = j then 1 else 0
  let W_jm : (Fin 3 × Fin 3) → Fin 3 → K := fun ⟨j, m⟩ k =>
    cVal m * (if k = cyc1 j then 1 else 0) -
    cVal m * tVal m * (if k = cyc2 j then 1 else 0)
  let A_pos : Fin 9 → (Fin 2 × Fin 3) → K := fun idx => A_jm (e9 idx)
  let B_neg : Fin 9 → (Fin 2 × Fin 3) → K := fun idx => B_jm (e9 idx)
  let W₀ : Fin 9 → Fin 3 → K := fun idx => W_jm (e9 idx)
  refine ⟨2,
    fun idx p => X ^ 2 * C (A_pos idx p) - C (B_neg idx p),
    fun idx k => C (W₀ idx k),
    fun p q k => X * C (∑ idx : Fin 9, A_pos idx p * A_pos idx q * W₀ idx k),
    fun p q k => ?_⟩
  have hterm : ∀ idx : Fin 9,
      (X ^ 2 * C (A_pos idx p) - C (B_neg idx p)) *
        (X ^ 2 * C (A_pos idx q) - C (B_neg idx q)) * C (W₀ idx k) =
      C (B_neg idx p * B_neg idx q * W₀ idx k) +
      C (-(B_neg idx p * A_pos idx q + A_pos idx p * B_neg idx q) * W₀ idx k) * X ^ 2 +
      C (A_pos idx p * A_pos idx q * W₀ idx k) * X ^ 4 := by
    intro idx
    simp only [map_neg, map_add, map_mul]
    ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [← Finset.sum_mul, ← map_sum]
  have hdeg0 : (∑ idx : Fin 9, B_neg idx p * B_neg idx q * W₀ idx k) = 0 := by
    dsimp [B_neg, W₀]
    rw [e9.sum_comp (fun jm => B_jm jm p * B_jm jm q * W_jm jm k), Fintype.sum_prod_type]
    refine Finset.sum_eq_zero fun j _ => ?_
    calc ∑ m : Fin 3, B_jm (j, m) p * B_jm (j, m) q * W_jm (j, m) k
        = (B_jm (j, 0) p * B_jm (j, 0) q) *
            ∑ m : Fin 3,
              (cVal m * (if k = cyc1 j then 1 else 0) -
               cVal m * tVal m * (if k = cyc2 j then 1 else 0)) := by
              rw [Finset.mul_sum]
      _ = 0 := by rw [hstep2_m0, mul_zero]
  have hdeg2 : (∑ idx : Fin 9,
      -(B_neg idx p * A_pos idx q + A_pos idx p * B_neg idx q) * W₀ idx k) =
      symEps3 K p q k := by
    dsimp [A_pos, B_neg, W₀]
    rw [e9.sum_comp (fun jm => -(B_jm jm p * A_jm jm q + A_jm jm p * B_jm jm q) * W_jm jm k),
      Fintype.sum_prod_type]
    rcases p with ⟨bp, ip⟩
    rcases q with ⟨bq, iq⟩
    fin_cases bp <;> fin_cases bq
    · simp [B_jm, A_jm, symEps3]
    · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, B_jm, A_jm, W_jm,
        zero_ne_one, one_ne_zero, true_and, false_and, ↓reduceIte, zero_mul, add_zero]
      have hj : ∀ j : Fin 3,
          (∑ m : Fin 3,
            -((if ip = j then (1 : K) else 0) *
              ((if iq = cyc1 j then 1 else 0) * tVal m +
               (if iq = cyc2 j then 1 else 0) * tVal m ^ 2)) *
            (cVal m * (if k = cyc1 j then 1 else 0) -
             cVal m * tVal m * (if k = cyc2 j then 1 else 0))) =
          (if ip = j then 1 else 0) *
            ((if iq = cyc1 j then 1 else 0) * (if k = cyc2 j then 1 else 0) -
             (if iq = cyc2 j then 1 else 0) * (if k = cyc1 j then 1 else 0)) := by
        intro j
        by_cases hip : ip = j
        · simp only [hip, ↓reduceIte, one_mul]
          exact hstep2_m2 _ _ _ _
        · simp [hip]
      simp_rw [hj]
      fin_cases ip <;> fin_cases iq <;> fin_cases k <;>
        simp [cyc1, cyc2, symEps3, eps3]
    · simp only [Fin.mk_one, Fin.zero_eta, Fin.isValue, B_jm, A_jm, W_jm,
        zero_ne_one, one_ne_zero, true_and, false_and, ↓reduceIte, mul_zero, zero_add]
      have hj : ∀ j : Fin 3,
          (∑ m : Fin 3,
            -(((if ip = cyc1 j then 1 else 0) * tVal m +
               (if ip = cyc2 j then 1 else 0) * tVal m ^ 2) *
              (if iq = j then (1 : K) else 0)) *
            (cVal m * (if k = cyc1 j then 1 else 0) -
             cVal m * tVal m * (if k = cyc2 j then 1 else 0))) =
          (if iq = j then 1 else 0) *
            ((if ip = cyc1 j then 1 else 0) * (if k = cyc2 j then 1 else 0) -
             (if ip = cyc2 j then 1 else 0) * (if k = cyc1 j then 1 else 0)) := by
        intro j
        by_cases hiq : iq = j
        · simp only [hiq, ↓reduceIte, mul_one, one_mul]
          exact hstep2_m2 _ _ _ _
        · simp [hiq]
      simp_rw [hj]
      fin_cases ip <;> fin_cases iq <;> fin_cases k <;>
        simp [cyc1, cyc2, symEps3, eps3]
    · simp [B_jm, A_jm, symEps3]
  rw [hdeg0, hdeg2, map_zero, zero_add]
  ring

/-- **Proposition 1.3 / Theorem 1.1, Step 2 (`T_RCB` universal formal border rank 9):**
Over every field `K` with `char K ≠ 2, 3` and `b ≠ 0`, both the `(1,2)`-symmetric and ordinary
formal border rank of `T_RCB K b` equal `9`. -/
theorem T_RCB_hasSym12FormalBorderRankLe_nine {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {b : K} (hb : b ≠ 0) :
    HasSym12FormalBorderRankLe (T_RCB K b) 9 ∧ HasFormalBorderRankLe (T_RCB K b) 9 := by
  have hcong := T_RCB_sym12Congruent_symEps3 h2 h3 hb
  have hsym :=
    (hcong.hasSym12FormalBorderRankLe_iff 9).mpr (symEps3_hasSym12FormalBorderRankLe_nine h2)
  exact ⟨hsym, hsym.toFormalBorderRankLe⟩

/-! ## Section 3: Step 3 — Explicit 9-Term Hesse Decomposition When `-3` is a Square -/

/-- Explicit `9`-term `(1,2)`-symmetric Hesse decomposition of `symEps3 K` whenever
`IsSquare (-3 : K)` (`char K ≠ 2, 3`, Step 3 of Theorem 1.1). -/
theorem symEps3_hasSym12RankLe_nine_of_isSquare_neg_three {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (hsq : IsSquare (-3 : K)) :
    HasSym12RankLe (symEps3 K) 9 := by
  rcases hsq with ⟨s, hs⟩
  have hs2 : s ^ 2 = -3 := by rw [sq, ← hs]
  let ω : K := (-1 + s) * (2 : K)⁻¹
  have hω_quad : ω ^ 2 + ω + 1 = 0 := by
    dsimp [ω]
    field_simp [h2]
    linear_combination hs2
  let αVal : Fin 3 → K := ![1, ω, -ω - 1]
  let αSq : Fin 3 → K := ![1, -ω - 1, ω]
  let cyc1 : Fin 3 → Fin 3 := ![1, 2, 0]
  let cyc2 : Fin 3 → Fin 3 := ![2, 0, 1]
  have hhesse_m0 : ∀ x y : K,
      ∑ m : Fin 3, (3 : K)⁻¹ * (x * αVal m - y * αSq m) = 0 := by
    intro x y
    simp [Fin.sum_univ_three, αVal, αSq]
    ring
  have hhesse_m1 : ∀ u₂ v₂ x y : K,
      ∑ m : Fin 3, -(u₂ * αVal m + v₂ * αSq m) * ((3 : K)⁻¹ * (x * αVal m - y * αSq m)) =
        u₂ * y - v₂ * x := by
    intro u₂ v₂ x y
    simp only [Fin.sum_univ_three, αVal, αSq, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val]
    field_simp [h3]
    linear_combination -2 * (u₂ - v₂) * (x + y) * hω_quad
  have hhesse_m2 : ∀ u₁ v₁ u₂ v₂ x y : K,
      ∑ m : Fin 3,
        (u₁ * αVal m + v₁ * αSq m) * (u₂ * αVal m + v₂ * αSq m) *
          ((3 : K)⁻¹ * (x * αVal m - y * αSq m)) =
        u₁ * u₂ * x - v₁ * v₂ * y := by
    intro u₁ v₁ u₂ v₂ x y
    simp only [Fin.sum_univ_three, αVal, αSq, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val]
    field_simp [h3]
    linear_combination
      (-3 * u₁ * u₂ * x - u₁ * u₂ * y + u₁ * v₂ * x - u₁ * v₂ * y +
       v₁ * u₂ * x - v₁ * u₂ * y + v₁ * v₂ * x + 3 * v₁ * v₂ * y) * hω_quad
  let e9 : Fin 9 ≃ Fin 3 × Fin 3 :=
    Fintype.equivOfCardEq (by decide : Fintype.card (Fin 9) = Fintype.card (Fin 3 × Fin 3))
  let L_jm : (Fin 3 × Fin 3) → (Fin 2 × Fin 3) → K := fun ⟨j, m⟩ p =>
    if p.1 = 0 then
      if p.2 = j then -1 else 0
    else
      (if p.2 = cyc1 j then (1 : K) else 0) * αVal m +
      (if p.2 = cyc2 j then (1 : K) else 0) * αSq m
  let W_jm : (Fin 3 × Fin 3) → Fin 3 → K := fun ⟨j, m⟩ k =>
    (3 : K)⁻¹ *
      ((if k = cyc1 j then (1 : K) else 0) * αVal m -
       (if k = cyc2 j then (1 : K) else 0) * αSq m)
  refine ⟨fun idx => L_jm (e9 idx), fun idx => W_jm (e9 idx), fun p q k => ?_⟩
  rw [e9.sum_comp (fun jm => L_jm jm p * L_jm jm q * W_jm jm k), Fintype.sum_prod_type]
  symm
  rcases p with ⟨bp, ip⟩
  rcases q with ⟨bq, iq⟩
  fin_cases bp <;> fin_cases bq
  · simp only [Fin.zero_eta, Fin.isValue, L_jm, W_jm, ↓reduceIte, symEps3, zero_ne_one, and_false]
    refine Finset.sum_eq_zero fun j _ => ?_
    calc ∑ m : Fin 3,
          (if ip = j then (-1 : K) else 0) * (if iq = j then (-1 : K) else 0) *
            ((3 : K)⁻¹ * ((if k = cyc1 j then 1 else 0) * αVal m -
                          (if k = cyc2 j then 1 else 0) * αSq m))
        = ((if ip = j then (-1 : K) else 0) * (if iq = j then (-1 : K) else 0)) *
            ∑ m : Fin 3,
              (3 : K)⁻¹ * ((if k = cyc1 j then 1 else 0) * αVal m -
                           (if k = cyc2 j then 1 else 0) * αSq m) := by
              rw [Finset.mul_sum]
      _ = 0 := by rw [hhesse_m0, mul_zero]
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, L_jm, W_jm, one_ne_zero, ↓reduceIte]
    have hj : ∀ j : Fin 3,
        (∑ m : Fin 3,
          (if ip = j then (-1 : K) else 0) *
          ((if iq = cyc1 j then 1 else 0) * αVal m + (if iq = cyc2 j then 1 else 0) * αSq m) *
          ((3 : K)⁻¹ * ((if k = cyc1 j then 1 else 0) * αVal m -
                        (if k = cyc2 j then 1 else 0) * αSq m))) =
        (if ip = j then 1 else 0) *
          ((if iq = cyc1 j then 1 else 0) * (if k = cyc2 j then 1 else 0) -
           (if iq = cyc2 j then 1 else 0) * (if k = cyc1 j then 1 else 0)) := by
      intro j
      by_cases hip : ip = j
      · simp only [hip, ↓reduceIte, neg_one_mul, one_mul]
        exact hhesse_m1 _ _ _ _
      · simp [hip]
    simp_rw [hj]
    fin_cases ip <;> fin_cases iq <;> fin_cases k <;>
      simp [cyc1, cyc2, symEps3, eps3]
  · simp only [Fin.mk_one, Fin.zero_eta, Fin.isValue, L_jm, W_jm, one_ne_zero, ↓reduceIte]
    have hj : ∀ j : Fin 3,
        (∑ m : Fin 3,
          ((if ip = cyc1 j then 1 else 0) * αVal m + (if ip = cyc2 j then 1 else 0) * αSq m) *
          (if iq = j then (-1 : K) else 0) *
          ((3 : K)⁻¹ * ((if k = cyc1 j then 1 else 0) * αVal m -
                        (if k = cyc2 j then 1 else 0) * αSq m))) =
        (if iq = j then 1 else 0) *
          ((if ip = cyc1 j then 1 else 0) * (if k = cyc2 j then 1 else 0) -
           (if ip = cyc2 j then 1 else 0) * (if k = cyc1 j then 1 else 0)) := by
      intro j
      by_cases hiq : iq = j
      · simp only [hiq, ↓reduceIte, mul_neg, mul_one, one_mul]
        exact hhesse_m1 _ _ _ _
      · simp [hiq]
    simp_rw [hj]
    fin_cases ip <;> fin_cases iq <;> fin_cases k <;>
      simp [cyc1, cyc2, symEps3, eps3]
  · simp only [Fin.mk_one, Fin.isValue, L_jm, W_jm]
    have hj : ∀ j : Fin 3,
        (∑ m : Fin 3,
          (if (1 : Fin 2) = 0 then if ip = j then (-1 : K) else 0
           else (if ip = cyc1 j then 1 else 0) * αVal m + (if ip = cyc2 j then 1 else 0) * αSq m) *
          (if (1 : Fin 2) = 0 then if iq = j then (-1 : K) else 0
           else (if iq = cyc1 j then 1 else 0) * αVal m + (if iq = cyc2 j then 1 else 0) * αSq m) *
          ((3 : K)⁻¹ * ((if k = cyc1 j then 1 else 0) * αVal m -
                        (if k = cyc2 j then 1 else 0) * αSq m))) =
        (if ip = cyc1 j then 1 else 0) * (if iq = cyc1 j then 1 else 0) *
          (if k = cyc1 j then 1 else 0) -
        (if ip = cyc2 j then 1 else 0) * (if iq = cyc2 j then 1 else 0) *
          (if k = cyc2 j then 1 else 0) := by
      intro j
      simp only [one_ne_zero, ↓reduceIte]
      exact hhesse_m2 _ _ _ _ _ _
    simp_rw [hj]
    fin_cases ip <;> fin_cases iq <;> fin_cases k <;>
      simp [Fin.sum_univ_three, cyc1, cyc2, symEps3]

/-- **Proposition 1.3 / Theorem 1.1, Step 3 (`T_RCB` symmetric rank 9 when `-3` is a square):**
Whenever `IsSquare (-3 : K)` (`char K ≠ 2, 3`, `b ≠ 0`), `HasSym12RankLe (T_RCB K b) 9` and
`HasTensorRankLe (T_RCB K b) 9`. -/
theorem T_RCB_hasSym12RankLe_nine_of_isSquare_neg_three {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {b : K} (hb : b ≠ 0)
    (hsq : IsSquare (-3 : K)) :
    HasSym12RankLe (T_RCB K b) 9 ∧ HasTensorRankLe (T_RCB K b) 9 := by
  have hcong := T_RCB_sym12Congruent_symEps3 h2 h3 hb
  have hsym := (hcong.hasSym12RankLe_iff 9).mpr
    (symEps3_hasSym12RankLe_nine_of_isSquare_neg_three h2 h3 hsq)
  exact ⟨hsym, hsym.toTensorRankLe⟩

/-! ## Section 4: Step 4 — Universal 5-Term `ε₃` and 10-Term `(1,2)`-Symmetric Decomposition -/

/-- Explicit `5`-term decomposition of the `3 × 3 × 3` Levi-Civita tensor `eps3 K` over any field
with `char K ≠ 2` (Step 4 of Theorem 1.1). -/
theorem eps3_hasTensorRankLe_five {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) :
    HasTensorRankLe (eps3 K) 5 := by
  let h : K := (2 : K)⁻¹
  let a5 : Fin 5 → Fin 3 → K :=
    ![![0, 1, 1], ![0, 1, -1], ![1, 0, 1], ![-1, 0, 1], ![1, 1, 0]]
  let b5 : Fin 5 → Fin 3 → K :=
    ![![0, 1, -1], ![0, 1, 1], ![-1, 0, 1], ![1, 0, 1], ![1, -1, 0]]
  let w5 : Fin 5 → Fin 3 → K :=
    ![![-h, 0, -h], ![h, 0, -h], ![0, -h, -h], ![0, h, -h], ![0, 0, -1]]
  refine ⟨a5, b5, w5, fun i j k => ?_⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [Fin.sum_univ_five, a5, b5, w5, h, eps3] <;>
    · field_simp [h2]; ring

/-- Polarized `10`-term `(1,2)`-symmetric decomposition of `symEps3 K` over any field `K` with
`char K ≠ 2` (Step 4 of Theorem 1.1). -/
theorem symEps3_hasSym12RankLe_ten {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) :
    HasSym12RankLe (symEps3 K) 10 := by
  obtain ⟨a5, b5, w5, heps⟩ := eps3_hasTensorRankLe_five h2
  have heps_skew : ∀ i j k : Fin 3, eps3 K j i k = -eps3 K i j k := by
    intro i j k; fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [eps3]
  let u10 : Fin 10 → (Fin 2 × Fin 3) → K := fun idx p =>
    let t : Fin 5 := ⟨idx.val / 2, by omega⟩
    if idx.val % 2 = 0 then
      if p.1 = 0 then a5 t p.2 else b5 t p.2
    else
      if p.1 = 0 then a5 t p.2 else -b5 t p.2
  let w10 : Fin 10 → Fin 3 → K := fun idx k =>
    let t : Fin 5 := ⟨idx.val / 2, by omega⟩
    if idx.val % 2 = 0 then (2 : K)⁻¹ * w5 t k else -(2 : K)⁻¹ * w5 t k
  refine ⟨u10, w10, fun p q k => ?_⟩
  have hpair : (∑ idx : Fin 10, u10 idx p * u10 idx q * w10 idx k) =
      ∑ t : Fin 5,
        (u10 ⟨2 * t.val, by omega⟩ p * u10 ⟨2 * t.val, by omega⟩ q * w10 ⟨2 * t.val, by omega⟩ k +
         u10 ⟨2 * t.val + 1, by omega⟩ p * u10 ⟨2 * t.val + 1, by omega⟩ q *
           w10 ⟨2 * t.val + 1, by omega⟩ k) := by
    let e10 : Fin 5 × Fin 2 ≃ Fin 10 :=
      { toFun := fun tb => ⟨2 * tb.1.val + tb.2.val, by omega⟩
        invFun := fun idx => (⟨idx.val / 2, by omega⟩, ⟨idx.val % 2, by omega⟩)
        left_inv := fun ⟨t, b⟩ => by ext <;> dsimp <;> omega
        right_inv := fun idx => by ext; dsimp; omega }
    rw [← e10.sum_comp (fun idx => u10 idx p * u10 idx q * w10 idx k), Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Fin.sum_univ_two]
    dsimp [e10]
  rw [hpair]
  rcases p with ⟨bp, ip⟩
  rcases q with ⟨bq, iq⟩
  fin_cases bp <;> fin_cases bq
  · simp only [Fin.zero_eta, Fin.isValue, symEps3, zero_ne_one, and_false, ↓reduceIte]
    symm
    refine Finset.sum_eq_zero fun t _ => ?_
    dsimp [u10, w10]
    have hm0 : (2 * t.val) % 2 = 0 := by omega
    have hm1 : (2 * t.val + 1) % 2 = 1 := by omega
    have hd0 : (⟨(2 * t.val) / 2, by omega⟩ : Fin 5) = t := by ext; dsimp; omega
    have hd1 : (⟨(2 * t.val + 1) / 2, by omega⟩ : Fin 5) = t := by ext; dsimp; omega
    simp only [hm0, hm1, one_ne_zero, ↓reduceIte, hd0, hd1]
    ring
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, symEps3, and_self, ↓reduceIte]
    rw [heps ip iq k]
    refine Finset.sum_congr rfl fun t _ => ?_
    dsimp [u10, w10]
    have hm0 : (2 * t.val) % 2 = 0 := by omega
    have hm1 : (2 * t.val + 1) % 2 = 1 := by omega
    have hd0 : (⟨(2 * t.val) / 2, by omega⟩ : Fin 5) = t := by ext; dsimp; omega
    have hd1 : (⟨(2 * t.val + 1) / 2, by omega⟩ : Fin 5) = t := by ext; dsimp; omega
    simp only [hm0, hm1, one_ne_zero, ↓reduceIte, hd0, hd1]
    field_simp [h2]
    ring
  · simp only [Fin.mk_one, Fin.zero_eta, Fin.isValue, symEps3, one_ne_zero, false_and,
      and_self, ↓reduceIte]
    rw [← heps_skew ip iq k, heps iq ip k]
    refine Finset.sum_congr rfl fun t _ => ?_
    dsimp [u10, w10]
    have hm0 : (2 * t.val) % 2 = 0 := by omega
    have hm1 : (2 * t.val + 1) % 2 = 1 := by omega
    have hd0 : (⟨(2 * t.val) / 2, by omega⟩ : Fin 5) = t := by ext; dsimp; omega
    have hd1 : (⟨(2 * t.val + 1) / 2, by omega⟩ : Fin 5) = t := by ext; dsimp; omega
    simp only [hm0, hm1, one_ne_zero, ↓reduceIte, hd0, hd1]
    field_simp [h2]
    ring
  · simp only [Fin.mk_one, Fin.isValue, symEps3, one_ne_zero, false_and, and_false, ↓reduceIte]
    symm
    refine Finset.sum_eq_zero fun t _ => ?_
    dsimp [u10, w10]
    have hm0 : (2 * t.val) % 2 = 0 := by omega
    have hm1 : (2 * t.val + 1) % 2 = 1 := by omega
    have hd0 : (⟨(2 * t.val) / 2, by omega⟩ : Fin 5) = t := by ext; dsimp; omega
    have hd1 : (⟨(2 * t.val + 1) / 2, by omega⟩ : Fin 5) = t := by ext; dsimp; omega
    simp only [hm0, hm1, one_ne_zero, ↓reduceIte, hd0, hd1]
    ring

/-- **Proposition 1.3 / Theorem 1.1, Step 4 (`T_RCB` universal `(1,2)`-symmetric rank `≤ 10`):**
Over every field `K` (`char K ≠ 2, 3`, `b ≠ 0`), `HasSym12RankLe (T_RCB K b) 10` and
`HasTensorRankLe (T_RCB K b) 10`. -/
theorem T_RCB_hasSym12RankLe_ten {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {b : K} (hb : b ≠ 0) :
    HasSym12RankLe (T_RCB K b) 10 ∧ HasTensorRankLe (T_RCB K b) 10 := by
  have hcong := T_RCB_sym12Congruent_symEps3 h2 h3 hb
  have hsym := (hcong.hasSym12RankLe_iff 10).mpr (symEps3_hasSym12RankLe_ten h2)
  exact ⟨hsym, hsym.toTensorRankLe⟩

/-! ## Section 5: Step 5 — Arbitrary-Field Obstruction (`rk_K(I₂ ⊗₁,₂ ε₃) ≤ 9 → IsSquare (-3)`) -/

/-- Explicit inverse `(T_C^{∧1})⁻¹ = I₂ ⊗ Φ⁻¹` on `K¹⁸` when `char K ≠ 2`. -/
def koszulInv18 (K : Type*) [Field K] : Matrix Idx18 Idx18 K :=
  fun row col => if row.1 = col.1 then koszulPhi9Inv K row.2 col.2 else 0

lemma koszulFlat_mul_inv18 {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) :
    linearFlattening (RingHom.id K) (koszulCoeff K) (I2_eps3 K) * koszulInv18 K = 1 := by
  have hphi := (koszulPhi9_mul_inv h2).1
  ext ⟨b, jl⟩ ⟨a, im⟩
  rw [Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type]
  simp only [koszulFlat_I2_eps3_eq, koszulInv18]
  by_cases hba : b = a
  · subst hba
    have hsum : (∑ c : Fin 2, ∑ t : Idx9,
        (if b = c then koszulPhi9 K jl t else 0) *
          (if c = b then koszulPhi9Inv K t im else 0)) =
        (koszulPhi9 K * koszulPhi9Inv K) jl im := by
      rw [Fin.sum_univ_two, Matrix.mul_apply]
      fin_cases b <;> simp
    rw [hsum, hphi, Matrix.one_apply]
    simp
  · have hsum : (∑ c : Fin 2, ∑ t : Idx9,
        (if b = c then koszulPhi9 K jl t else 0) *
          (if c = a then koszulPhi9Inv K t im else 0)) = 0 := by
      refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun t _ => ?_
      by_cases hbc : b = c
      · subst hbc; simp [hba]
      · simp [hbc]
    rw [hsum]
    simp [hba]

/-- Tensor product vector `v ⊗ β ∈ (E ⊗ V) ⊗ V ≅ K¹⁸`. -/
def vecTensor18 {K : Type*} [CommRing K] (v : Fin 2 × Fin 3 → K) (β : Fin 3 → K) : Idx18 → K :=
  fun row => v (row.1, row.2.1) * β row.2.2

/-- `3 × 3` matrix `G(u, v) = U Vᵀ = ∑_{a=0}^1 u^{(a)} (v^{(a)})ᵀ`. -/
def matG3 {K : Type*} [CommRing K] (u v : Fin 2 × Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  fun i j => u (0, i) * v (0, j) + u (1, i) * v (1, j)

/-- `3 × 3` matrix `M(u, v) = (1/2) G(u, v) - G(u, v)ᵀ` from Section 3.1 (Step 5) of Paper 1. -/
def matM3 {K : Type*} [Field K] (u v : Fin 2 × Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  fun i j => (2 : K)⁻¹ * matG3 u v i j - matG3 u v j i

lemma dot3_matG3_mulVec {K : Type*} [CommRing K]
    (u v : Fin 2 × Fin 3 → K) (γ β : Fin 3 → K) :
    dot3 γ (matG3 u v *ᵥ β) =
      dot3 γ (fun i => u (0, i)) * dot3 (fun j => v (0, j)) β +
      dot3 γ (fun i => u (1, i)) * dot3 (fun j => v (1, j)) β := by
  simp only [dot3, matG3, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

lemma dot3_matM3_mulVec {K : Type*} [Field K]
    (u v : Fin 2 × Fin 3 → K) (γ β : Fin 3 → K) :
    dot3 γ (matM3 u v *ᵥ β) =
      (2 : K)⁻¹ * dot3 γ (matG3 u v *ᵥ β) - dot3 β (matG3 u v *ᵥ γ) := by
  simp only [dot3, matM3, matG3, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- Action of `(u_s ⊗ v_s ⊗ w_s)_C^{∧1} (T_C^{∧1})⁻¹` on any `v₀ ⊗ β ∈ K¹⁸`:
`P_s (v₀ ⊗ β) = v_s ⊗ (w_s × (M_{s,0} β))` (Section 3.1, Step 5.1 of Paper 1). -/
lemma koszulRankOne_mul_inv18_vecTensor {K : Type*} [Field K]
    (u_s v_s : Fin 2 × Fin 3 → K) (w_s : Fin 3 → K)
    (v₀ : Fin 2 × Fin 3 → K) (β : Fin 3 → K) :
    (linearFlattening (RingHom.id K) (koszulCoeff K) (rankOneTensor u_s v_s w_s) *
      koszulInv18 K) *ᵥ vecTensor18 v₀ β =
    vecTensor18 v_s (cross3 w_s (matM3 u_s v₀ *ᵥ β)) := by
  rw [← Matrix.mulVec_mulVec]
  let zVec : Idx18 → K := koszulInv18 K *ᵥ vecTensor18 v₀ β
  change (linearFlattening (RingHom.id K) (koszulCoeff K) (rankOneTensor u_s v_s w_s) *ᵥ zVec) = _
  have hz : ∀ (a : Fin 2) (i m : Fin 3),
      zVec (a, (i, m)) =
        (if i = m then (2 : K)⁻¹ * (v₀ (a, 0) * β 0 + v₀ (a, 1) * β 1 + v₀ (a, 2) * β 2)
         else 0) - v₀ (a, m) * β i := by
    intro a i m
    dsimp only [zVec]
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
    have ha_collapse : (∑ b : Fin 2, ∑ j : Fin 3, ∑ l : Fin 3,
        koszulInv18 K (a, (i, m)) (b, (j, l)) * vecTensor18 v₀ β (b, (j, l))) =
        ∑ j : Fin 3, ∑ l : Fin 3, koszulPhi9Inv K (i, m) (j, l) * (v₀ (a, j) * β l) := by
      rw [Fintype.sum_eq_single a]
      · simp [koszulInv18, vecTensor18]
      · intro b hb
        simp [koszulInv18, hb.symm]
    rw [ha_collapse]
    fin_cases i <;> fin_cases m <;>
      simp [Fin.sum_univ_three, koszulPhi9Inv] <;> ring
  funext ⟨b, j₀, l₀⟩
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  have hentry : ∀ (a : Fin 2) (i m : Fin 3),
      linearFlattening (RingHom.id K) (koszulCoeff K) (rankOneTensor u_s v_s w_s)
        (b, (j₀, l₀)) (a, (i, m)) =
      u_s (a, i) * v_s (b, j₀) * cross3 w_s (stdBasis3 m) l₀ := by
    intro a i m
    rw [koszulFlat_apply]
    simp only [RingHom.id_apply, rankOneTensor]
    calc ∑ k : Fin 3, eps3 K k m l₀ * (u_s (a, i) * v_s (b, j₀) * w_s k)
        = u_s (a, i) * v_s (b, j₀) * ∑ k : Fin 3, eps3 K k m l₀ * w_s k := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ => by ring
      _ = u_s (a, i) * v_s (b, j₀) * cross3 w_s (stdBasis3 m) l₀ := by
            rw [sum_eps3_mul_eq_cross3_stdBasis]
  simp_rw [hentry, hz]
  fin_cases l₀ <;>
    simp [Fin.sum_univ_two, Fin.sum_univ_three, vecTensor18, cross3, stdBasis3,
      matM3, matG3, Matrix.mulVec, dotProduct] <;>
    ring

/-- The standard `9 × 9` trace Gram matrix `(G_std)_{(i,j),(k,l)} = Tr(E_{ij} E_{kl}) = δ_{jk} δ_{il}`
on `Mat₃(K)` has determinant `(+1)³(-1)³ = -1` over every commutative ring `K`. -/
def stdTraceGram9 (K : Type*) [CommRing K] : Matrix Idx9 Idx9 K :=
  fun ij kl => if ij.2 = kl.1 ∧ ij.1 = kl.2 then 1 else 0

theorem det_stdTraceGram9 (K : Type*) [CommRing K] : (stdTraceGram9 K).det = -1 := by
  rw [← Matrix.det_reindex_self blockIdx9Equiv.symm (stdTraceGram9 K)]
  let I3 : Matrix (Fin 3) (Fin 3) K := 1
  let F2 : Matrix (Fin 2) (Fin 2) K := ![![0, 1], ![1, 0]]
  have hblk : Matrix.reindex blockIdx9Equiv.symm blockIdx9Equiv.symm (stdTraceGram9 K) =
      Matrix.fromBlocks I3 0 0
        (Matrix.fromBlocks F2 0 0 (Matrix.fromBlocks F2 0 0 F2)) := by
    ext x y
    rcases x with i | (i | (i | i)) <;> rcases y with j | (j | (j | j)) <;>
      fin_cases i <;> fin_cases j <;>
      simp [blockIdx9Equiv, stdTraceGram9, I3, F2, Matrix.fromBlocks]
  rw [hblk, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_fromBlocks_zero₂₁]
  have hI3 : I3.det = 1 := Matrix.det_one
  have hF2 : F2.det = -1 := by rw [Matrix.det_fin_two]; simp [F2]
  rw [hI3, hF2]
  ring

/-- Determinant of the `9 × 9` equiangular Gram matrix `G_Q = (3/4) I₉ + (1/4) J₉`:
`det(G_Q) = 3 · (81 / 256)²` over any field `K` with `char K ≠ 2` (Equation (3.11)). -/
def equiangularGram9 (K : Type*) [Field K] : Matrix (Fin 9) (Fin 9) K :=
  fun r s => if r = s then 1 else (4 : K)⁻¹

theorem det_equiangularGram9 {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) :
    (equiangularGram9 K).det = 3 * (81 * (256 : K)⁻¹) ^ 2 := by
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have h256 : (256 : K) ≠ 0 := by
    have : (256 : K) = 2 ^ 8 := by norm_num
    rw [this]; exact pow_ne_zero 8 h2
  let R1 : Matrix (Fin 9) (Fin 9) K :=
    fun i j => if i = j then 1 else if j = 0 then -1 else 0
  let C1 : Matrix (Fin 9) (Fin 9) K :=
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
  let RG : Matrix (Fin 9) (Fin 9) K := R1 * equiangularGram9 K
  have hRG : ∀ i j : Fin 9, RG i j =
      if i = 0 then equiangularGram9 K 0 j
      else if j = 0 then -(3 * (4 : K)⁻¹)
      else if i = j then 3 * (4 : K)⁻¹ else 0 := by
    intro i j
    change (R1 * equiangularGram9 K) i j = _
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    refine Fin.cases ?_ (fun i' => ?_) i
    · have htail : (∑ x : Fin 8, R1 0 x.succ * equiangularGram9 K x.succ j) = 0 := by
        refine Finset.sum_eq_zero fun x _ => ?_
        have h0s : (0 : Fin 9) ≠ x.succ := (Fin.succ_ne_zero x).symm
        simp [R1, h0s, Fin.succ_ne_zero]
      rw [htail, add_zero]
      simp [R1]
    · have hs0 : i'.succ ≠ 0 := Fin.succ_ne_zero i'
      have h0i : (0 : Fin 9) ≠ i'.succ := hs0.symm
      have htail : (∑ x : Fin 8, R1 i'.succ x.succ * equiangularGram9 K x.succ j) =
          equiangularGram9 K i'.succ j := by
        have hite : ∀ x : Fin 8, R1 i'.succ x.succ * equiangularGram9 K x.succ j =
            if x = i' then equiangularGram9 K i'.succ j else 0 := by
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
      · simp only [hs0, ↓reduceIte, equiangularGram9]
        field_simp [h4]; ring
      · have hj0 : j'.succ ≠ 0 := Fin.succ_ne_zero j'
        have h0j : (0 : Fin 9) ≠ j'.succ := hj0.symm
        by_cases hij : i' = j'
        · subst hij
          simp only [hs0, h0i, ↓reduceIte, equiangularGram9]
          field_simp [h4]; ring
        · have hsij : i'.succ ≠ j'.succ := fun h => hij (Fin.succ_inj.mp h)
          simp only [hs0, hj0, h0j, hsij, ↓reduceIte, equiangularGram9]
          ring
  let U : Matrix (Fin 9) (Fin 9) K := RG * C1
  have hU_entry : ∀ i j : Fin 9, U i j =
      if i = 0 then (if j = 0 then 3 else (4 : K)⁻¹)
      else if i = j then 3 * (4 : K)⁻¹ else 0 := by
    intro i j
    change (RG * C1) i j = _
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    refine Fin.cases ?_ (fun j' => ?_) j
    · have hC1_0 : ∀ k : Fin 9, C1 k 0 = 1 := by
        intro k; by_cases hk : k = 0 <;> simp [C1, hk]
      simp_rw [hC1_0, mul_one]
      refine Fin.cases ?_ (fun i' => ?_) i
      · simp only [↓reduceIte, hRG]
        have htail : (∑ x : Fin 8, equiangularGram9 K 0 x.succ) = 8 * (4 : K)⁻¹ := by
          have hc : ∀ x : Fin 8, equiangularGram9 K 0 x.succ = (4 : K)⁻¹ := fun x => by
            have h0s : (0 : Fin 9) ≠ x.succ := (Fin.succ_ne_zero x).symm
            simp [equiangularGram9, h0s]
          simp_rw [hc]
          simp
        rw [htail]
        simp only [equiangularGram9, ↓reduceIte]
        field_simp [h4]; ring
      · have hs0 : i'.succ ≠ 0 := Fin.succ_ne_zero i'
        simp only [hs0, ↓reduceIte, hRG, Fin.succ_ne_zero]
        have htail : (∑ x : Fin 8, if i'.succ = x.succ then 3 * (4 : K)⁻¹ else (0 : K)) =
            3 * (4 : K)⁻¹ := by
          simp only [Fin.succ_inj, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
        rw [htail]
        ring
    · have hj0 : j'.succ ≠ 0 := Fin.succ_ne_zero j'
      have hC1_s : ∀ k : Fin 9, C1 k j'.succ = if k = j'.succ then 1 else 0 := by
        intro k; by_cases hk : k = j'.succ <;> simp [C1, hk, hj0]
      simp_rw [hC1_s]
      have h0j : (0 : Fin 9) ≠ j'.succ := hj0.symm
      have htail : (∑ x : Fin 8, RG i x.succ * (if x.succ = j'.succ then 1 else 0)) =
          RG i j'.succ := by
        simp only [Fin.succ_inj, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      rw [htail]
      simp only [h0j, ↓reduceIte, mul_zero, zero_add, hRG, hj0]
      by_cases hi0 : i = 0
      · subst hi0; simp [equiangularGram9, h0j]
      · simp [hi0]
  have hU_up : U.IsUpperTriangular := by
    intro i j hij
    have hi0 : i ≠ 0 := by intro h0; subst h0; exact Nat.not_lt_zero j.val hij
    have hne : i ≠ j := ne_of_gt hij
    rw [hU_entry]
    simp [hi0, hne]
  have hU_det : U.det = 3 * (81 * (256 : K)⁻¹) ^ 2 := by
    rw [Matrix.det_of_isUpperTriangular hU_up, Fin.prod_univ_succ]
    have h00 : U 0 0 = 3 := by rw [hU_entry]; simp
    have hdiag : ∀ x : Fin 8, U x.succ x.succ = 3 * (4 : K)⁻¹ := fun x => by
      rw [hU_entry]; simp [Fin.succ_ne_zero]
    simp_rw [h00, hdiag]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    field_simp [h4, h256]
    ring
  have hdet_rel : U.det = (equiangularGram9 K).det := by
    change (R1 * equiangularGram9 K * C1).det = _
    rw [Matrix.det_mul, Matrix.det_mul, hR1_det, hC1_det, one_mul, mul_one]
  rw [← hdet_rel, hU_det]

/-- **Theorem 1.1, Step 5 (Arbitrary-field rank-9 obstruction — Section 3.1 of Paper 1):**
Over *every* field `K` with `char K ≠ 2, 3`, if `I₂ ⊗₁,₂ ε₃` admits a `9`-term tensor
decomposition over `K`, then `-3` is a square in `K`. -/
theorem rank_9_implies_isSquare_neg_three {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (hr9 : HasTensorRankLe (I2_eps3 K) 9) :
    IsSquare (-3 : K) := by
  classical
  rcases hr9 with ⟨u, v, w, hT⟩
  -- 5.1. Zero-slack complementary idempotent projections P_r = L_r (T_C^{∧1})⁻¹
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
  choose b₀ b₁ c₀ c₁ hb₀ hb₁ hw0_zero hw_span hL_fac using hfac_all
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
  have hBA_block : ∀ s r : Fin 9, B_fac s * A_fac r = if s = r then 1 else 0 := by
    intro s r
    ext t₁ t₂
    have hent := congrFun (congrFun hBA_big (s, t₁)) (r, t₂)
    rw [Matrix.mul_apply] at hent ⊢
    by_cases hsr : s = r
    · subst hsr
      simpa [B_big, A_big, Matrix.one_apply] using hent
    · simpa [B_big, A_big, Matrix.one_apply, hsr] using hent
  -- Complementary idempotent projection relations P_s * P_r = δ_{sr} P_s
  have hP_orthog : ∀ s r : Fin 9, P_mat s * P_mat r = if s = r then P_mat s else 0 := by
    intro s r
    have hassoc : P_mat s * P_mat r = A_fac s * (B_fac s * A_fac r) * B_fac r := by
      rw [hP_fac s, hP_fac r]
      simp only [Matrix.mul_assoc]
    rw [hassoc, hBA_block s r]
    by_cases hsr : s = r
    · subst hsr
      simp [← hP_fac s]
    · simp [hsr]
  have hw_ne : ∀ r : Fin 9, w r ≠ 0 := by
    intro r h0
    rcases hw0_zero r h0 with ⟨hb0_0, hb1_0⟩
    have hA0 : A_fac r = 0 := by
      ext row t; fin_cases t <;> simp [A_fac, hb0_0, hb1_0]
    have h1 := hBA_block r r
    simp only [↓reduceIte, hA0, Matrix.mul_zero] at h1
    exact one_ne_zero (congrFun (congrFun h1 0) 0).symm
  have hv_ne : ∀ r : Fin 9, v r ≠ 0 := by
    intro r h0
    have hA0 : A_fac r = 0 := by
      ext row t; simp [A_fac, h0]
    have h1 := hBA_block r r
    simp only [↓reduceIte, hA0, Matrix.mul_zero] at h1
    exact one_ne_zero (congrFun (congrFun h1 0) 0).symm
  have hP_on_perp : ∀ (s r : Fin 9) (β : Fin 3 → K), dot3 (w r) β = 0 →
      P_mat s *ᵥ vecTensor18 (v r) β = if s = r then vecTensor18 (v r) β else 0 := by
    intro s r β hβ
    have hβ_eq := hw_span r (hw_ne r) β hβ
    have hvec_eq : vecTensor18 (v r) β = A_fac r *ᵥ ![c₀ r β, c₁ r β] := by
      funext ⟨b, j, l⟩
      have hl := congrFun hβ_eq l
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hl
      simp only [vecTensor18, hl, Matrix.mulVec, dotProduct, Fin.sum_univ_two, A_fac,
        Matrix.of_apply, Fin.isValue, ↓reduceIte, one_ne_zero, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      ring
    have hcalc : P_mat s *ᵥ vecTensor18 (v r) β =
        A_fac s *ᵥ ((B_fac s * A_fac r) *ᵥ ![c₀ r β, c₁ r β]) := by
      rw [hvec_eq, hP_fac s]
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [hcalc, hBA_block s r]
    by_cases hsr : s = r
    · subst hsr; simp [← hvec_eq]
    · simp [hsr]
  -- Derive Equations (3.6) and (3.7) of Section 3.1 (Step 5.1)
  have hcross_rel : ∀ (s r : Fin 9) (β : Fin 3 → K), dot3 (w r) β = 0 →
      cross3 (w s) (matM3 (u s) (v r) *ᵥ β) = if s = r then β else 0 := by
    intro s r β hβ
    have h1 := hP_on_perp s r β hβ
    have h2_act : P_mat s *ᵥ vecTensor18 (v r) β =
        vecTensor18 (v s) (cross3 (w s) (matM3 (u s) (v r) *ᵥ β)) :=
      koszulRankOne_mul_inv18_vecTensor (u s) (v s) (w s) (v r) β
    rw [h2_act] at h1
    have hex_v : ∃ p₀ : Fin 2 × Fin 3, v s p₀ ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hv_ne s (funext hall)
    rcases hex_v with ⟨⟨b₀_idx, j₀_idx⟩, hvs_ne⟩
    by_cases hsr : s = r
    · subst hsr
      simp only [↓reduceIte] at h1 ⊢
      funext l
      have hl := congrFun h1 (b₀_idx, (j₀_idx, l))
      simp only [vecTensor18] at hl
      exact mul_left_cancel₀ hvs_ne hl
    · simp only [hsr, ↓reduceIte] at h1 ⊢
      funext l
      have hl := congrFun h1 (b₀_idx, (j₀_idx, l))
      simp only [vecTensor18, Pi.zero_apply] at hl
      exact (mul_eq_zero.mp hl).resolve_left hvs_ne
  -- Equation (I): w_r × (M_{rr} β) = β for all β ∈ w_r⊥
  have eq_I : ∀ (r : Fin 9) (β : Fin 3 → K), dot3 (w r) β = 0 →
      cross3 (w r) (matM3 (u r) (v r) *ᵥ β) = β := by
    intro r β hβ
    simpa using hcross_rel r r β hβ
  -- Equation (II): γᵀ G_{rs} β = 2 βᵀ G_{rs} γ for r ≠ s, β ∈ w_s⊥, γ ∈ w_r⊥
  have eq_II : ∀ {r s : Fin 9}, r ≠ s → ∀ (β γ : Fin 3 → K),
      dot3 (w s) β = 0 → dot3 (w r) γ = 0 →
      dot3 γ (matG3 (u r) (v s) *ᵥ β) = 2 * dot3 β (matG3 (u r) (v s) *ᵥ γ) := by
    intro r s hrs β γ hβ hγ
    have hcr0 : cross3 (w r) (matM3 (u r) (v s) *ᵥ β) = 0 := by
      simpa [hrs] using hcross_rel r s β hβ
    obtain ⟨c_col, hc_col⟩ := cross3_eq_zero_imp_collinear (hw_ne r) hcr0
    have hdotM : dot3 γ (matM3 (u r) (v s) *ᵥ β) = 0 := by
      rw [hc_col, dot3_smul_right, dot3_comm γ (w r), hγ, mul_zero]
    rw [dot3_matM3_mulVec] at hdotM
    field_simp [h2] at hdotM
    linear_combination hdotM
  -- 5.2. Diagonal nondegeneracy, Δ_r ≠ 0, and V_r = (2 / (3 Δ_r)) U_r J + w_r λ_rᵀ
  have hGrr_alt_self : ∀ (r : Fin 9) (β : Fin 3 → K), dot3 (w r) β = 0 →
      dot3 β (matG3 (u r) (v r) *ᵥ β) = 0 := by
    intro r β hβ
    have hcr := eq_I r β hβ
    have horth : dot3 (matM3 (u r) (v r) *ᵥ β) β = 0 := by
      calc dot3 (matM3 (u r) (v r) *ᵥ β) β
          = dot3 (matM3 (u r) (v r) *ᵥ β) (cross3 (w r) (matM3 (u r) (v r) *ᵥ β)) := by
              nth_rw 2 [← hcr]
        _ = 0 := by simp [dot3, cross3]; ring
    rw [dot3_comm, dot3_matM3_mulVec] at horth
    field_simp [h2] at horth
    linear_combination -horth
  have hGrr_skew : ∀ (r : Fin 9) (β₁ β₂ : Fin 3 → K),
      dot3 (w r) β₁ = 0 → dot3 (w r) β₂ = 0 →
      dot3 β₂ (matG3 (u r) (v r) *ᵥ β₁) = -dot3 β₁ (matG3 (u r) (v r) *ᵥ β₂) := by
    intro r β₁ β₂ h₁ h₂
    have hsum_perp : dot3 (w r) (β₁ + β₂) = 0 := by
      rw [dot3_add_right, h₁, h₂, add_zero]
    have h0 := hGrr_alt_self r (β₁ + β₂) hsum_perp
    have h10 := hGrr_alt_self r β₁ h₁
    have h20 := hGrr_alt_self r β₂ h₂
    have hexp : dot3 (β₁ + β₂) (matG3 (u r) (v r) *ᵥ (β₁ + β₂)) =
        dot3 β₁ (matG3 (u r) (v r) *ᵥ β₁) + dot3 β₁ (matG3 (u r) (v r) *ᵥ β₂) +
        dot3 β₂ (matG3 (u r) (v r) *ᵥ β₁) + dot3 β₂ (matG3 (u r) (v r) *ᵥ β₂) := by
      simp only [dot3, matG3, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.add_apply]
      ring
    rw [hexp, h10, h20] at h0
    linear_combination h0
  -- Equation (3.8): β₁ × β₂ = (3/2)(β₁ᵀ G_{rr} β₂) w_r
  have hdiag_cross : ∀ (r : Fin 9) (β₁ β₂ : Fin 3 → K),
      dot3 (w r) β₁ = 0 → dot3 (w r) β₂ = 0 →
      cross3 β₁ β₂ = ((3 * (2 : K)⁻¹) * dot3 β₁ (matG3 (u r) (v r) *ᵥ β₂)) • w r := by
    intro r β₁ β₂ h₁ h₂
    have hcr₂ := eq_I r β₂ h₂
    calc cross3 β₁ β₂ = cross3 β₁ (cross3 (w r) (matM3 (u r) (v r) *ᵥ β₂)) := by
            conv_lhs => rw [← hcr₂]
      _ = (dot3 β₁ (matM3 (u r) (v r) *ᵥ β₂)) • w r -
            (dot3 β₁ (w r)) • (matM3 (u r) (v r) *ᵥ β₂) := bac_cab _ _ _
      _ = ((3 * (2 : K)⁻¹) * dot3 β₁ (matG3 (u r) (v r) *ᵥ β₂)) • w r := by
            rw [dot3_comm β₁ (w r), h₁, zero_smul, sub_zero, dot3_matM3_mulVec,
              hGrr_skew r β₁ β₂ h₁ h₂]
            congr 1
            field_simp [h2]; ring
  let u1 : Fin 9 → Fin 3 → K := fun r i => u r (0, i)
  let u2 : Fin 9 → Fin 3 → K := fun r i => u r (1, i)
  let v1 : Fin 9 → Fin 3 → K := fun r i => v r (0, i)
  let v2 : Fin 9 → Fin 3 → K := fun r i => v r (1, i)
  let ν : Fin 9 → Fin 3 → K := fun r => cross3 (u1 r) (u2 r)
  let Δ : Fin 9 → K := fun r => dot3 (ν r) (w r)
  have hΔ_ne : ∀ r : Fin 9, Δ r ≠ 0 := by
    intro r hΔ0
    obtain ⟨p₀, p₁, _, _, s_r, hp₀, hp₁, hs_ne, hcr_p, _, _, _⟩ :=
      exists_perp_basis_of_ne_zero (hw_ne r)
    have hcr_ne : cross3 p₀ p₁ ≠ 0 := by
      rw [hcr_p]
      intro h0
      have : s_r⁻¹ • (s_r • w r) = 0 := by rw [h0, smul_zero]
      rw [smul_smul, inv_mul_cancel₀ hs_ne, one_smul] at this
      exact hw_ne r this
    have hg01_ne : dot3 p₀ (matG3 (u r) (v r) *ᵥ p₁) ≠ 0 := by
      intro hg0
      have hc := hdiag_cross r p₀ p₁ hp₀ hp₁
      rw [hg0, mul_zero, zero_smul] at hc
      exact hcr_ne hc
    have hdet2 :
        dot3 p₀ (matG3 (u r) (v r) *ᵥ p₀) * dot3 p₁ (matG3 (u r) (v r) *ᵥ p₁) -
        dot3 p₀ (matG3 (u r) (v r) *ᵥ p₁) * dot3 p₁ (matG3 (u r) (v r) *ᵥ p₀) =
        dot3 (cross3 p₀ p₁) (ν r) * dot3 (cross3 (v1 r) (v2 r)) (cross3 p₀ p₁) := by
      simp only [dot3_matG3_mulVec]
      dsimp [u1, u2, v1, v2, ν]
      simp [dot3, cross3]
      ring
    rw [hGrr_alt_self r p₀ hp₀, hGrr_alt_self r p₁ hp₁,
      hGrr_skew r p₀ p₁ hp₀ hp₁, hcr_p, dot3_smul_left, dot3_comm (w r) (ν r)] at hdet2
    change 0 * 0 - dot3 p₀ (matG3 (u r) (v r) *ᵥ p₁) * (-dot3 p₀ (matG3 (u r) (v r) *ᵥ p₁)) =
      s_r * Δ r * dot3 (cross3 (v1 r) (v2 r)) (s_r • w r) at hdet2
    rw [hΔ0] at hdet2
    have hsq0 : dot3 p₀ (matG3 (u r) (v r) *ᵥ p₁) * dot3 p₀ (matG3 (u r) (v r) *ᵥ p₁) = 0 := by
      linear_combination hdet2
    exact hg01_ne (mul_self_eq_zero.mp hsq0)
  -- Explicit formula V_r = (2 / (3 Δ_r)) U_r J + w_r λ_rᵀ (Equation (3.9))
  have hVr_decomp : ∀ r : Fin 9,
      ∃ lam1 lam2 : K,
        v1 r = (2 * (3 * Δ r)⁻¹) • u2 r + lam1 • w r ∧
        v2 r = -(2 * (3 * Δ r)⁻¹) • u1 r + lam2 • w r := by
    intro r
    let β₁ : Fin 3 → K := cross3 (u2 r) (w r)
    let β₂ : Fin 3 → K := cross3 (w r) (u1 r)
    have hβ₁_perp : dot3 (w r) β₁ = 0 := dot3_cross3_self_right (u2 r) (w r)
    have hβ₂_perp : dot3 (w r) β₂ = 0 := dot3_cross3_self_left (w r) (u1 r)
    have hβ₁_u1 : dot3 β₁ (u1 r) = Δ r := by dsimp [β₁, Δ, ν]; simp [dot3, cross3]; ring
    have hβ₁_u2 : dot3 β₁ (u2 r) = 0 := by dsimp [β₁]; simp [dot3, cross3]; ring
    have hβ₂_u1 : dot3 β₂ (u1 r) = 0 := by dsimp [β₂]; simp [dot3, cross3]; ring
    have hβ₂_u2 : dot3 β₂ (u2 r) = Δ r := by dsimp [β₂, Δ, ν]; simp [dot3, cross3]; ring
    have hcr_β : cross3 β₁ β₂ = Δ r • w r := by
      funext i; fin_cases i <;> dsimp [β₁, β₂, Δ, ν] <;> simp [dot3, cross3] <;> ring
    have hΔr := hΔ_ne r
    have hv1_β₁ : dot3 (v1 r) β₁ = 0 := by
      have h0 := hGrr_alt_self r β₁ hβ₁_perp
      rw [dot3_matG3_mulVec] at h0
      change dot3 β₁ (u1 r) * dot3 (v1 r) β₁ + dot3 β₁ (u2 r) * dot3 (v2 r) β₁ = 0 at h0
      rw [hβ₁_u1, hβ₁_u2, zero_mul, add_zero] at h0
      exact (mul_eq_zero.mp h0).resolve_left hΔr
    have hv2_β₂ : dot3 (v2 r) β₂ = 0 := by
      have h0 := hGrr_alt_self r β₂ hβ₂_perp
      rw [dot3_matG3_mulVec] at h0
      change dot3 β₂ (u1 r) * dot3 (v1 r) β₂ + dot3 β₂ (u2 r) * dot3 (v2 r) β₂ = 0 at h0
      rw [hβ₂_u1, hβ₂_u2, zero_mul, zero_add] at h0
      exact (mul_eq_zero.mp h0).resolve_left hΔr
    have hcr_eq := hdiag_cross r β₁ β₂ hβ₁_perp hβ₂_perp
    rw [hcr_β] at hcr_eq
    have hscalar_eq : (3 * (2 : K)⁻¹) * dot3 β₁ (matG3 (u r) (v r) *ᵥ β₂) = Δ r := by
      have hdiff : (Δ r - (3 * (2 : K)⁻¹) * dot3 β₁ (matG3 (u r) (v r) *ᵥ β₂)) • w r = 0 := by
        rw [sub_smul, hcr_eq, sub_self]
      by_contra hne
      have hsub_ne : Δ r - (3 * (2 : K)⁻¹) * dot3 β₁ (matG3 (u r) (v r) *ᵥ β₂) ≠ 0 :=
        sub_ne_zero.mpr (Ne.symm hne)
      have hw0 : w r = 0 := by
        calc w r = (Δ r - (3 * (2 : K)⁻¹) * dot3 β₁ (matG3 (u r) (v r) *ᵥ β₂))⁻¹ •
                ((Δ r - (3 * (2 : K)⁻¹) * dot3 β₁ (matG3 (u r) (v r) *ᵥ β₂)) • w r) := by
                  rw [smul_smul, inv_mul_cancel₀ hsub_ne, one_smul]
          _ = 0 := by rw [hdiff, smul_zero]
      exact hw_ne r hw0
    have hv1_β₂ : dot3 (v1 r) β₂ = 2 * (3 : K)⁻¹ := by
      rw [dot3_matG3_mulVec] at hscalar_eq
      change (3 * (2 : K)⁻¹) *
        (dot3 β₁ (u1 r) * dot3 (v1 r) β₂ + dot3 β₁ (u2 r) * dot3 (v2 r) β₂) = Δ r at hscalar_eq
      rw [hβ₁_u1, hβ₁_u2, zero_mul, add_zero] at hscalar_eq
      have hcancel : Δ r * (3 * (2 : K)⁻¹ * dot3 (v1 r) β₂ - 1) = 0 := by
        linear_combination hscalar_eq
      have hlin := (mul_eq_zero.mp hcancel).resolve_left hΔr
      field_simp [h2, h3] at hlin ⊢
      linear_combination hlin
    have hv2_β₁ : dot3 (v2 r) β₁ = -(2 * (3 : K)⁻¹) := by
      have hskew := hGrr_skew r β₁ β₂ hβ₁_perp hβ₂_perp
      rw [dot3_matG3_mulVec, dot3_matG3_mulVec] at hskew
      change dot3 β₂ (u1 r) * dot3 (v1 r) β₁ + dot3 β₂ (u2 r) * dot3 (v2 r) β₁ =
        -(dot3 β₁ (u1 r) * dot3 (v1 r) β₂ + dot3 β₁ (u2 r) * dot3 (v2 r) β₂) at hskew
      rw [hβ₂_u1, hβ₂_u2, hβ₁_u1, hβ₁_u2, hv1_β₂] at hskew
      have hcancel : Δ r * (dot3 (v2 r) β₁ + 2 * (3 : K)⁻¹) = 0 := by
        linear_combination hskew
      have hlin := (mul_eq_zero.mp hcancel).resolve_left hΔr
      linear_combination hlin
    let d1 : Fin 3 → K := v1 r - (2 * (3 * Δ r)⁻¹) • u2 r
    let d2 : Fin 3 → K := v2 r + (2 * (3 * Δ r)⁻¹) • u1 r
    have hd1_β₁ : dot3 d1 β₁ = 0 := by
      dsimp [d1]
      have hexp : dot3 (v1 r - (2 * (3 * Δ r)⁻¹) • u2 r) β₁ =
          dot3 (v1 r) β₁ - (2 * (3 * Δ r)⁻¹) * dot3 β₁ (u2 r) := by
        simp [dot3]; ring
      rw [hexp, hv1_β₁, hβ₁_u2]
      ring
    have hd1_β₂ : dot3 d1 β₂ = 0 := by
      dsimp [d1]
      have hexp : dot3 (v1 r - (2 * (3 * Δ r)⁻¹) • u2 r) β₂ =
          dot3 (v1 r) β₂ - (2 * (3 * Δ r)⁻¹) * dot3 β₂ (u2 r) := by
        simp [dot3]; ring
      rw [hexp, hv1_β₂, hβ₂_u2]
      field_simp [h3, hΔr]; ring
    have hd2_β₁ : dot3 d2 β₁ = 0 := by
      dsimp [d2]
      have hexp : dot3 (v2 r + (2 * (3 * Δ r)⁻¹) • u1 r) β₁ =
          dot3 (v2 r) β₁ + (2 * (3 * Δ r)⁻¹) * dot3 β₁ (u1 r) := by
        simp [dot3]; ring
      rw [hexp, hv2_β₁, hβ₁_u1]
      field_simp [h3, hΔr]; ring
    have hd2_β₂ : dot3 d2 β₂ = 0 := by
      dsimp [d2]
      have hexp : dot3 (v2 r + (2 * (3 * Δ r)⁻¹) • u1 r) β₂ =
          dot3 (v2 r) β₂ + (2 * (3 * Δ r)⁻¹) * dot3 β₂ (u1 r) := by
        simp [dot3]; ring
      rw [hexp, hv2_β₂, hβ₂_u1, mul_zero, add_zero]
    have hcr_d1 : cross3 (w r) d1 = 0 := by
      have h0 : cross3 d1 (cross3 β₁ β₂) = 0 := by
        simp [bac_cab, hd1_β₂, hd1_β₁]
      rw [hcr_β, cross3_smul_right] at h0
      have hd1w : cross3 d1 (w r) = 0 := by
        calc cross3 d1 (w r) = (Δ r)⁻¹ • (Δ r • cross3 d1 (w r)) := by
                rw [smul_smul, inv_mul_cancel₀ hΔr, one_smul]
          _ = 0 := by rw [h0, smul_zero]
      rw [cross3_anticomm, hd1w, neg_zero]
    have hcr_d2 : cross3 (w r) d2 = 0 := by
      have h0 : cross3 d2 (cross3 β₁ β₂) = 0 := by
        simp [bac_cab, hd2_β₂, hd2_β₁]
      rw [hcr_β, cross3_smul_right] at h0
      have hd2w : cross3 d2 (w r) = 0 := by
        calc cross3 d2 (w r) = (Δ r)⁻¹ • (Δ r • cross3 d2 (w r)) := by
                rw [smul_smul, inv_mul_cancel₀ hΔr, one_smul]
          _ = 0 := by rw [h0, smul_zero]
      rw [cross3_anticomm, hd2w, neg_zero]
    obtain ⟨lam1, hlam1⟩ := cross3_eq_zero_imp_collinear (hw_ne r) hcr_d1
    obtain ⟨lam2, hlam2⟩ := cross3_eq_zero_imp_collinear (hw_ne r) hcr_d2
    refine ⟨lam1, lam2, ?_, ?_⟩
    · funext i; have hi := congrFun hlam1 i; dsimp [d1] at hi; simp at hi ⊢; linear_combination hi
    · funext i; have hi := congrFun hlam2 i; dsimp [d2] at hi; simp at hi ⊢; linear_combination hi
  choose lam1 lam2 hv1_eq hv2_eq using hVr_decomp
  have hGrs_on_perp : ∀ (r s : Fin 9) (γ β : Fin 3 → K), dot3 (w s) β = 0 →
      dot3 γ (matG3 (u r) (v s) *ᵥ β) =
        (2 * (3 * Δ s)⁻¹) * (dot3 γ (u1 r) * dot3 (u2 s) β - dot3 γ (u2 r) * dot3 (u1 s) β) := by
    intro r s γ β hβ
    rw [dot3_matG3_mulVec]
    change dot3 γ (u1 r) * dot3 (v1 s) β + dot3 γ (u2 r) * dot3 (v2 s) β = _
    rw [hv1_eq s, hv2_eq s]
    have hd_v1 : dot3 ((2 * (3 * Δ s)⁻¹) • u2 s + lam1 s • w s) β =
        (2 * (3 * Δ s)⁻¹) * dot3 (u2 s) β := by
      rw [dot3_add_left, dot3_smul_left, dot3_smul_left, hβ, mul_zero, add_zero]
    have hd_v2 : dot3 (-(2 * (3 * Δ s)⁻¹) • u1 s + lam2 s • w s) β =
        -(2 * (3 * Δ s)⁻¹) * dot3 (u1 s) β := by
      calc dot3 (-(2 * (3 * Δ s)⁻¹) • u1 s + lam2 s • w s) β
          = -(2 * (3 * Δ s)⁻¹) * dot3 (u1 s) β + lam2 s * dot3 (w s) β := by
              simp [dot3]; ring
        _ = -(2 * (3 * Δ s)⁻¹) * dot3 (u1 s) β := by rw [hβ, mul_zero, add_zero]
    rw [hd_v1, hd_v2]
    ring
  -- 5.3. Off-diagonal non-collinearity w_r ∦ w_s and equiangularity (ν_rᵀ w_s)(ν_sᵀ w_r)/(Δ_r Δ_s) = 1/4
  have hw_nonpar : ∀ {r s : Fin 9}, r ≠ s → cross3 (w r) (w s) ≠ 0 := by
    intro r s hrs hcr0
    obtain ⟨c_ws, hc_ws⟩ := cross3_eq_zero_imp_collinear (hw_ne r) hcr0
    have hc_ne : c_ws ≠ 0 := by
      intro h0; rw [h0, zero_smul] at hc_ws; exact hw_ne s hc_ws
    have hperp_iff : ∀ x : Fin 3 → K, dot3 (w s) x = 0 ↔ dot3 (w r) x = 0 := by
      intro x; rw [hc_ws, dot3_smul_left, mul_eq_zero]
      exact ⟨fun h => h.resolve_left hc_ne, fun h => Or.inr h⟩
    let γ₀ : Fin 3 → K := cross3 (u2 r) (w r)
    let β₀ : Fin 3 → K := cross3 (u1 s) (w s)
    have hγ₀_r : dot3 (w r) γ₀ = 0 := dot3_cross3_self_right (u2 r) (w r)
    have hγ₀_s : dot3 (w s) γ₀ = 0 := (hperp_iff γ₀).mpr hγ₀_r
    have hβ₀_s : dot3 (w s) β₀ = 0 := dot3_cross3_self_right (u1 s) (w s)
    have hβ₀_r : dot3 (w r) β₀ = 0 := (hperp_iff β₀).mp hβ₀_s
    have heq1 := eq_II hrs β₀ γ₀ hβ₀_s hγ₀_r
    have heq2 := eq_II hrs γ₀ β₀ hγ₀_s hβ₀_r
    have h3zero : 3 * dot3 γ₀ (matG3 (u r) (v s) *ᵥ β₀) = 0 := by
      linear_combination -(heq1 + 2 * heq2)
    have hval0 : dot3 γ₀ (matG3 (u r) (v s) *ᵥ β₀) = 0 :=
      (mul_eq_zero.mp h3zero).resolve_left h3
    rw [hGrs_on_perp r s γ₀ β₀ hβ₀_s] at hval0
    have hγ_u1 : dot3 γ₀ (u1 r) = Δ r := by dsimp [γ₀, Δ, ν]; simp [dot3, cross3]; ring
    have hγ_u2 : dot3 γ₀ (u2 r) = 0 := by dsimp [γ₀]; simp [dot3, cross3]; ring
    have hβ_u2 : dot3 (u2 s) β₀ = -Δ s := by dsimp [β₀, Δ, ν]; simp [dot3, cross3]; ring
    rw [hγ_u1, hγ_u2, hβ_u2, zero_mul, sub_zero] at hval0
    have hΔs := hΔ_ne s
    field_simp [h3, hΔs] at hval0
    have hprod : 2 * Δ r = 0 := by linear_combination -hval0
    exact mul_ne_zero h2 (hΔ_ne r) hprod
  have hUr_inj_on_perp : ∀ (r : Fin 9) (η : Fin 3 → K),
      dot3 (w r) η = 0 → η ≠ 0 → dot3 η (u1 r) ≠ 0 ∨ dot3 η (u2 r) ≠ 0 := by
    intro r η hη_perp hη_ne
    by_contra hboth
    push Not at hboth
    rcases hboth with ⟨hu1_0, hu2_0⟩
    let β₁ : Fin 3 → K := cross3 (u2 r) (w r)
    let β₂ : Fin 3 → K := cross3 (w r) (u1 r)
    have hcr1 : cross3 η β₁ = 0 := by
      dsimp [β₁]
      simp [bac_cab, dot3_comm η (w r), hη_perp, hu2_0]
    have hcr2 : cross3 η β₂ = 0 := by
      dsimp [β₂]
      simp [bac_cab, hu1_0, dot3_comm η (w r), hη_perp]
    obtain ⟨t₁, ht₁⟩ := cross3_eq_zero_imp_collinear hη_ne hcr1
    obtain ⟨t₂, ht₂⟩ := cross3_eq_zero_imp_collinear hη_ne hcr2
    have hcr12 : cross3 β₁ β₂ = 0 := by
      rw [ht₁, ht₂, cross3_smul_left, cross3_smul_right, cross3_self, smul_zero, smul_zero]
    have hcr_Δ : cross3 β₁ β₂ = Δ r • w r := by
      funext i; fin_cases i <;> dsimp [β₁, β₂, Δ, ν] <;> simp [dot3, cross3] <;> ring
    rw [hcr_Δ] at hcr12
    have hw0 : w r = 0 := by
      calc w r = (Δ r)⁻¹ • (Δ r • w r) := by rw [smul_smul, inv_mul_cancel₀ (hΔ_ne r), one_smul]
        _ = 0 := by rw [hcr12, smul_zero]
    exact hw_ne r hw0
  -- Directed κ_{rs} relation: for r ≠ s and η = w_r × w_s, ∃ κ ≠ 0, U_sᵀ η = κ U_rᵀ η and 2 κ² (ν_rᵀ w_s) = -Δ_s
  have hkappa_rel : ∀ {r s : Fin 9}, r ≠ s →
      let η := cross3 (w r) (w s)
      ∃ κ : K, κ ≠ 0 ∧
        dot3 η (u1 s) = κ * dot3 η (u1 r) ∧
        dot3 η (u2 s) = κ * dot3 η (u2 r) ∧
        2 * κ ^ 2 * dot3 (ν r) (w s) = -Δ s := by
    intro r s hrs η
    have hη_ne : η ≠ 0 := hw_nonpar hrs
    have hη_r : dot3 (w r) η = 0 := dot3_cross3_self_left (w r) (w s)
    have hη_s : dot3 (w s) η = 0 := dot3_cross3_self_right (w r) (w s)
    have hII_ηη := eq_II hrs η η hη_s hη_r
    have hG_ηη0 : dot3 η (matG3 (u r) (v s) *ᵥ η) = 0 := by linear_combination -hII_ηη
    rw [hGrs_on_perp r s η η hη_s] at hG_ηη0
    have hscale_s_ne : 2 * (3 * Δ s)⁻¹ ≠ 0 :=
      mul_ne_zero h2 (inv_ne_zero (mul_ne_zero h3 (hΔ_ne s)))
    have halt0 : dot3 η (u1 r) * dot3 (u2 s) η - dot3 η (u2 r) * dot3 (u1 s) η = 0 :=
      (mul_eq_zero.mp hG_ηη0).resolve_left hscale_s_ne
    rw [dot3_comm (u2 s) η, dot3_comm (u1 s) η] at halt0
    have hex_κ : ∃ κ : K, κ ≠ 0 ∧
        dot3 η (u1 s) = κ * dot3 η (u1 r) ∧ dot3 η (u2 s) = κ * dot3 η (u2 r) := by
      rcases hUr_inj_on_perp r η hη_r hη_ne with hu1r | hu2r
      · let κ := dot3 η (u1 s) * (dot3 η (u1 r))⁻¹
        have hk1 : dot3 η (u1 s) = κ * dot3 η (u1 r) := by
          dsimp [κ]; rw [mul_assoc, inv_mul_cancel₀ hu1r, mul_one]
        have hk2 : dot3 η (u2 s) = κ * dot3 η (u2 r) := by
          have hrel : dot3 η (u1 r) * (dot3 η (u2 s) - κ * dot3 η (u2 r)) = 0 := by
            dsimp [κ]
            calc dot3 η (u1 r) * (dot3 η (u2 s) - dot3 η (u1 s) * (dot3 η (u1 r))⁻¹ * dot3 η (u2 r))
                = dot3 η (u1 r) * dot3 η (u2 s) -
                    dot3 η (u1 s) * dot3 η (u2 r) * (dot3 η (u1 r) * (dot3 η (u1 r))⁻¹) := by ring
              _ = dot3 η (u1 r) * dot3 η (u2 s) - dot3 η (u2 r) * dot3 η (u1 s) := by
                    rw [mul_inv_cancel₀ hu1r, mul_one]; ring
              _ = 0 := halt0
          exact sub_eq_zero.mp ((mul_eq_zero.mp hrel).resolve_left hu1r)
        have hκ_ne : κ ≠ 0 := by
          intro h0
          rw [h0, zero_mul] at hk1 hk2
          rcases hUr_inj_on_perp s η hη_s hη_ne with hu1s | hu2s
          · exact hu1s hk1
          · exact hu2s hk2
        exact ⟨κ, hκ_ne, hk1, hk2⟩
      · let κ := dot3 η (u2 s) * (dot3 η (u2 r))⁻¹
        have hk2 : dot3 η (u2 s) = κ * dot3 η (u2 r) := by
          dsimp [κ]; rw [mul_assoc, inv_mul_cancel₀ hu2r, mul_one]
        have hk1 : dot3 η (u1 s) = κ * dot3 η (u1 r) := by
          have hrel : dot3 η (u2 r) * (dot3 η (u1 s) - κ * dot3 η (u1 r)) = 0 := by
            dsimp [κ]
            calc dot3 η (u2 r) * (dot3 η (u1 s) - dot3 η (u2 s) * (dot3 η (u2 r))⁻¹ * dot3 η (u1 r))
                = dot3 η (u2 r) * dot3 η (u1 s) -
                    dot3 η (u2 s) * dot3 η (u1 r) * (dot3 η (u2 r) * (dot3 η (u2 r))⁻¹) := by ring
              _ = -(dot3 η (u1 r) * dot3 η (u2 s) - dot3 η (u2 r) * dot3 η (u1 s)) := by
                    rw [mul_inv_cancel₀ hu2r, mul_one]; ring
              _ = 0 := by rw [halt0, neg_zero]
          exact sub_eq_zero.mp ((mul_eq_zero.mp hrel).resolve_left hu2r)
        have hκ_ne : κ ≠ 0 := by
          intro h0
          rw [h0, zero_mul] at hk1 hk2
          rcases hUr_inj_on_perp s η hη_s hη_ne with hu1s | hu2s
          · exact hu1s hk1
          · exact hu2s hk2
        exact ⟨κ, hκ_ne, hk1, hk2⟩
    rcases hex_κ with ⟨κ, hκ_ne, hk1, hk2⟩
    -- Choose β₀ ∈ w_s⊥ with η × β₀ = c_b • w_s (c_b ≠ 0)
    obtain ⟨q₀, q₁, _, _, s_s, hq₀, hq₁, hs_s_ne, hcr_q, _, _, _⟩ :=
      exists_perp_basis_of_ne_zero (hw_ne s)
    have hex_β₀ : ∃ β₀ : Fin 3 → K, dot3 (w s) β₀ = 0 ∧ cross3 η β₀ ≠ 0 := by
      by_cases hq0_cr : cross3 η q₀ ≠ 0
      · exact ⟨q₀, hq₀, hq0_cr⟩
      · push Not at hq0_cr
        refine ⟨q₁, hq₁, fun hq1_cr => ?_⟩
        obtain ⟨t₀, ht₀⟩ := cross3_eq_zero_imp_collinear hη_ne hq0_cr
        obtain ⟨t₁, ht₁⟩ := cross3_eq_zero_imp_collinear hη_ne hq1_cr
        have hcr_qq : cross3 q₀ q₁ = 0 := by
          rw [ht₀, ht₁, cross3_smul_left, cross3_smul_right, cross3_self, smul_zero, smul_zero]
        rw [hcr_q] at hcr_qq
        have hws0 : w s = 0 := by
          calc w s = s_s⁻¹ • (s_s • w s) := by rw [smul_smul, inv_mul_cancel₀ hs_s_ne, one_smul]
            _ = 0 := by rw [hcr_qq, smul_zero]
        exact hw_ne s hws0
    rcases hex_β₀ with ⟨β₀, hβ₀_s, hcr_ηβ_ne⟩
    have hcr_ws_zero : cross3 (w s) (cross3 η β₀) = 0 := by
      simp [bac_cab, hβ₀_s, hη_s]
    obtain ⟨c_b, hc_b⟩ := cross3_eq_zero_imp_collinear (hw_ne s) hcr_ws_zero
    have hc_b_ne : c_b ≠ 0 := by
      intro h0; rw [h0, zero_smul] at hc_b; exact hcr_ηβ_ne hc_b
    have hII_ηβ := eq_II hrs β₀ η hβ₀_s hη_r
    rw [hGrs_on_perp r s η β₀ hβ₀_s, hGrs_on_perp r s β₀ η hη_s] at hII_ηβ
    have hII_alt :
        (dot3 η (u1 r) * dot3 (u2 s) β₀ - dot3 η (u2 r) * dot3 (u1 s) β₀) =
        2 * (dot3 β₀ (u1 r) * dot3 (u2 s) η - dot3 β₀ (u2 r) * dot3 (u1 s) η) := by
      have hmul : (2 * (3 * Δ s)⁻¹) *
          ((dot3 η (u1 r) * dot3 (u2 s) β₀ - dot3 η (u2 r) * dot3 (u1 s) β₀) -
           2 * (dot3 β₀ (u1 r) * dot3 (u2 s) η - dot3 β₀ (u2 r) * dot3 (u1 s) η)) = 0 := by
        linear_combination hII_ηβ
      exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hscale_s_ne)
    -- Multiply LHS by κ and use U_sᵀ η = κ U_rᵀ η + Lagrange identity
    have hlhs_κ :
        κ * (dot3 η (u1 r) * dot3 (u2 s) β₀ - dot3 η (u2 r) * dot3 (u1 s) β₀) =
        c_b * Δ s := by
      calc κ * (dot3 η (u1 r) * dot3 (u2 s) β₀ - dot3 η (u2 r) * dot3 (u1 s) β₀)
          = (κ * dot3 η (u1 r)) * dot3 β₀ (u2 s) - (κ * dot3 η (u2 r)) * dot3 β₀ (u1 s) := by
              rw [dot3_comm (u2 s) β₀, dot3_comm (u1 s) β₀]; ring
        _ = dot3 η (u1 s) * dot3 β₀ (u2 s) - dot3 η (u2 s) * dot3 β₀ (u1 s) := by
              rw [← hk1, ← hk2]
        _ = dot3 (cross3 η β₀) (ν s) := lagrange_dot3_cross3 η β₀ (u1 s) (u2 s)
        _ = c_b * Δ s := by
              rw [hc_b, dot3_smul_left, dot3_comm (w s) (ν s)]
    have hrhs_κ :
        dot3 β₀ (u1 r) * dot3 (u2 s) η - dot3 β₀ (u2 r) * dot3 (u1 s) η =
        -(κ * c_b * dot3 (ν r) (w s)) := by
      calc dot3 β₀ (u1 r) * dot3 (u2 s) η - dot3 β₀ (u2 r) * dot3 (u1 s) η
          = κ * (-(dot3 η (u1 r) * dot3 β₀ (u2 r) - dot3 η (u2 r) * dot3 β₀ (u1 r))) := by
              rw [dot3_comm (u2 s) η, dot3_comm (u1 s) η, hk1, hk2]; ring
        _ = κ * (-dot3 (cross3 η β₀) (ν r)) := by
              rw [lagrange_dot3_cross3 η β₀ (u1 r) (u2 r)]
        _ = -(κ * c_b * dot3 (ν r) (w s)) := by
              rw [hc_b, dot3_smul_left, dot3_comm (w s) (ν r)]; ring
    have hcomb : c_b * (2 * κ ^ 2 * dot3 (ν r) (w s) + Δ s) = 0 := by
      have hmul_κ := congrArg (fun x => κ * x) hII_alt
      change κ * (dot3 η (u1 r) * dot3 (u2 s) β₀ - dot3 η (u2 r) * dot3 (u1 s) β₀) =
        κ * (2 * (dot3 β₀ (u1 r) * dot3 (u2 s) η - dot3 β₀ (u2 r) * dot3 (u1 s) η)) at hmul_κ
      rw [hlhs_κ, hrhs_κ] at hmul_κ
      linear_combination hmul_κ
    have hzero := (mul_eq_zero.mp hcomb).resolve_left hc_b_ne
    refine ⟨κ, hκ_ne, hk1, hk2, ?_⟩
    linear_combination hzero
  -- Equation (3.10): 4 (ν_rᵀ w_s)(ν_sᵀ w_r) = Δ_r Δ_s for all r ≠ s
  have hbiorthog_quarter : ∀ {r s : Fin 9}, r ≠ s →
      4 * (dot3 (ν r) (w s) * dot3 (ν s) (w r)) = Δ r * Δ s := by
    intro r s hrs
    obtain ⟨κ_rs, hκ_rs_ne, hk1_rs, hk2_rs, hsq_rs⟩ := hkappa_rel hrs
    obtain ⟨κ_sr, _, hk1_sr, hk2_sr, hsq_sr⟩ := hkappa_rel hrs.symm
    let η := cross3 (w r) (w s)
    have hη_swap : cross3 (w s) (w r) = -η := cross3_anticomm (w s) (w r)
    have hη_ne : η ≠ 0 := hw_nonpar hrs
    have hη_r : dot3 (w r) η = 0 := dot3_cross3_self_left (w r) (w s)
    have hprod1 : κ_sr * κ_rs = 1 := by
      rcases hUr_inj_on_perp r η hη_r hη_ne with hu1r | hu2r
      · have h1 : dot3 (-η) (u1 r) = κ_sr * dot3 (-η) (u1 s) := by
          simpa [hη_swap] using hk1_sr
        have hneg_l : dot3 (-η) (u1 r) = -dot3 η (u1 r) := by simp [dot3]; ring
        have hneg_r : dot3 (-η) (u1 s) = -dot3 η (u1 s) := by simp [dot3]; ring
        rw [hneg_l, hneg_r, hk1_rs] at h1
        have hlin : dot3 η (u1 r) * (κ_sr * κ_rs - 1) = 0 := by linear_combination h1
        exact sub_eq_zero.mp ((mul_eq_zero.mp hlin).resolve_left hu1r)
      · have h2_eq : dot3 (-η) (u2 r) = κ_sr * dot3 (-η) (u2 s) := by
          simpa [hη_swap] using hk2_sr
        have hneg_l : dot3 (-η) (u2 r) = -dot3 η (u2 r) := by simp [dot3]; ring
        have hneg_r : dot3 (-η) (u2 s) = -dot3 η (u2 s) := by simp [dot3]; ring
        rw [hneg_l, hneg_r, hk2_rs] at h2_eq
        have hlin : dot3 η (u2 r) * (κ_sr * κ_rs - 1) = 0 := by linear_combination h2_eq
        exact sub_eq_zero.mp ((mul_eq_zero.mp hlin).resolve_left hu2r)
    have hprod_sq : (2 * κ_rs ^ 2 * dot3 (ν r) (w s)) * (2 * κ_sr ^ 2 * dot3 (ν s) (w r)) =
        (-Δ s) * (-Δ r) := by
      rw [hsq_rs, hsq_sr]
    calc 4 * (dot3 (ν r) (w s) * dot3 (ν s) (w r))
        = (κ_sr * κ_rs) ^ 2 * (4 * (dot3 (ν r) (w s) * dot3 (ν s) (w r))) := by
            rw [hprod1, one_pow, one_mul]
      _ = (2 * κ_rs ^ 2 * dot3 (ν r) (w s)) * (2 * κ_sr ^ 2 * dot3 (ν s) (w r)) := by ring
      _ = Δ r * Δ s := by rw [hprod_sq]; ring
  -- 5.4. Nine rank-1 idempotents Q_r ∈ Mat_3(K) and trace-form discriminant obstruction
  let Q_mat : Fin 9 → Matrix (Fin 3) (Fin 3) K := fun r i j =>
    (Δ r)⁻¹ * w r i * ν r j
  have hQ_trace_prod : ∀ r s : Fin 9,
      (Q_mat r * Q_mat s).trace = equiangularGram9 K r s := by
    intro r s
    have htr : (Q_mat r * Q_mat s).trace =
        (Δ r)⁻¹ * (Δ s)⁻¹ * (dot3 (ν r) (w s) * dot3 (ν s) (w r)) := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three]
      dsimp [Q_mat, dot3]
      ring
    rw [htr]
    by_cases hrs : r = s
    · subst hrs
      simp only [equiangularGram9, ↓reduceIte]
      change (Δ r)⁻¹ * (Δ r)⁻¹ * (Δ r * Δ r) = 1
      have hΔr := hΔ_ne r
      field_simp [hΔr]
    · simp only [equiangularGram9, hrs, ↓reduceIte]
      have hq := hbiorthog_quarter hrs
      have hΔr := hΔ_ne r
      have hΔs := hΔ_ne s
      have h4 : (4 : K) ≠ 0 := by
        have : (4 : K) = 2 * 2 := by norm_num
        rw [this]; exact mul_ne_zero h2 h2
      field_simp [hΔr, hΔs, h4]
      linear_combination hq
  -- Congruence G_Q = C₉ᵀ G_std C₉ on Mat_3(K)
  let e9 : Fin 9 ≃ Idx9 :=
    Fintype.equivOfCardEq (by decide : Fintype.card (Fin 9) = Fintype.card Idx9)
  let C9 : Matrix (Fin 9) (Fin 9) K := fun a r => Q_mat r (e9 a).1 (e9 a).2
  let G9 : Matrix (Fin 9) (Fin 9) K := (stdTraceGram9 K).submatrix e9 e9
  have hG9_det : G9.det = -1 := by
    change (Matrix.reindex e9.symm e9.symm (stdTraceGram9 K)).det = -1
    rw [Matrix.det_reindex_self, det_stdTraceGram9]
  have hcong_Q : C9ᵀ * G9 * C9 = equiangularGram9 K := by
    ext r s
    rw [← hQ_trace_prod r s]
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_apply]
    have hsum1 : ∀ b : Fin 9,
        (∑ a : Fin 9, C9ᵀ r a * G9 a b) * C9 b s =
        (∑ ij : Idx9, Q_mat r ij.1 ij.2 * stdTraceGram9 K ij (e9 b)) *
          Q_mat s (e9 b).1 (e9 b).2 := by
      intro b
      congr 1
      simp only [C9, G9, Matrix.submatrix_apply]
      exact e9.sum_comp (fun ij => Q_mat r ij.1 ij.2 * stdTraceGram9 K ij (e9 b))
    simp_rw [hsum1]
    rw [e9.sum_comp
      (fun kl : Idx9 => (∑ ij : Idx9, Q_mat r ij.1 ij.2 * stdTraceGram9 K ij kl) * Q_mat s kl.1 kl.2)]
    rw [Fintype.sum_prod_type]
    have hinner : ∀ k l : Fin 3,
        (∑ ij : Idx9, Q_mat r ij.1 ij.2 * stdTraceGram9 K ij (k, l)) = Q_mat r l k := by
      intro k l
      rw [Fintype.sum_prod_type]
      fin_cases k <;> fin_cases l <;> simp [Fin.sum_univ_three, stdTraceGram9]
    simp_rw [hinner]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    rw [Finset.sum_comm]
  have hdet_cong : (C9ᵀ * G9 * C9).det = -(C9.det ^ 2) := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hG9_det]
    ring
  rw [hcong_Q, det_equiangularGram9 h2] at hdet_cong
  have h81_ne : (81 : K) ≠ 0 := by
    have : (81 : K) = 3 ^ 4 := by norm_num
    rw [this]; exact pow_ne_zero 4 h3
  have h256_ne : (256 : K) ≠ 0 := by
    have : (256 : K) = 2 ^ 8 := by norm_num
    rw [this]; exact pow_ne_zero 8 h2
  refine ⟨(256 * (81 : K)⁻¹) * C9.det, ?_⟩
  field_simp [h81_ne, h256_ne] at hdet_cong ⊢
  linear_combination -hdet_cong

/-- Transfer of the rank-`9` quadratic-reciprocity obstruction to `symEps3 K` and `T_RCB K b`. -/
theorem T_RCB_rank_9_implies_isSquare_neg_three {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {b : K} (hb : b ≠ 0)
    (hr9 : HasTensorRankLe (T_RCB K b) 9) :
    IsSquare (-3 : K) :=
  rank_9_implies_isSquare_neg_three h2 h3
    (((T_RCB_equiv_I2_eps3 h2 h3 hb).hasTensorRankLe_iff 9).mp hr9)

/-! ## Section 6: Proposition 1.3 Transfer & Field Corollaries (`ℚ`, `ℝ`, `ℂ`, `𝔽_p`) -/

/-- **Proposition 1.3 — Part 1 (`rcb_border_rank_nine`, via Theorem 1.1 Equation (1.3)):**
Over *every* field `K` with `char K ≠ 2, 3` and every `b ≠ 0`, both the ordinary and
`(1,2)`-symmetric formal algebraic border rank of `T_RCB K b` equal `9`. -/
theorem rcb_border_rank_nine {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {b : K} (hb : b ≠ 0) :
    HasSym12FormalBorderRankLe (T_RCB K b) 9 ∧
    HasFormalBorderRankLe (T_RCB K b) 9 ∧
    (∀ r : ℕ, HasFormalBorderRankLe (T_RCB K b) r → 9 ≤ r) ∧
    ¬ HasFormalBorderRankLe (T_RCB K b) 8 := by
  rcases T_RCB_hasSym12FormalBorderRankLe_nine h2 h3 hb with ⟨hs9, hb9⟩
  rcases T_RCB_borderRank_ge_nine h2 h3 hb with ⟨hge, _, hn8⟩
  exact ⟨hs9, hb9, hge, hn8⟩

/-- **Proposition 1.3 — Part 2 (`rcb_rank_dichotomy`, via Theorem 1.1 Equation (1.4)):**
Over *every* field `K` with `char K ≠ 2, 3` and every `b ≠ 0`:
- `HasTensorRankLe (T_RCB K b) 9 ↔ IsSquare (-3 : K)` and
  `HasSym12RankLe (T_RCB K b) 9 ↔ IsSquare (-3 : K)`;
- `¬ HasTensorRankLe (T_RCB K b) 8`;
- when `IsSquare (-3 : K)`, both ordinary and `(1,2)`-symmetric rank equal `9`;
- when `¬ IsSquare (-3 : K)`, both ordinary and `(1,2)`-symmetric rank equal `10` (so a strict
  border-rank gap `9 < 10` occurs). -/
theorem rcb_rank_dichotomy {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {b : K} (hb : b ≠ 0) :
    ¬ HasTensorRankLe (T_RCB K b) 8 ∧
    (HasTensorRankLe (T_RCB K b) 9 ↔ IsSquare (-3 : K)) ∧
    (HasSym12RankLe (T_RCB K b) 9 ↔ IsSquare (-3 : K)) ∧
    HasSym12RankLe (T_RCB K b) 10 ∧
    (¬ IsSquare (-3 : K) →
      ∀ r : ℕ, HasTensorRankLe (T_RCB K b) r → 10 ≤ r) := by
  have hn8_brk := (T_RCB_borderRank_ge_nine h2 h3 hb).2.2
  have hn8 : ¬ HasTensorRankLe (T_RCB K b) 8 :=
    fun h8 => hn8_brk h8.toFormalBorderRankLe
  have hiff_rk : HasTensorRankLe (T_RCB K b) 9 ↔ IsSquare (-3 : K) :=
    ⟨T_RCB_rank_9_implies_isSquare_neg_three h2 h3 hb,
     fun hsq => (T_RCB_hasSym12RankLe_nine_of_isSquare_neg_three h2 h3 hb hsq).2⟩
  have hiff_sym : HasSym12RankLe (T_RCB K b) 9 ↔ IsSquare (-3 : K) :=
    ⟨fun hs9 => T_RCB_rank_9_implies_isSquare_neg_three h2 h3 hb hs9.toTensorRankLe,
     fun hsq => (T_RCB_hasSym12RankLe_nine_of_isSquare_neg_three h2 h3 hb hsq).1⟩
  have hs10 := (T_RCB_hasSym12RankLe_ten h2 h3 hb).1
  refine ⟨hn8, hiff_rk, hiff_sym, hs10, ?_⟩
  intro hnsq r hr
  have hge9 : 9 ≤ r := (T_RCB_borderRank_ge_nine h2 h3 hb).1 r hr.toFormalBorderRankLe
  by_contra hlt10
  have hr9_eq : r = 9 := by omega
  subst hr9_eq
  exact hnsq (hiff_rk.mp hr)

/-- **Corollary (Proposition 1.3 & Theorem 1.1 over `ℚ`):** `rk_ℚ(T_RCB) = rk_ℚ^{sym_{1,2}}(T_RCB) = 10` and
`brk_ℚ(T_RCB) = 9` for every `b ∈ ℚˣ`. -/
theorem rcb_rank_rat {b : ℚ} (hb : b ≠ 0) :
    ¬ HasTensorRankLe (T_RCB ℚ b) 9 ∧
    HasSym12RankLe (T_RCB ℚ b) 10 ∧
    HasSym12FormalBorderRankLe (T_RCB ℚ b) 9 ∧
    ¬ HasFormalBorderRankLe (T_RCB ℚ b) 8 := by
  have hnsq : ¬ IsSquare (-3 : ℚ) := by
    rintro ⟨q, hq⟩
    have hnonneg : (0 : ℚ) ≤ q * q := mul_self_nonneg q
    linarith
  rcases rcb_rank_dichotomy (by norm_num : (2 : ℚ) ≠ 0) (by norm_num : (3 : ℚ) ≠ 0) hb with
    ⟨_, hiff9, _, hs10, _⟩
  rcases rcb_border_rank_nine (by norm_num : (2 : ℚ) ≠ 0) (by norm_num : (3 : ℚ) ≠ 0) hb with
    ⟨hbs9, _, _, hbn8⟩
  exact ⟨fun h9 => hnsq (hiff9.mp h9), hs10, hbs9, hbn8⟩

/-- **Corollary (Proposition 1.3 & Theorem 1.1 over `ℝ`):** `rk_ℝ(T_RCB) = rk_ℝ^{sym_{1,2}}(T_RCB) = 10` and
`brk_ℝ(T_RCB) = 9` for every `b ∈ ℝˣ`. -/
theorem rcb_rank_real {b : ℝ} (hb : b ≠ 0) :
    ¬ HasTensorRankLe (T_RCB ℝ b) 9 ∧
    HasSym12RankLe (T_RCB ℝ b) 10 ∧
    HasSym12FormalBorderRankLe (T_RCB ℝ b) 9 ∧
    ¬ HasFormalBorderRankLe (T_RCB ℝ b) 8 := by
  have hnsq : ¬ IsSquare (-3 : ℝ) := by
    rintro ⟨x, hx⟩
    have hnonneg : (0 : ℝ) ≤ x * x := mul_self_nonneg x
    linarith
  rcases rcb_rank_dichotomy (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0) hb with
    ⟨_, hiff9, _, hs10, _⟩
  rcases rcb_border_rank_nine (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0) hb with
    ⟨hbs9, _, _, hbn8⟩
  exact ⟨fun h9 => hnsq (hiff9.mp h9), hs10, hbs9, hbn8⟩

/-- **Corollary (Proposition 1.3 & Theorem 1.1 over `ℂ`):** `rk_ℂ(T_RCB) = rk_ℂ^{sym_{1,2}}(T_RCB) = 9` and
`brk_ℂ(T_RCB) = 9` for every `b ∈ ℂˣ`. -/
theorem rcb_rank_complex {b : ℂ} (hb : b ≠ 0) :
    HasSym12RankLe (T_RCB ℂ b) 9 ∧
    HasTensorRankLe (T_RCB ℂ b) 9 ∧
    ¬ HasFormalBorderRankLe (T_RCB ℂ b) 8 := by
  have hsq : IsSquare (-3 : ℂ) := by
    refine ⟨Complex.I * (Real.sqrt 3 : ℂ), ?_⟩
    have hs3 : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
      norm_cast
      exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    calc (-3 : ℂ) = (-1 : ℂ) * 3 := by ring
      _ = Complex.I ^ 2 * (Real.sqrt 3 : ℂ) ^ 2 := by rw [Complex.I_sq, hs3]
      _ = (Complex.I * (Real.sqrt 3 : ℂ)) * (Complex.I * (Real.sqrt 3 : ℂ)) := by ring
  rcases T_RCB_hasSym12RankLe_nine_of_isSquare_neg_three
    (by norm_num : (2 : ℂ) ≠ 0) (by norm_num : (3 : ℂ) ≠ 0) hb hsq with ⟨hs9, hr9⟩
  exact ⟨hs9, hr9,
    (T_RCB_borderRank_ge_nine (by norm_num : (2 : ℂ) ≠ 0) (by norm_num : (3 : ℂ) ≠ 0) hb).2.2⟩

/-- **Corollary (Proposition 1.3 & Theorem 1.1 over `AlgebraicClosure K`):** Over the algebraic closure of any field
`K` with `char K ≠ 2, 3` (`b ≠ 0`), `T_RCB` has exact ordinary and `(1,2)`-symmetric rank `9`. -/
theorem rcb_rank_algebraicClosure {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {b : K} (hb : b ≠ 0) :
    let φ : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
    HasSym12RankLe (T_RCB (AlgebraicClosure K) (φ b)) 9 ∧
    HasTensorRankLe (T_RCB (AlgebraicClosure K) (φ b)) 9 ∧
    ¬ HasFormalBorderRankLe (T_RCB (AlgebraicClosure K) (φ b)) 8 := by
  intro φ
  have h2L : (2 : AlgebraicClosure K) ≠ 0 := by
    intro h0; exact h2 (φ.injective (by rw [map_ofNat, h0, map_zero]))
  have h3L : (3 : AlgebraicClosure K) ≠ 0 := by
    intro h0; exact h3 (φ.injective (by rw [map_ofNat, h0, map_zero]))
  have hbL : φ b ≠ 0 := fun h0 => hb (φ.injective (by rw [h0, map_zero]))
  have hsq : IsSquare (-3 : AlgebraicClosure K) := IsAlgClosed.isSquare (-3 : AlgebraicClosure K)
  rcases T_RCB_hasSym12RankLe_nine_of_isSquare_neg_three h2L h3L hbL hsq with ⟨hs9, hr9⟩
  exact ⟨hs9, hr9, (T_RCB_borderRank_ge_nine h2L h3L hbL).2.2⟩

/-- Quadratic-reciprocity criterion for `-3 ∈ (𝔽_pˣ)²` (`p ≥ 5` prime):
`legendreSym p (-3) = legendreSym 3 p`, so `IsSquare (-3 : ZMod p) ↔ p % 3 = 1` (and
`¬ IsSquare (-3 : ZMod p) ↔ p % 3 = 2`). -/
theorem zmod_isSquare_neg_three_iff {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) :
    (IsSquare (-3 : ZMod p) ↔ p % 3 = 1) ∧
    (¬ IsSquare (-3 : ZMod p) ↔ p % 3 = 2) := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hp_prime : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have h3_ne_zmod : ((-3 : ℤ) : ZMod p) ≠ 0 := by
    intro h0
    have h30 : ((3 : ℕ) : ZMod p) = 0 := by
      have : (-((3 : ℕ) : ZMod p)) = 0 := by simpa using h0
      exact neg_eq_zero.mp this
    have hdvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h30
    have hle : p ≤ 3 := Nat.le_of_dvd (by decide) hdvd
    omega
  have hp_mod2 : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two hp_prime).mpr hp2
  have hp_mod3_ne0 : p % 3 ≠ 0 := by
    intro hm0
    have hdvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero hm0
    rcases hp_prime.eq_one_or_self_of_dvd 3 hdvd with h | h <;> omega
  have hp_mod3_cases : p % 3 = 1 ∨ p % 3 = 2 := by omega
  have hleg_eq : legendreSym p (-3) = legendreSym 3 p := by
    rw [legendreSym.at_neg hp2 3]
    have hp_mod4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases hp_mod4 with hp4 | hp4
    · have hqr := legendreSym.quadratic_reciprocity_one_mod_four hp4 (by decide : 3 ≠ 2)
      rw [ZMod.χ₄_nat_one_mod_four hp4, one_mul]
      simpa using hqr.symm
    · have hqr := legendreSym.quadratic_reciprocity_three_mod_four (by decide : 3 % 4 = 3) hp4
      rw [ZMod.χ₄_nat_three_mod_four hp4]
      have hqr' : legendreSym p 3 = -legendreSym 3 (p : ℤ) := by simpa using hqr
      linear_combination -hqr'
  have hsq_cast : IsSquare ((-3 : ℤ) : ZMod p) ↔ IsSquare (-3 : ZMod p) := by norm_cast
  have hiff1 : IsSquare (-3 : ZMod p) ↔ p % 3 = 1 := by
    rw [← hsq_cast, ← legendreSym.eq_one_iff p h3_ne_zmod, hleg_eq, legendreSym.mod 3 p]
    have hmod_cast : (p : ℤ) % (3 : ℕ) = ((p % 3 : ℕ) : ℤ) := Int.ofNat_mod_ofNat p 3
    rw [hmod_cast]
    rcases hp_mod3_cases with h1 | h2_mod
    · rw [h1]; decide
    · rw [h2_mod]
      have hl2 : legendreSym 3 2 = -1 := by decide
      rw [show ((2 : ℕ) : ℤ) = 2 from rfl, hl2]
      omega
  refine ⟨hiff1, ?_⟩
  rw [hiff1]
  omega

/-- **Corollary (Proposition 1.3 & Theorem 1.1 over prime fields `𝔽_p`, `p ≥ 5`):**
For every prime `p ≥ 5` and `b ∈ (ZMod p)ˣ`:
- `p ≡ 1 (mod 3)` implies `rk_{𝔽_p}(T_RCB) = rk_{𝔽_p}^{sym_{1,2}}(T_RCB) = 9`;
- `p ≡ 2 (mod 3)` implies `rk_{𝔽_p}(T_RCB) = rk_{𝔽_p}^{sym_{1,2}}(T_RCB) = 10` (with formal
  border rank `9`, so a strict border-rank gap occurs). -/
theorem rcb_rank_zmod_prime {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {b : ZMod p} (hb : b ≠ 0) :
    HasSym12FormalBorderRankLe (T_RCB (ZMod p) b) 9 ∧
    ¬ HasFormalBorderRankLe (T_RCB (ZMod p) b) 8 ∧
    (p % 3 = 1 → HasSym12RankLe (T_RCB (ZMod p) b) 9 ∧ HasTensorRankLe (T_RCB (ZMod p) b) 9) ∧
    (p % 3 = 2 →
      ¬ HasTensorRankLe (T_RCB (ZMod p) b) 9 ∧
      HasSym12RankLe (T_RCB (ZMod p) b) 10 ∧
      (∀ r : ℕ, HasTensorRankLe (T_RCB (ZMod p) b) r → 10 ≤ r)) := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h0)
    have hle : p ≤ 2 := Nat.le_of_dvd (by decide) hdvd
    omega
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h0
    have hdvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp (by simpa using h0)
    have hle : p ≤ 3 := Nat.le_of_dvd (by decide) hdvd
    omega
  rcases rcb_border_rank_nine h2 h3 hb with ⟨hbs9, _, _, hbn8⟩
  rcases rcb_rank_dichotomy h2 h3 hb with ⟨_, hiff_rk, hiff_sym, hs10, hge10⟩
  rcases zmod_isSquare_neg_three_iff hp5 with ⟨hqr1, hqr2⟩
  refine ⟨hbs9, hbn8, ?_, ?_⟩
  · intro hp1
    have hsq := hqr1.mpr hp1
    exact ⟨hiff_sym.mpr hsq, hiff_rk.mpr hsq⟩
  · intro hp2
    have hnsq := hqr2.mpr hp2
    exact ⟨fun hr9 => hnsq (hiff_rk.mp hr9), hs10, hge10 hnsq⟩

end SemaevRCB
