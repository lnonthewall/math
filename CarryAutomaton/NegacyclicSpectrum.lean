module

public import CarryAutomaton.Defs
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

@[expose] public section

/-!
# Negacyclic Walsh–Hadamard Spectrum, Exact Ranks, and Spectral Cover Bounds

Formalization of Section 4 (Theorem 4.1 & Remark 4.3) of Paper 2 (where the borrow core `C_t` is
formalized as `K_coreRel s` / `K_coreMat R s` with `s = t - 1`):
1. Orthonormal Walsh–Hadamard block-diagonalization of the borrow core `C_t` (`K_coreMat`) into
   character matrices `H_α` (`walsh_conj_K_coreMat`; Theorem 4.1(a), Equation (4.3)).
2. Kronecker factorization `H_α = J_{2^{s-r}} ⊗ H̃_α` and exact diagonal-sign conjugation
   `D H̃_α D = ∏_{j=0}^{r-1} (I + (-1)^{α_j} T^{2^j})` in the negacyclic shift `T`
   (Theorem 4.1(a), Equation (4.4)).
3. Unitary negacyclic DFT diagonalization of `T` and `G_α(T)`, closed-form positive singular values,
   invertibility of `H̃_α` over `ℚ` and `ℂ`, and exact rational/complex ranks
   `rank(C_t) = (2 · 4^s + 1) / 3` and `rank(M_t) = (4^t + 2) / 3` (Theorem 4.1(b)–(c),
   Equation (4.5)).
4. Sharp trigonometric spectral envelope `‖H_α‖₂ ≤ 2^{s-r} / sin(π / 2^{r+1})`, exact equality
   characterization `α ∈ {e_r, e_r + e_{r-1}}` for `r ≥ 2`, exact centered spectral norm
   `Λ(C_t) = 2^{t - 3/2}` (`t ≥ 2`, `Λ(C_1) = 0`), second-tier bound `2^{t-1} / (4 sin(π/8))`,
   and `Λ(M_t) = 2^t` (Theorem 4.1(c), Equations (4.6)–(4.7)).
5. Overlap-safe centered spectral biclique-cover lower bound `Λ · W_label ≥ 2(1 - p)|E|` and its
   exponential separation (`Θ(1)` vs `Θ(2^{s/2})`) on `C_t` (Remark 4.3).
-/

namespace CarryAutomaton

open Finset BigOperators Matrix

/-! ### 1. `𝔽₂^s` Characters and Walsh–Hadamard Block Diagonalization (Theorem 4.1(a), Part 1) -/

/-- Standard `𝔽₂`-inner product `⟨α, β⟩ = ∑_{i < s} α_i β_i` in `ZMod 2`. -/
def f2Inner (s : ℕ) (α β : Fin s → ZMod 2) : ZMod 2 :=
  ∑ i : Fin s, α i * β i

lemma f2Inner_comm (s : ℕ) (α β : Fin s → ZMod 2) :
    f2Inner s α β = f2Inner s β α := by
  simp only [f2Inner, mul_comm]

lemma f2Inner_add_left (s : ℕ) (α₁ α₂ β : Fin s → ZMod 2) :
    f2Inner s (α₁ + α₂) β = f2Inner s α₁ β + f2Inner s α₂ β := by
  simp only [f2Inner, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma f2Inner_add_right (s : ℕ) (α β₁ β₂ : Fin s → ZMod 2) :
    f2Inner s α (β₁ + β₂) = f2Inner s α β₁ + f2Inner s α β₂ := by
  simp only [f2Inner, Pi.add_apply, mul_add, Finset.sum_add_distrib]

@[simp]
lemma f2Inner_zero_left (s : ℕ) (β : Fin s → ZMod 2) :
    f2Inner s 0 β = 0 := by
  simp [f2Inner]

@[simp]
lemma f2Inner_zero_right (s : ℕ) (α : Fin s → ZMod 2) :
    f2Inner s α 0 = 0 := by
  simp [f2Inner]

lemma zmod2_eq_zero_or_one : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

@[simp]
private lemma zmod2_val_one : (1 : ZMod 2).val = 1 := rfl

@[simp]
private lemma zmod2_two_eq_zero : (2 : ZMod 2) = 0 := by decide

lemma zmod2_ne_zero_iff : ∀ a : ZMod 2, a ≠ 0 ↔ a = 1 := by decide

lemma zmod2_add_self : ∀ a : ZMod 2, a + a = 0 := by decide

lemma zmod2_add_eq_zero_iff : ∀ a b : ZMod 2, a + b = 0 ↔ a = b := by decide

lemma zmod2_add_eq_iff : ∀ a b c : ZMod 2, a + b = c ↔ b = a + c := by decide

lemma f2_vec_add_self (s : ℕ) (x : Fin s → ZMod 2) : x + x = 0 := by
  ext i
  exact zmod2_add_self (x i)

lemma f2_vec_add_eq_iff (s : ℕ) (x y c : Fin s → ZMod 2) :
    x + y = c ↔ y = x + c := by
  constructor <;> intro h <;> ext i
  · exact (zmod2_add_eq_iff (x i) (y i) (c i)).mp (congr_fun h i)
  · exact (zmod2_add_eq_iff (x i) (y i) (c i)).mpr (congr_fun h i)

lemma f2_vec_add_eq_zero_iff (s : ℕ) (α β : Fin s → ZMod 2) :
    α + β = 0 ↔ α = β := by
  constructor <;> intro h <;> ext i
  · exact (zmod2_add_eq_zero_iff (α i) (β i)).mp (congr_fun h i)
  · exact (zmod2_add_eq_zero_iff (α i) (β i)).mpr (congr_fun h i)

lemma neg_one_pow_zmod2_add {R : Type*} [Ring R] (a b : ZMod 2) :
    (-1 : R) ^ (a + b).val = (-1 : R) ^ a.val * (-1 : R) ^ b.val := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one b with rfl | rfl
  · simp
  · simp
  · simp
  · change (-1 : R) ^ (0 : ZMod 2).val = (-1 : R) ^ 1 * (-1 : R) ^ 1
    simp

lemma neg_one_pow_zmod2_mul_self {R : Type*} [Ring R] (a : ZMod 2) :
    (-1 : R) ^ a.val * (-1 : R) ^ a.val = 1 := by
  rw [← neg_one_pow_zmod2_add, zmod2_add_self]
  simp

lemma neg_one_pow_zmod2_eq_one_or_neg_one {R : Type*} [Ring R] (a : ZMod 2) :
    (-1 : R) ^ a.val = 1 ∨ (-1 : R) ^ a.val = -1 := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl
  · left; simp
  · right; simp

lemma neg_one_pow_zmod2_sum {R : Type*} [CommRing R] {ι : Type*}
    (S : Finset ι) (f : ι → ZMod 2) :
    (-1 : R) ^ (∑ i ∈ S, f i).val = ∏ i ∈ S, (-1 : R) ^ (f i).val := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    rw [Finset.sum_insert hi, neg_one_pow_zmod2_add, Finset.prod_insert hi, ih]

lemma sum_zmod2_char {R : Type*} [CommRing R] (a : ZMod 2) :
    (∑ b : ZMod 2, (-1 : R) ^ (a * b).val) = if a = 0 then 2 else 0 := by
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [huniv, Finset.sum_pair (by decide)]
  rcases zmod2_eq_zero_or_one a with rfl | rfl
  · simp [one_add_one_eq_two]
  · simp

/-- Exact character orthogonality over any commutative ring `R`:
`∑_{x ∈ 𝔽₂^s} (-1)^{⟨α, x⟩} = 2^s` if `α = 0`, else `0`. -/
theorem sum_f2Inner_sign {R : Type*} [CommRing R] (s : ℕ) (α : Fin s → ZMod 2) :
    (∑ x : Fin s → ZMod 2, (-1 : R) ^ (f2Inner s α x).val) =
      if α = 0 then (2 : R) ^ s else 0 := by
  by_cases hα : α = 0
  · subst hα
    simp
  · have hprod :
        (∑ x : Fin s → ZMod 2, (-1 : R) ^ (f2Inner s α x).val) =
          ∏ i : Fin s, ∑ b : ZMod 2, (-1 : R) ^ (α i * b).val := by
      rw [Fintype.prod_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      exact neg_one_pow_zmod2_sum Finset.univ (fun i => α i * x i)
    rw [hprod]
    simp only [hα, ↓reduceIte]
    have ⟨i₀, hi₀⟩ : ∃ i : Fin s, α i ≠ 0 := by
      by_contra h
      exact hα (funext fun i => not_not.mp fun hni => h ⟨i, hni⟩)
    refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
    rw [sum_zmod2_char]
    simp [hi₀]

/-- Unnormalized `2^s × 2^s` Walsh–Hadamard matrix `W_s[α, x] = (-1)^{⟨α, x⟩}` over `R`. -/
def W_unnorm (R : Type*) [CommRing R] (s : ℕ) :
    Matrix (Fin s → ZMod 2) (Fin s → ZMod 2) R :=
  fun α x => (-1 : R) ^ (f2Inner s α x).val

@[simp]
theorem W_unnorm_transpose (R : Type*) [CommRing R] (s : ℕ) :
    (W_unnorm R s)ᵀ = W_unnorm R s := by
  ext α x
  simp [W_unnorm, f2Inner_comm]

theorem W_unnorm_mul_self (R : Type*) [CommRing R] (s : ℕ) :
    W_unnorm R s * W_unnorm R s =
      ((2 : R) ^ s) • (1 : Matrix (Fin s → ZMod 2) (Fin s → ZMod 2) R) := by
  ext α β
  simp only [Matrix.mul_apply, W_unnorm, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have hcombine : ∀ x : Fin s → ZMod 2,
      (-1 : R) ^ (f2Inner s α x).val * (-1 : R) ^ (f2Inner s x β).val =
        (-1 : R) ^ (f2Inner s (α + β) x).val := by
    intro x
    rw [f2Inner_comm s x β, ← neg_one_pow_zmod2_add, ← f2Inner_add_left]
  simp_rw [hcombine, sum_f2Inner_sign]
  by_cases hαβ : α = β
  · subst hαβ
    rw [f2_vec_add_self]
    simp
  · have hne : α + β ≠ 0 := fun h0 => hαβ ((f2_vec_add_eq_zero_iff s α β).mp h0)
    simp [hαβ, hne]

/-- Orthonormal Walsh–Hadamard matrix `H_s = 2^{-s/2} [(-1)^{⟨α, x'⟩}]` over `ℝ`. -/
noncomputable def H_s (s : ℕ) :
    Matrix (Fin s → ZMod 2) (Fin s → ZMod 2) ℝ :=
  ((Real.sqrt 2) ^ s)⁻¹ • W_unnorm ℝ s

/-- Orthonormal Walsh–Hadamard matrix `H_s` over `ℂ`. -/
noncomputable def H_s_C (s : ℕ) :
    Matrix (Fin s → ZMod 2) (Fin s → ZMod 2) ℂ :=
  (((Real.sqrt 2) ^ s : ℝ)⁻¹ : ℂ) • W_unnorm ℂ s

theorem H_s_scale_eq_rpow (s : ℕ) :
    ((Real.sqrt 2) ^ s)⁻¹ = (2 : ℝ) ^ (-(s : ℝ) / 2) := by
  have h2 : (0 : ℝ) < 2 := by positivity
  rw [← Real.rpow_natCast (Real.sqrt 2) s, Real.sqrt_eq_rpow, ← Real.rpow_mul h2.le,
    ← Real.rpow_neg h2.le]
  ring_nf

@[simp]
theorem H_s_transpose (s : ℕ) : (H_s s)ᵀ = H_s s := by
  simp [H_s]

theorem H_s_mul_self (s : ℕ) : H_s s * H_s s = 1 := by
  simp only [H_s, Matrix.smul_mul, Matrix.mul_smul, W_unnorm_mul_self, smul_smul]
  have hsq : (Real.sqrt 2 ^ s)⁻¹ * ((Real.sqrt 2 ^ s)⁻¹ * (2 : ℝ) ^ s) = 1 := by
    have hpow : (Real.sqrt 2) ^ s * (Real.sqrt 2) ^ s = (2 : ℝ) ^ s := by
      rw [← mul_pow, Real.mul_self_sqrt (by positivity)]
    have hne : (Real.sqrt 2) ^ s ≠ 0 := by positivity
    rw [← hpow]
    field_simp [hne]
  rw [hsq, one_smul]

@[simp]
theorem H_s_C_conjTranspose (s : ℕ) : (H_s_C s)ᴴ = H_s_C s := by
  ext α x
  simp only [H_s_C, Matrix.conjTranspose_apply, Matrix.smul_apply, W_unnorm, smul_eq_mul,
    star_mul', Complex.star_def, map_inv₀, Complex.conj_ofReal, map_pow, map_neg, map_one,
    f2Inner_comm]

theorem H_s_C_mul_self (s : ℕ) : H_s_C s * H_s_C s = 1 := by
  simp only [H_s_C, Matrix.smul_mul, Matrix.mul_smul, W_unnorm_mul_self, smul_smul]
  have hsq : (((Real.sqrt 2 ^ s : ℝ)⁻¹ : ℂ) * (((Real.sqrt 2 ^ s : ℝ)⁻¹ : ℂ) * (2 : ℂ) ^ s)) = 1 := by
    have hpow : (Real.sqrt 2) ^ s * (Real.sqrt 2) ^ s = (2 : ℝ) ^ s := by
      rw [← mul_pow, Real.mul_self_sqrt (by positivity)]
    have hne : ((Real.sqrt 2 ^ s : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (by positivity : (Real.sqrt 2) ^ s ≠ 0)
    have hpowC : ((Real.sqrt 2 ^ s : ℝ) : ℂ) * ((Real.sqrt 2 ^ s : ℝ) : ℂ) = (2 : ℂ) ^ s := by
      exact_mod_cast hpow
    rw [← hpowC]
    field_simp [hne]
  rw [hsq, one_smul]

/-- Character matrix `H_α[w', z'] = (-1)^{⟨α, c(w', z')⟩}` of size `2^s × 2^s` over `R`
(Paper 2, Section 4, eq. (4.3)). -/
def H_alpha (R : Type*) [CommRing R] (s : ℕ) (α : Fin s → ZMod 2) :
    Matrix (Fin (2 ^ s)) (Fin (2 ^ s)) R :=
  fun w z => (-1 : R) ^ (f2Inner s α (borrowVec s w z)).val

/-- Unnormalized Walsh conjugation identity over any commutative ring `R`:
`((W_s ⊗ I_{2^s}) K_t (W_s ⊗ I_{2^s}))[(α, w), (β, z)] = 2^s H_α[w, z]` if `α = β`, else `0`. -/
theorem walsh_conj_K_coreMat_unnorm (R : Type*) [CommRing R] (s : ℕ)
    (α β : Fin s → ZMod 2) (w z : Fin (2 ^ s)) :
    ((Matrix.kroneckerMap (· * ·) (W_unnorm R s) (1 : Matrix (Fin (2 ^ s)) (Fin (2 ^ s)) R)) *
        K_coreMat R s *
      (Matrix.kroneckerMap (· * ·) (W_unnorm R s) (1 : Matrix (Fin (2 ^ s)) (Fin (2 ^ s)) R)))
        (α, w) (β, z) =
      if α = β then (2 : R) ^ s * H_alpha R s α w z else 0 := by
  simp only [Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]
  rw [Fintype.sum_prod_type]
  have houter : ∀ x : Fin s → ZMod 2, ∀ w' : Fin (2 ^ s),
      (∑ u : (Fin s → ZMod 2) × Fin (2 ^ s),
          (W_unnorm R s α u.1 * if w = u.2 then 1 else 0) * K_coreMat R s u (x, w')) *
        (W_unnorm R s x β * if w' = z then 1 else 0) =
      if w' = z then W_unnorm R s α (x + borrowVec s w z) * W_unnorm R s x β else 0 := by
    intro x w'
    by_cases hwz : w' = z
    · subst hwz
      simp only [↓reduceIte, mul_one]
      rw [Fintype.sum_prod_type]
      have hsum_w : ∀ u₁ : Fin s → ZMod 2,
          (∑ u₂ : Fin (2 ^ s), (W_unnorm R s α u₁ * if w = u₂ then 1 else 0) *
              K_coreMat R s (u₁, u₂) (x, w')) =
            W_unnorm R s α u₁ * K_coreMat R s (u₁, w) (x, w') := by
        intro u₁
        rw [Finset.sum_eq_single w]
        · simp
        · intro u₂ _ hu₂
          simp [Ne.symm hu₂]
        · intro hw
          exact absurd (Finset.mem_univ w) hw
      simp_rw [hsum_w]
      have hsum_x : (∑ u₁ : Fin s → ZMod 2, W_unnorm R s α u₁ * K_coreMat R s (u₁, w) (x, w')) =
          W_unnorm R s α (x + borrowVec s w w') := by
        rw [Finset.sum_eq_single (x + borrowVec s w w')]
        · have hrel : K_coreRel s (x + borrowVec s w w', w) (x, w') := by
            simp only [K_coreRel]
            rw [add_comm x (borrowVec s w w'), add_assoc, f2_vec_add_self, add_zero]
          simp [K_coreMat, hrel]
        · intro u₁ _ hu₁
          have hnrel : ¬ K_coreRel s (u₁, w) (x, w') := by
            intro hrel
            simp only [K_coreRel] at hrel
            have heq := (f2_vec_add_eq_iff s x u₁ (borrowVec s w w')).mp (by simpa [add_comm] using hrel)
            exact hu₁ heq
          simp [K_coreMat, hnrel]
        · intro hmem
          exact absurd (Finset.mem_univ _) hmem
      rw [hsum_x]
    · simp [hwz]
  simp_rw [houter]
  have hcollapse : ∀ x : Fin s → ZMod 2,
      (∑ w' : Fin (2 ^ s),
        if w' = z then W_unnorm R s α (x + borrowVec s w z) * W_unnorm R s x β else 0) =
        W_unnorm R s α (x + borrowVec s w z) * W_unnorm R s x β := by
    intro x
    simp
  simp_rw [hcollapse]
  have hterm : ∀ x : Fin s → ZMod 2,
      W_unnorm R s α (x + borrowVec s w z) * W_unnorm R s x β =
        H_alpha R s α w z * (-1 : R) ^ (f2Inner s (α + β) x).val := by
    intro x
    simp only [W_unnorm, H_alpha]
    rw [f2Inner_add_right, neg_one_pow_zmod2_add, f2Inner_comm s x β,
      mul_comm _ ((-1 : R) ^ (f2Inner s α (borrowVec s w z)).val),
      mul_assoc, ← neg_one_pow_zmod2_add, ← f2Inner_add_left]
  simp_rw [hterm, ← Finset.mul_sum, sum_f2Inner_sign, if_congr (f2_vec_add_eq_zero_iff s α β) rfl rfl]
  split_ifs with hαβ
  · ring
  · simp

/-- **Theorem 4.1(a), Part 1 (Orthonormal Walsh–Hadamard Block-Diagonalization over `ℝ`)**:
`((H_s ⊗ I_{2^s}) C_t (H_s ⊗ I_{2^s}))[(α, w), (β, z)] = H_α[w, z]` if `α = β`, else `0`
(Paper 2, eq. (4.3)). -/
theorem walsh_conj_K_coreMat (s : ℕ) (α β : Fin s → ZMod 2) (w z : Fin (2 ^ s)) :
    ((Matrix.kroneckerMap (· * ·) (H_s s) (1 : Matrix (Fin (2 ^ s)) (Fin (2 ^ s)) ℝ)) *
        K_coreMat ℝ s *
      (Matrix.kroneckerMap (· * ·) (H_s s) (1 : Matrix (Fin (2 ^ s)) (Fin (2 ^ s)) ℝ)))
        (α, w) (β, z) =
      if α = β then H_alpha ℝ s α w z else 0 := by
  let W_I := Matrix.kroneckerMap (· * ·) (W_unnorm ℝ s) (1 : Matrix (Fin (2 ^ s)) (Fin (2 ^ s)) ℝ)
  have hkron :
      Matrix.kroneckerMap (· * ·) (H_s s) (1 : Matrix (Fin (2 ^ s)) (Fin (2 ^ s)) ℝ) =
        ((Real.sqrt 2) ^ s)⁻¹ • W_I := by
    ext ⟨a, u⟩ ⟨b, v⟩
    simp [W_I, H_s, mul_assoc]
  have hmul :
      (((Real.sqrt 2) ^ s)⁻¹ • W_I) * K_coreMat ℝ s * (((Real.sqrt 2) ^ s)⁻¹ • W_I) =
        (((Real.sqrt 2) ^ s)⁻¹ * ((Real.sqrt 2) ^ s)⁻¹) • (W_I * K_coreMat ℝ s * W_I) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  rw [hkron, hmul, Matrix.smul_apply, walsh_conj_K_coreMat_unnorm, smul_eq_mul]
  have hsq : ((Real.sqrt 2) ^ s)⁻¹ * ((Real.sqrt 2) ^ s)⁻¹ * (2 : ℝ) ^ s = 1 := by
    have hpow : (Real.sqrt 2) ^ s * (Real.sqrt 2) ^ s = (2 : ℝ) ^ s := by
      rw [← mul_pow, Real.mul_self_sqrt (by positivity)]
    have hne : (Real.sqrt 2) ^ s ≠ 0 := by positivity
    rw [← hpow]
    field_simp [hne]
  split_ifs
  · rw [← mul_assoc, hsq, one_mul]
  · simp

/-- Orthonormal Walsh–Hadamard block-diagonalization over `ℂ`. -/
theorem walsh_conj_K_coreMat_C (s : ℕ) (α β : Fin s → ZMod 2) (w z : Fin (2 ^ s)) :
    ((Matrix.kroneckerMap (· * ·) (H_s_C s) (1 : Matrix (Fin (2 ^ s)) (Fin (2 ^ s)) ℂ)) *
        K_coreMat ℂ s *
      (Matrix.kroneckerMap (· * ·) (H_s_C s) (1 : Matrix (Fin (2 ^ s)) (Fin (2 ^ s)) ℂ)))
        (α, w) (β, z) =
      if α = β then H_alpha ℂ s α w z else 0 := by
  let W_I := Matrix.kroneckerMap (· * ·) (W_unnorm ℂ s) (1 : Matrix (Fin (2 ^ s)) (Fin (2 ^ s)) ℂ)
  have hkron :
      Matrix.kroneckerMap (· * ·) (H_s_C s) (1 : Matrix (Fin (2 ^ s)) (Fin (2 ^ s)) ℂ) =
        (((Real.sqrt 2) ^ s : ℝ)⁻¹ : ℂ) • W_I := by
    ext ⟨a, u⟩ ⟨b, v⟩
    simp [W_I, H_s_C, mul_assoc]
  have hmul :
      ((((Real.sqrt 2) ^ s : ℝ)⁻¹ : ℂ) • W_I) * K_coreMat ℂ s *
          ((((Real.sqrt 2) ^ s : ℝ)⁻¹ : ℂ) • W_I) =
        ((((Real.sqrt 2) ^ s : ℝ)⁻¹ : ℂ) * (((Real.sqrt 2) ^ s : ℝ)⁻¹ : ℂ)) •
          (W_I * K_coreMat ℂ s * W_I) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  rw [hkron, hmul, Matrix.smul_apply, walsh_conj_K_coreMat_unnorm, smul_eq_mul]
  have hsq : (((Real.sqrt 2) ^ s : ℝ)⁻¹ : ℂ) * (((Real.sqrt 2) ^ s : ℝ)⁻¹ : ℂ) * (2 : ℂ) ^ s = 1 := by
    have hpow : (Real.sqrt 2) ^ s * (Real.sqrt 2) ^ s = (2 : ℝ) ^ s := by
      rw [← mul_pow, Real.mul_self_sqrt (by positivity)]
    have hne : ((Real.sqrt 2 ^ s : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (by positivity : (Real.sqrt 2) ^ s ≠ 0)
    have hpowC : ((Real.sqrt 2 ^ s : ℝ) : ℂ) * ((Real.sqrt 2 ^ s : ℝ) : ℂ) = (2 : ℂ) ^ s := by
      exact_mod_cast hpow
    rw [← hpowC]
    field_simp [hne]
  split_ifs
  · rw [← mul_assoc, hsq, one_mul]
  · simp

/-! ### 2. Factorization and Exact Negacyclic Conjugation (Theorem 4.1(a), Part 2) -/

/-- `n × n` all-ones matrix `J_n`. -/
def allOnesMat (R : Type*) [One R] (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  fun _ _ => 1

/-- Standard `1`-indexed unit vector `e_r ∈ 𝔽₂^s` (`1 ≤ r ≤ s`, placed at `0`-based index `r - 1`). -/
def stdUnitVec (s r : ℕ) : Fin s → ZMod 2 :=
  fun i => if i.val + 1 = r then 1 else 0

/-- `α ∈ 𝔽₂^s` has highest nonzero bit `r` (`1 ≤ r ≤ s`, i.e., `α_{r} = 1` and `α_i = 0` for `i > r`). -/
def HasHighestBit (s : ℕ) (α : Fin s → ZMod 2) (r : ℕ) : Prop :=
  ∃ (_ : 1 ≤ r) (hrs : r ≤ s),
    α ⟨r - 1, by omega⟩ = 1 ∧ ∀ i : Fin s, r ≤ i.val → α i = 0

/-- `1`-indexed coefficient `α_j` with convention `α_0 = 0` (matching Paper 2, eq. (4.4)). -/
def alphaCoeff (s : ℕ) (α : Fin s → ZMod 2) (j : ℕ) : ZMod 2 :=
  if j = 0 then 0
  else if hj : j - 1 < s then α ⟨j - 1, hj⟩ else 0

@[simp]
lemma alphaCoeff_zero (s : ℕ) (α : Fin s → ZMod 2) : alphaCoeff s α 0 = 0 := rfl

lemma alphaCoeff_succ_of_lt {s j : ℕ} (hj : j < s) (α : Fin s → ZMod 2) :
    alphaCoeff s α (j + 1) = α ⟨j, hj⟩ := by
  simp [alphaCoeff, hj]

lemma alphaCoeff_top_eq_one {s r : ℕ} {α : Fin s → ZMod 2} (h : HasHighestBit s α r) :
    alphaCoeff s α r = 1 := by
  rcases h with ⟨hr1, hrs, htop, _⟩
  have hr0 : r ≠ 0 := by omega
  have hrlt : r - 1 < s := by omega
  simp [alphaCoeff, hr0, hrlt, htop]

lemma existsUnique_hasHighestBit (s : ℕ) {α : Fin s → ZMod 2} (hα : α ≠ 0) :
    ∃! r : ℕ, HasHighestBit s α r := by
  classical
  let supp : Finset (Fin s) := Finset.univ.filter fun i => α i ≠ 0
  have hne : supp.Nonempty := by
    have ⟨i₀, hi₀⟩ : ∃ i : Fin s, α i ≠ 0 := by
      by_contra h
      exact hα (funext fun i => not_not.mp fun hni => h ⟨i, hni⟩)
    exact ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ i₀, hi₀⟩⟩
  let imax : Fin s := supp.max' hne
  refine ⟨imax.val + 1, ?_, ?_⟩
  · refine ⟨by omega, by omega, ?_, ?_⟩
    · have himem : imax ∈ supp := Finset.max'_mem supp hne
      have hine : α imax ≠ 0 := (Finset.mem_filter.mp himem).2
      have hidx : (⟨imax.val + 1 - 1, by omega⟩ : Fin s) = imax := by ext; simp
      rw [hidx]
      exact (zmod2_ne_zero_iff (α imax)).mp hine
    · intro i hi
      by_contra hni
      have himem : i ∈ supp := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hni⟩
      have hle : i ≤ imax := Finset.le_max' supp i himem
      have hval : i.val ≤ imax.val := hle
      omega
  · intro r' ⟨hr1', hrs', htop', hzero'⟩
    by_contra hne_r
    rcases lt_trichotomy r' (imax.val + 1) with hlt | heq | hgt
    · have himem : imax ∈ supp := Finset.max'_mem supp hne
      have hine : α imax ≠ 0 := (Finset.mem_filter.mp himem).2
      exact hine (hzero' imax (by omega))
    · exact hne_r heq
    · let idx' : Fin s := ⟨r' - 1, by omega⟩
      have hmem' : idx' ∈ supp := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ idx', ?_⟩
        rw [htop']
        decide
      have hle' : idx' ≤ imax := Finset.le_max' supp idx' hmem'
      have hval' : r' - 1 ≤ imax.val := hle'
      omega

/-- Reduced `2^r × 2^r` character block `H̃_α` for `α` with highest bit `r`. -/
def Htilde_alpha (R : Type*) [CommRing R] (s r : ℕ) (α : Fin s → ZMod 2) :
    Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) R :=
  fun w z =>
    (-1 : R) ^ (∑ i : Fin r, alphaCoeff s α (i.val + 1) * borrowVec r w z i).val

lemma borrowBit_mod_pow {i r : ℕ} (hir : i ≤ r) (w z : ℕ) :
    borrowBit i (w % 2 ^ r) (z % 2 ^ r) = borrowBit i w z := by
  have hdvd : 2 ^ i ∣ 2 ^ r := Nat.pow_dvd_pow 2 hir
  simp only [borrowBit, Nat.mod_mod_of_dvd _ hdvd]

/-- `H_α[w', z'] = H̃_α[w' mod 2^r, z' mod 2^r]` when `α` has highest nonzero bit `r`. -/
theorem H_alpha_eq_Htilde_mod (R : Type*) [CommRing R] {s r : ℕ} {α : Fin s → ZMod 2}
    (h : HasHighestBit s α r) (w' z' : Fin (2 ^ s)) :
    H_alpha R s α w' z' =
      Htilde_alpha R s r α
        ⟨w'.val % 2 ^ r, Nat.mod_lt _ (by positivity)⟩
        ⟨z'.val % 2 ^ r, Nat.mod_lt _ (by positivity)⟩ := by
  rcases h with ⟨_, hrs, _, hzero⟩
  simp only [H_alpha, Htilde_alpha, f2Inner, borrowVec]
  congr 2
  have hsplit :
      (∑ i : Fin s, α i * borrowBit (i.val + 1) w'.val z'.val) =
        ∑ i ∈ Finset.univ.filter (fun i : Fin s => i.val < r),
          α i * borrowBit (i.val + 1) w'.val z'.val := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro i _ hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
    rw [hzero i hi, zero_mul]
  rw [hsplit]
  refine Finset.sum_bij (fun (i : Fin s) (hi : i ∈ Finset.univ.filter fun i : Fin s => i.val < r) =>
      (⟨i.val, (Finset.mem_filter.mp hi).2⟩ : Fin r)) ?_ ?_ ?_ ?_
  · intro i _; exact Finset.mem_univ _
  · intro i₁ _ i₂ _ heq
    have hv : i₁.val = i₂.val := by simpa using congr_arg Fin.val heq
    exact Fin.ext hv
  · intro j _
    refine ⟨⟨j.val, by omega⟩, ?_, by ext; rfl⟩
    simp [j.isLt]
  · intro i hi
    have hilt : i.val < r := (Finset.mem_filter.mp hi).2
    rw [alphaCoeff_succ_of_lt i.isLt, borrowBit_mod_pow (by omega)]

/-- Quotient-remainder equivalence `Fin (2^s) ≃ Fin (2^{s-r}) × Fin (2^r)` (`r ≤ s`). -/
def divModPowTwoEquiv (s r : ℕ) (hrs : r ≤ s) :
    Fin (2 ^ s) ≃ Fin (2 ^ (s - r)) × Fin (2 ^ r) where
  toFun w' :=
    (⟨w'.val / 2 ^ r, by
        have hpow : 2 ^ s = 2 ^ (s - r) * 2 ^ r := by rw [← pow_add]; congr 1; omega
        have hw : w'.val < 2 ^ (s - r) * 2 ^ r := hpow ▸ w'.isLt
        exact Nat.div_lt_of_lt_mul (by simpa [mul_comm] using hw)⟩,
     ⟨w'.val % 2 ^ r, Nat.mod_lt _ (by positivity)⟩)
  invFun qw :=
    ⟨qw.1.val * 2 ^ r + qw.2.val, by
      have hpow : 2 ^ s = 2 ^ (s - r) * 2 ^ r := by rw [← pow_add]; congr 1; omega
      rw [hpow]
      have hq : qw.1.val + 1 ≤ 2 ^ (s - r) := qw.1.isLt
      have hr : qw.2.val < 2 ^ r := qw.2.isLt
      calc qw.1.val * 2 ^ r + qw.2.val
          < qw.1.val * 2 ^ r + 2 ^ r := by omega
        _ = (qw.1.val + 1) * 2 ^ r := by ring
        _ ≤ 2 ^ (s - r) * 2 ^ r := Nat.mul_le_mul_right _ hq⟩
  left_inv w' := by
    ext
    dsimp only
    rw [mul_comm, Nat.div_add_mod]
  right_inv qw := by
    rcases qw with ⟨q, w⟩
    have hrpos : 0 < 2 ^ r := by positivity
    ext <;> dsimp only
    · rw [mul_comm, Nat.mul_add_div hrpos, Nat.div_eq_of_lt w.isLt, add_zero]
    · rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt w.isLt]

/-- **Theorem 4.1(a), Factorization**: `H_α` reindexed by quotient and remainder modulo `2^r`
equals `J_{2^{s-r}} ⊗ H̃_α` (Paper 2, eq. (4.3)). -/
theorem H_alpha_reindex_eq_kronecker (R : Type*) [CommRing R] {s r : ℕ} {α : Fin s → ZMod 2}
    (h : HasHighestBit s α r) :
    (H_alpha R s α).reindex (divModPowTwoEquiv s r h.2.1) (divModPowTwoEquiv s r h.2.1) =
      Matrix.kroneckerMap (· * ·) (allOnesMat R (2 ^ (s - r))) (Htilde_alpha R s r α) := by
  ext ⟨qw, w⟩ ⟨qz, z⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    allOnesMat, one_mul]
  rw [H_alpha_eq_Htilde_mod R h]
  congr 1 <;>
    · simp only [divModPowTwoEquiv, Equiv.coe_fn_symm_mk]
      ext
      simp [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt w.isLt, Nat.mod_eq_of_lt z.isLt]

/-- `j`-th binary bit `(n / 2^j : ZMod 2)` of `n : ℕ`. -/
def natBit (n j : ℕ) : ZMod 2 :=
  ((n / 2 ^ j : ℕ) : ZMod 2)

/-- `2^r × 2^r` negacyclic shift matrix `T_neg r` (`T[w, w+1] = 1` for `w < 2^r - 1`,
`T[2^r - 1, 0] = -1`, else `0`; Paper 2, Section 4, eq. (4.4)). -/
def T_neg (R : Type*) [Ring R] (r : ℕ) : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) R :=
  fun w z =>
    if w.val + 1 < 2 ^ r then
      (if z.val = w.val + 1 then 1 else 0)
    else
      (if z.val = 0 then -1 else 0)

/-- Diagonal sign matrix `D_sign[w, w] = (-1)^{∑_{j=1}^{r-1} α_j w_j}` (`D^2 = I`, entries in `{±1}`). -/
def D_sign (R : Type*) [CommRing R] (s r : ℕ) (α : Fin s → ZMod 2) :
    Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) R :=
  Matrix.diagonal fun w =>
    (-1 : R) ^ (∑ j ∈ Finset.Ico 1 r, alphaCoeff s α j * natBit w.val j).val

@[simp]
theorem D_sign_transpose (R : Type*) [CommRing R] (s r : ℕ) (α : Fin s → ZMod 2) :
    (D_sign R s r α)ᵀ = D_sign R s r α := by
  simp [D_sign]

theorem D_sign_mul_self (R : Type*) [CommRing R] (s r : ℕ) (α : Fin s → ZMod 2) :
    D_sign R s r α * D_sign R s r α = 1 := by
  simp only [D_sign, Matrix.diagonal_mul_diagonal]
  have h1 : (fun i : Fin (2 ^ r) =>
      (-1 : R) ^ (∑ j ∈ Finset.Ico 1 r, alphaCoeff s α j * natBit i.val j).val *
      (-1 : R) ^ (∑ j ∈ Finset.Ico 1 r, alphaCoeff s α j * natBit i.val j).val) =
      fun _ => (1 : R) := by
    funext i
    exact neg_one_pow_zmod2_mul_self _
  rw [h1, Matrix.diagonal_one]

theorem D_sign_diag_mem_pm_one (R : Type*) [CommRing R] (s r : ℕ) (α : Fin s → ZMod 2)
    (w : Fin (2 ^ r)) :
    D_sign R s r α w w = 1 ∨ D_sign R s r α w w = -1 := by
  simp only [D_sign, Matrix.diagonal_apply_eq]
  exact neg_one_pow_zmod2_eq_one_or_neg_one _

/-- Factor `I_{2^r} + (-1)^{α_j} T^{2^j}` in `G_α(T)` (Paper 2, eq. (4.4)). -/
def G_alphaFactor (R : Type*) [CommRing R] (s r : ℕ) (α : Fin s → ZMod 2) (j : ℕ) :
    Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) R :=
  1 + ((-1 : R) ^ (alphaCoeff s α j).val) • (T_neg R r) ^ (2 ^ j)

/-- Negacyclic shift polynomial `G_α(T) = ∏_{j=0}^{r-1} (I + (-1)^{α_j} T^{2^j})` (with `α_0 = 0`;
Paper 2, eq. (4.4)). -/
def G_alphaMat (R : Type*) [CommRing R] (s r : ℕ) (α : Fin s → ZMod 2) :
    Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) R :=
  ((List.range r).map (G_alphaFactor R s r α)).prod

/-- Closed-form entries of all powers `(T_neg R r)^k` (`k : ℕ`). -/
theorem T_neg_pow_apply (R : Type*) [CommRing R] (r k : ℕ) (w z : Fin (2 ^ r)) :
    ((T_neg R r) ^ k) w z =
      if (w.val + k) % 2 ^ r = z.val then (-1 : R) ^ ((w.val + k) / 2 ^ r) else 0 := by
  induction k generalizing z with
  | zero =>
    have hwmod : (w.val + 0) % 2 ^ r = w.val := by simp [Nat.mod_eq_of_lt w.isLt]
    have hwdiv : (w.val + 0) / 2 ^ r = 0 := by simp [Nat.div_eq_of_lt w.isLt]
    rw [pow_zero, hwmod, hwdiv, pow_zero, Matrix.one_apply]
    by_cases hwz : w = z
    · subst hwz; simp
    · have hval : w.val ≠ z.val := fun h => hwz (Fin.ext h)
      simp [hwz, hval]
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    let u₀ : Fin (2 ^ r) := ⟨(w.val + k) % 2 ^ r, Nat.mod_lt _ (by positivity)⟩
    rw [Finset.sum_eq_single u₀]
    · rw [ih u₀]
      simp only [u₀, ↓reduceIte, T_neg]
      have hdiv_mod := (Nat.div_add_mod (w.val + k) (2 ^ r)).symm
      have hM : 0 < 2 ^ r := by positivity
      by_cases hstep : (w.val + k) % 2 ^ r + 1 < 2 ^ r
      · simp only [hstep, ↓reduceIte]
        have hmod1 : (w.val + (k + 1)) % 2 ^ r = (w.val + k) % 2 ^ r + 1 := by
          have heq : w.val + (k + 1) = 2 ^ r * ((w.val + k) / 2 ^ r) + ((w.val + k) % 2 ^ r + 1) := by
            omega
          rw [heq, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hstep]
        have hdiv1 : (w.val + (k + 1)) / 2 ^ r = (w.val + k) / 2 ^ r := by
          have heq : w.val + (k + 1) = 2 ^ r * ((w.val + k) / 2 ^ r) + ((w.val + k) % 2 ^ r + 1) := by
            omega
          rw [heq, Nat.mul_add_div hM, Nat.div_eq_of_lt hstep, add_zero]
        rw [hmod1, hdiv1]
        by_cases hz : z.val = (w.val + k) % 2 ^ r + 1
        · rw [hz]; simp
        · have hz' : (w.val + k) % 2 ^ r + 1 ≠ z.val := Ne.symm hz
          simp [hz, hz']
      · simp only [hstep, ↓reduceIte]
        have hrem : (w.val + k) % 2 ^ r < 2 ^ r := Nat.mod_lt _ hM
        have hrem_eq : (w.val + k) % 2 ^ r + 1 = 2 ^ r := by omega
        have heq : w.val + (k + 1) = 2 ^ r * ((w.val + k) / 2 ^ r + 1) := by nlinarith
        have hmod1 : (w.val + (k + 1)) % 2 ^ r = 0 := by
          rw [heq, Nat.mul_mod_right]
        have hdiv1 : (w.val + (k + 1)) / 2 ^ r = (w.val + k) / 2 ^ r + 1 := by
          rw [heq, Nat.mul_div_right _ hM]
        rw [hmod1, hdiv1]
        by_cases hz : z.val = 0
        · rw [hz]; simp [pow_succ]
        · have hz' : 0 ≠ z.val := Ne.symm hz
          simp [hz, hz']
    · intro u _ hu
      rw [ih u]
      have hval : (w.val + k) % 2 ^ r ≠ u.val := fun h => hu (Fin.ext h.symm)
      simp [hval]
    · intro hmem
      exact absurd (Finset.mem_univ u₀) hmem

/-- `(T_neg R r)^{2^r} = -I_{2^r}`. -/
theorem T_neg_pow_two_pow (R : Type*) [CommRing R] (r : ℕ) :
    (T_neg R r) ^ (2 ^ r) = -1 := by
  ext w z
  rw [T_neg_pow_apply]
  have hM : 0 < 2 ^ r := by positivity
  have hmod : (w.val + 2 ^ r) % 2 ^ r = w.val := by
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt w.isLt]
  have hdiv : (w.val + 2 ^ r) / 2 ^ r = 1 := by
    rw [Nat.add_div_right _ hM, Nat.div_eq_of_lt w.isLt, zero_add]
  rw [hmod, hdiv, pow_one, Matrix.neg_apply, Matrix.one_apply]
  by_cases hwz : w = z
  · subst hwz; simp
  · have hval : w.val ≠ z.val := fun h => hwz (Fin.ext h)
    simp [hwz, hval]

private lemma G_alpha_partial_prod_eq_sum (R : Type*) [CommRing R] (s r m : ℕ)
    (α : Fin s → ZMod 2) :
    ((List.range m).map (G_alphaFactor R s r α)).prod =
      ∑ k : Fin (2 ^ m),
        ((-1 : R) ^ (∑ j ∈ Finset.range m, alphaCoeff s α j * natBit k.val j).val) •
          (T_neg R r) ^ k.val := by
  induction m with
  | zero =>
    ext w z
    have huniv : (Finset.univ : Finset (Fin (2 ^ 0))) = {⟨0, by decide⟩} := by decide
    rw [List.range_zero, List.map_nil, List.prod_nil, Matrix.sum_apply, huniv,
      Finset.sum_singleton]
    simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton, ih, G_alphaFactor, mul_add, Finset.sum_mul, Finset.sum_mul]
    have hsplit :
        (∑ k : Fin (2 ^ (m + 1)),
            ((-1 : R) ^ (∑ j ∈ Finset.range (m + 1), alphaCoeff s α j * natBit k.val j).val) •
              (T_neg R r) ^ k.val) =
          (∑ k : Fin (2 ^ m),
            ((-1 : R) ^ (∑ j ∈ Finset.range (m + 1), alphaCoeff s α j * natBit k.val j).val) •
              (T_neg R r) ^ k.val) +
          (∑ k : Fin (2 ^ m),
            ((-1 : R) ^ (∑ j ∈ Finset.range (m + 1),
                alphaCoeff s α j * natBit (k.val + 2 ^ m) j).val) •
              (T_neg R r) ^ (k.val + 2 ^ m)) := by
      let e : Fin (2 ^ m) ⊕ Fin (2 ^ m) ≃ Fin (2 ^ (m + 1)) :=
        { toFun := Sum.elim
            (fun k => ⟨k.val, by
              have hk : k.val < 2 ^ m := k.isLt
              calc k.val < 2 ^ m := hk
                _ ≤ 2 ^ m * 2 := by omega
                _ = 2 ^ (m + 1) := by rw [pow_succ]⟩)
            (fun k => ⟨k.val + 2 ^ m, by
              have hk : k.val < 2 ^ m := k.isLt
              calc k.val + 2 ^ m < 2 ^ m * 2 := by omega
                _ = 2 ^ (m + 1) := by rw [pow_succ]⟩)
          invFun := fun x =>
            if hx : x.val < 2 ^ m then Sum.inl ⟨x.val, hx⟩
            else Sum.inr ⟨x.val - 2 ^ m, by
              have hx_lt : x.val < 2 ^ m * 2 := by simpa only [pow_succ] using x.isLt
              omega⟩
          left_inv := by
            rintro (k | k) <;> dsimp only
            · simp [k.isLt]
            · have hnot : ¬(k.val + 2 ^ m < 2 ^ m) := by omega
              simp [hnot]
          right_inv := by
            intro x
            by_cases hx : x.val < 2 ^ m
            · simp [hx]
            · simp only [hx, ↓reduceDIte, Sum.elim_inr]
              ext
              change x.val - 2 ^ m + 2 ^ m = x.val
              omega }
      rw [← Equiv.sum_comp e, Fintype.sum_sum_type]
      rfl
    rw [hsplit]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_one, Finset.sum_range_succ]
      have hbit_top : natBit k.val m = 0 := by
        simp [natBit, Nat.div_eq_of_lt k.isLt]
      rw [hbit_top, mul_zero, add_zero]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, ← pow_add (T_neg R r)]
      congr 1
      have hlow : ∀ j ∈ Finset.range m, natBit (k.val + 2 ^ m) j = natBit k.val j := by
        intro j hj
        have hjlt : j < m := Finset.mem_range.mp hj
        have hdvd : 2 ^ (j + 1) ∣ 2 ^ m := Nat.pow_dvd_pow 2 hjlt
        obtain ⟨q, hq⟩ := hdvd
        have hpos : 0 < 2 ^ j := by positivity
        set kv := k.val
        have heq : kv + 2 ^ m = 2 ^ j * (2 * q) + kv := by
          rw [hq, pow_succ]; ring
        rw [natBit, natBit, heq, Nat.mul_add_div hpos, Nat.cast_add, Nat.cast_mul]
        simp
      have hsum_eq :
          (∑ j ∈ Finset.range m, alphaCoeff s α j * natBit (k.val + 2 ^ m) j) =
            ∑ j ∈ Finset.range m, alphaCoeff s α j * natBit k.val j := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [hlow j hj]
      have htop : natBit (k.val + 2 ^ m) m = 1 := by
        have hpos : 0 < 2 ^ m := by positivity
        rw [natBit, Nat.add_div_right _ hpos, Nat.div_eq_of_lt k.isLt, zero_add, Nat.cast_one]
      rw [Finset.sum_range_succ, hsum_eq, htop, mul_one, neg_one_pow_zmod2_add, mul_comm]

private lemma binary_sub_carry_bit_aux (M : ℕ) (hM : 0 < M) (w k z : ℕ)
    (hmod2 : (w + k) % (2 * M) = z % (2 * M)) :
    ((k / M : ℕ) : ZMod 2) =
      ((w / M : ℕ) : ZMod 2) + ((z / M : ℕ) : ZMod 2) +
        (if z % M < w % M then (1 : ZMod 2) else 0) := by
  have hdvdM : M ∣ 2 * M := ⟨2, by ring⟩
  have hmodM : (w + k) % M = z % M := by
    have h1 := congr_arg (· % M) hmod2
    simpa only [Nat.mod_mod_of_dvd _ hdvdM] using h1
  have hrw : w % M < M := Nat.mod_lt w hM
  have hrk : k % M < M := Nat.mod_lt k hM
  have hrz : z % M < M := Nat.mod_lt z hM
  have hlow_mod : (w % M + k % M) % M = z % M := by
    rw [← Nat.add_mod, hmodM]
  have hparity : (w / M + k / M + (if z % M < w % M then 1 else 0)) % 2 = (z / M) % 2 := by
    have hlow_exact :
        w % M + k % M = z % M + M * (if z % M < w % M then 1 else 0) := by
      by_cases hlt : z % M < w % M
      · simp only [hlt, ↓reduceIte, mul_one]
        have hge : M ≤ w % M + k % M := by
          by_contra hltM
          have hms : (w % M + k % M) % M = w % M + k % M := Nat.mod_eq_of_lt (by omega)
          omega
        have hsub : (w % M + k % M) % M = w % M + k % M - M := by
          rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
        omega
      · simp only [hlt, ↓reduceIte, mul_zero, add_zero]
        have hltM : w % M + k % M < M := by
          by_contra hgeM
          have hsub : (w % M + k % M) % M = w % M + k % M - M := by
            rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
          omega
        have hms : (w % M + k % M) % M = w % M + k % M := Nat.mod_eq_of_lt hltM
        omega
    let c : ℕ := if z % M < w % M then 1 else 0
    have hw_eq : w = M * (w / M) + w % M := (Nat.div_add_mod w M).symm
    have hk_eq : k = M * (k / M) + k % M := (Nat.div_add_mod k M).symm
    have hz_eq : z = M * (z / M) + z % M := (Nat.div_add_mod z M).symm
    have hsum_eq : w + k = M * (w / M + k / M + c) + z % M := by
      change w % M + k % M = z % M + M * c at hlow_exact
      linarith
    let S := w / M + k / M + c
    let Q := z / M
    have hS_decomp : M * S + z % M = (2 * M) * (S / 2) + (M * (S % 2) + z % M) := by
      have hd := (Nat.div_add_mod S 2).symm
      nlinarith
    have hQ_decomp : M * Q + z % M = (2 * M) * (Q / 2) + (M * (Q % 2) + z % M) := by
      have hd := (Nat.div_add_mod Q 2).symm
      nlinarith
    have hb1 : S % 2 < 2 := Nat.mod_lt S (by decide)
    have hb2 : Q % 2 < 2 := Nat.mod_lt Q (by decide)
    have hrem1 : (w + k) % (2 * M) = M * (S % 2) + z % M := by
      rw [hsum_eq, hS_decomp, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt (by nlinarith)]
    have hrem2 : z % (2 * M) = M * (Q % 2) + z % M := by
      conv_lhs => rw [hz_eq]
      rw [hQ_decomp, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt (by nlinarith)]
    have heq_rem : M * (S % 2) + z % M = M * (Q % 2) + z % M :=
      hrem1.symm.trans (hmod2.trans hrem2)
    exact Nat.eq_of_mul_eq_mul_left hM (Nat.add_right_cancel heq_rem)
  have hcast :
      ((w / M + k / M + (if z % M < w % M then 1 else 0) : ℕ) : ZMod 2) =
        ((z / M : ℕ) : ZMod 2) :=
    (ZMod.natCast_eq_natCast_iff' _ _ 2).mpr hparity
  push_cast at hcast
  set bw : ZMod 2 := ((w / M : ℕ) : ZMod 2)
  set bk : ZMod 2 := ((k / M : ℕ) : ZMod 2)
  set bz : ZMod 2 := ((z / M : ℕ) : ZMod 2)
  set bc : ZMod 2 := if z % M < w % M then 1 else 0
  have hcast' : bw + bk + bc = bz := by
    have hbc : (((if z % M < w % M then 1 else 0 : ℕ) : ZMod 2)) = bc := by
      dsimp [bc]; split_ifs <;> simp
    simpa [bw, bk, bz, hbc] using hcast
  calc bk = 0 + bk + 0 := by simp
    _ = (bw + bw) + bk + (bc + bc) := by rw [zmod2_add_self bw, zmod2_add_self bc]
    _ = bw + (bw + bk + bc) + bc := by ring
    _ = bw + bz + bc := by rw [hcast']

private lemma binary_sub_carry_bit {r j w k z : ℕ} (hjr : j < r)
    (hmod : (w + k) % 2 ^ r = z % 2 ^ r) :
    natBit k j = natBit w j + natBit z j + borrowBit j w z := by
  have hdvd : 2 ^ (j + 1) ∣ 2 ^ r := Nat.pow_dvd_pow 2 hjr
  have hmod2 : (w + k) % (2 * 2 ^ j) = z % (2 * 2 ^ j) := by
    have h1 := congr_arg (· % 2 ^ (j + 1)) hmod
    rw [Nat.mod_mod_of_dvd _ hdvd, Nat.mod_mod_of_dvd _ hdvd] at h1
    have h2 : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
    rwa [h2] at h1
  simpa only [natBit, borrowBit] using binary_sub_carry_bit_aux (2 ^ j) (by positivity) w k z hmod2

/-- **Theorem 4.1(a), Part 2 (Exact Negacyclic Conjugation over `ℤ` and any `CommRing R`)**:
For `α` with highest nonzero bit `r`,
`D_sign * Htilde_alpha * D_sign = ∏_{j=0}^{r-1} (I + (-1)^{α_j} T_neg^{2^j})`
(with `α_0 = 0`; Paper 2, eq. (4.4)). -/
theorem D_sign_conj_Htilde_eq_G_alpha (R : Type*) [CommRing R] {s r : ℕ} {α : Fin s → ZMod 2}
    (h : HasHighestBit s α r) :
    D_sign R s r α * Htilde_alpha R s r α * D_sign R s r α = G_alphaMat R s r α := by
  have htop := alphaCoeff_top_eq_one h
  rcases h with ⟨hr1, hrs, _, _⟩
  rw [G_alphaMat, G_alpha_partial_prod_eq_sum]
  ext w z
  simp only [D_sign, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, T_neg_pow_apply]
  let k₀ : Fin (2 ^ r) := ⟨(z.val + 2 ^ r - w.val) % 2 ^ r, Nat.mod_lt _ (by positivity)⟩
  rw [Finset.sum_eq_single k₀]
  · have hk₀_mod : (w.val + k₀.val) % 2 ^ r = z.val := by
      have hw : w.val ≤ 2 ^ r := w.isLt.le
      have h1 : (w.val + ((z.val + 2 ^ r - w.val) % 2 ^ r)) % 2 ^ r =
          (w.val + (z.val + 2 ^ r - w.val)) % 2 ^ r := by rw [Nat.add_mod_mod]
      have h2 : w.val + (z.val + 2 ^ r - w.val) = z.val + 2 ^ r := by omega
      rw [h1, h2, Nat.add_mod_right, Nat.mod_eq_of_lt z.isLt]
    simp only [hk₀_mod, ↓reduceIte]
    have hk₀_div : (-1 : R) ^ ((w.val + k₀.val) / 2 ^ r) =
        (-1 : R) ^ (borrowBit r w.val z.val).val := by
      by_cases hlt : z.val < w.val
      · have hk_val : k₀.val = z.val + 2 ^ r - w.val := by
          dsimp [k₀]
          exact Nat.mod_eq_of_lt (by have := z.isLt; omega)
        have hsum : w.val + k₀.val = z.val + 2 ^ r := by omega
        have hdiv : (w.val + k₀.val) / 2 ^ r = 1 := by
          rw [hsum, Nat.add_div_right _ (by positivity), Nat.div_eq_of_lt z.isLt, zero_add]
        have hbb : borrowBit r w.val z.val = 1 := by
          simp [borrowBit, Nat.mod_eq_of_lt w.isLt, Nat.mod_eq_of_lt z.isLt, hlt]
        rw [hdiv, hbb]
        rfl
      · have hk_val : k₀.val = z.val - w.val := by
          dsimp [k₀]
          have heq : z.val + 2 ^ r - w.val = (z.val - w.val) + 2 ^ r := by omega
          rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := z.isLt; omega)]
        have hsum : w.val + k₀.val = z.val := by omega
        have hdiv : (w.val + k₀.val) / 2 ^ r = 0 := by
          rw [hsum, Nat.div_eq_of_lt z.isLt]
        have hbb : borrowBit r w.val z.val = 0 := by
          simp [borrowBit, Nat.mod_eq_of_lt w.isLt, Nat.mod_eq_of_lt z.isLt, hlt]
        rw [hdiv, hbb]
        rfl
    rw [hk₀_div, ← neg_one_pow_zmod2_add]
    simp only [Htilde_alpha, ← neg_one_pow_zmod2_add]
    congr 2
    have hrange_ico :
        (∑ j ∈ Finset.range r, alphaCoeff s α j * natBit k₀.val j) =
          ∑ j ∈ Finset.Ico 1 r, alphaCoeff s α j * natBit k₀.val j := by
      have hunion : Finset.range r = insert 0 (Finset.Ico 1 r) := by
        ext j; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
      rw [hunion, Finset.sum_insert (by simp), alphaCoeff_zero, zero_mul, zero_add]
    rw [hrange_ico]
    have hfin_r :
        (∑ i : Fin r, alphaCoeff s α (i.val + 1) * borrowVec r w z i) =
          (∑ j ∈ Finset.Ico 1 r, alphaCoeff s α j * borrowBit j w.val z.val) +
            borrowBit r w.val z.val := by
      have hbij :
          (∑ i : Fin r, alphaCoeff s α (i.val + 1) * borrowVec r w z i) =
            ∑ j ∈ Finset.Icc 1 r, alphaCoeff s α j * borrowBit j w.val z.val := by
        refine Finset.sum_bij (fun (i : Fin r) _ => i.val + 1) ?_ ?_ ?_ ?_
        · intro i _; simp only [Finset.mem_Icc]; have := i.isLt; omega
        · intro i₁ _ i₂ _ heq; ext; omega
        · intro j hj
          simp only [Finset.mem_Icc] at hj
          exact ⟨⟨j - 1, by omega⟩, Finset.mem_univ _, by dsimp only; omega⟩
        · intro i _; rfl
      rw [hbij]
      have hicc : Finset.Icc 1 r = insert r (Finset.Ico 1 r) := by
        ext j; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]; omega
      rw [hicc, Finset.sum_insert (by simp), htop, one_mul, add_comm]
    rw [hfin_r]
    have hk_sum :
        (∑ j ∈ Finset.Ico 1 r, alphaCoeff s α j * natBit k₀.val j) =
          (∑ j ∈ Finset.Ico 1 r, alphaCoeff s α j * natBit w.val j) +
            (∑ j ∈ Finset.Ico 1 r, alphaCoeff s α j * natBit z.val j) +
            (∑ j ∈ Finset.Ico 1 r, alphaCoeff s α j * borrowBit j w.val z.val) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      simp only [Finset.mem_Ico] at hj
      have hmod' : (w.val + k₀.val) % 2 ^ r = z.val % 2 ^ r := by
        rw [hk₀_mod, Nat.mod_eq_of_lt z.isLt]
      rw [binary_sub_carry_bit hj.2 hmod']
      ring
    rw [hk_sum]
    ring
  · intro k _ hk
    have hneq : (w.val + k.val) % 2 ^ r ≠ z.val := by
      intro heq
      apply hk
      apply Fin.ext
      dsimp only [k₀]
      have hw : w.val < 2 ^ r := w.isLt
      have hk_lt : k.val < 2 ^ r := k.isLt
      rw [← heq]
      by_cases hwrap : w.val + k.val < 2 ^ r
      · rw [Nat.mod_eq_of_lt hwrap]
        have h2 : w.val + k.val + 2 ^ r - w.val = k.val + 2 ^ r := by omega
        rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hk_lt]
      · have hmod_sub : (w.val + k.val) % 2 ^ r = w.val + k.val - 2 ^ r := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [hmod_sub]
        have h2 : w.val + k.val - 2 ^ r + 2 ^ r - w.val = k.val := by omega
        rw [h2, Nat.mod_eq_of_lt hk_lt]
    simp [hneq]
  · intro hmem
    exact absurd (Finset.mem_univ k₀) hmem

/-- Specialization of `D_sign_conj_Htilde_eq_G_alpha` over `ℤ`. -/
theorem D_sign_conj_Htilde_eq_G_alpha_int {s r : ℕ} {α : Fin s → ZMod 2}
    (h : HasHighestBit s α r) :
    D_sign ℤ s r α * Htilde_alpha ℤ s r α * D_sign ℤ s r α = G_alphaMat ℤ s r α :=
  D_sign_conj_Htilde_eq_G_alpha ℤ h

/-! ### 3. Negacyclic DFT Diagonalization, Singular Values, and Exact Ranks (Theorem 4.1(b)–(c)) -/

/-- `2^r` negacyclic roots `ζ_ℓ = exp((2ℓ + 1) π i / 2^r)` (`0 ≤ ℓ < 2^r`). -/
noncomputable def zetaNeg (r : ℕ) (ℓ : Fin (2 ^ r)) : ℂ :=
  Complex.exp (((((2 * (ℓ.val : ℝ) + 1) * Real.pi) / (2 : ℝ) ^ r : ℝ) : ℂ) * Complex.I)

theorem zetaNeg_eq_div (r : ℕ) (ℓ : Fin (2 ^ r)) :
    zetaNeg r ℓ =
      Complex.exp (((2 * (ℓ.val : ℂ) + 1) * (Real.pi : ℂ) * Complex.I) / (2 : ℂ) ^ r) := by
  simp only [zetaNeg]
  congr 1
  push_cast
  ring

@[simp]
theorem norm_zetaNeg (r : ℕ) (ℓ : Fin (2 ^ r)) : ‖zetaNeg r ℓ‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem zetaNeg_pow_two_pow (r : ℕ) (ℓ : Fin (2 ^ r)) :
    (zetaNeg r ℓ) ^ (2 ^ r) = -1 := by
  rw [zetaNeg_eq_div, ← Complex.exp_nat_mul]
  have h2 : (2 : ℂ) ^ r ≠ 0 := pow_ne_zero r (by norm_num)
  have hexp :
      ((2 ^ r : ℕ) : ℂ) * (((2 * (ℓ.val : ℂ) + 1) * (Real.pi : ℂ) * Complex.I) / (2 : ℂ) ^ r) =
        ((ℓ.val : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) + (Real.pi : ℂ) * Complex.I := by
    push_cast
    field_simp [h2]
  rw [hexp, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I, one_mul]

lemma star_zetaNeg_mul_zetaNeg_eq (r : ℕ) (ℓ₁ ℓ₂ : Fin (2 ^ r)) :
    star (zetaNeg r ℓ₁) * zetaNeg r ℓ₂ =
      Complex.exp (((((ℓ₂.val : ℤ) - (ℓ₁.val : ℤ) : ℂ) / (2 : ℂ) ^ r) *
        (2 * (Real.pi : ℂ) * Complex.I))) := by
  have hstar : star (zetaNeg r ℓ₁) =
      Complex.exp (-(((((2 * (ℓ₁.val : ℝ) + 1) * Real.pi) / (2 : ℝ) ^ r : ℝ) : ℂ) * Complex.I)) := by
    rw [zetaNeg, Complex.star_def, ← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  rw [hstar, zetaNeg, ← Complex.exp_add]
  congr 1
  have h2 : (2 : ℂ) ^ r ≠ 0 := pow_ne_zero r (by norm_num)
  push_cast
  field_simp [h2]
  ring

@[simp]
lemma star_zetaNeg_mul_self (r : ℕ) (ℓ : Fin (2 ^ r)) :
    star (zetaNeg r ℓ) * zetaNeg r ℓ = 1 := by
  rw [star_zetaNeg_mul_zetaNeg_eq]
  simp

lemma star_zetaNeg_mul_ne_one_of_ne (r : ℕ) {ℓ₁ ℓ₂ : Fin (2 ^ r)} (hne : ℓ₁ ≠ ℓ₂) :
    star (zetaNeg r ℓ₁) * zetaNeg r ℓ₂ ≠ 1 := by
  rw [star_zetaNeg_mul_zetaNeg_eq, Ne, Complex.exp_eq_one_iff]
  rintro ⟨n, hn⟩
  have h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have hdiv := mul_right_cancel₀ h2pi hn
  have h2pow : (2 : ℂ) ^ r ≠ 0 := pow_ne_zero r (by norm_num)
  have hintC : ((ℓ₂.val : ℤ) - (ℓ₁.val : ℤ) : ℂ) = ((n * (2 ^ r : ℤ)) : ℂ) := by
    push_cast
    rw [div_eq_iff h2pow] at hdiv
    simpa [mul_comm] using hdiv
  have hint : (ℓ₂.val : ℤ) - (ℓ₁.val : ℤ) = n * (2 ^ r : ℤ) := by exact_mod_cast hintC
  have h1 : (ℓ₁.val : ℤ) < (2 ^ r : ℤ) := by exact_mod_cast ℓ₁.isLt
  have h2 : (ℓ₂.val : ℤ) < (2 ^ r : ℤ) := by exact_mod_cast ℓ₂.isLt
  have h10 : (0 : ℤ) ≤ (ℓ₁.val : ℤ) := Int.natCast_nonneg _
  have h20 : (0 : ℤ) ≤ (ℓ₂.val : ℤ) := Int.natCast_nonneg _
  have hpos : (0 : ℤ) < (2 : ℤ) ^ r := by positivity
  have hn_gt : -1 < n := by nlinarith
  have hn_lt : n < 1 := by nlinarith
  have hn0 : n = 0 := by omega
  rw [hn0, zero_mul] at hint
  have hval : ℓ₁.val = ℓ₂.val := by omega
  exact hne (Fin.ext hval)

/-- Unitary `2^r × 2^r` negacyclic DFT matrix `U_neg[w, ℓ] = 2^{-r/2} ζ_ℓ^w`. -/
noncomputable def U_neg (r : ℕ) : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℂ :=
  fun w ℓ => (((Real.sqrt 2) ^ r : ℝ)⁻¹ : ℂ) * (zetaNeg r ℓ) ^ w.val

/-- `U_neg r` is unitary: `Uᴴ * U = I`. -/
theorem U_neg_conjTranspose_mul_self (r : ℕ) :
    (U_neg r)ᴴ * U_neg r = 1 := by
  ext ℓ₁ ℓ₂
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, U_neg, Matrix.one_apply,
    star_mul', star_pow, Complex.star_def, map_inv₀, Complex.conj_ofReal]
  have hpull :
      ∀ w : Fin (2 ^ r),
        (((Real.sqrt 2 ^ r : ℝ) : ℂ)⁻¹ * (starRingEnd ℂ) (zetaNeg r ℓ₁) ^ w.val) *
            ((((Real.sqrt 2) ^ r : ℝ)⁻¹ : ℂ) * zetaNeg r ℓ₂ ^ w.val) =
          (((2 : ℂ) ^ r)⁻¹) * (star (zetaNeg r ℓ₁) * zetaNeg r ℓ₂) ^ w.val := by
    intro w
    have hpow : ((Real.sqrt 2 ^ r : ℝ) : ℂ) * ((Real.sqrt 2 ^ r : ℝ) : ℂ) = (2 : ℂ) ^ r := by
      have hR : (Real.sqrt 2) ^ r * (Real.sqrt 2) ^ r = (2 : ℝ) ^ r := by
        rw [← mul_pow, Real.mul_self_sqrt (by positivity)]
      exact_mod_cast hR
    have hinv : (((Real.sqrt 2 ^ r : ℝ) : ℂ)⁻¹) * ((((Real.sqrt 2) ^ r : ℝ)⁻¹ : ℂ)) =
        ((2 : ℂ) ^ r)⁻¹ := by
      push_cast [← hpow]
      ring
    calc (((Real.sqrt 2 ^ r : ℝ) : ℂ)⁻¹ * (starRingEnd ℂ) (zetaNeg r ℓ₁) ^ w.val) *
            ((((Real.sqrt 2) ^ r : ℝ)⁻¹ : ℂ) * zetaNeg r ℓ₂ ^ w.val)
        = ((((Real.sqrt 2 ^ r : ℝ) : ℂ)⁻¹) * ((((Real.sqrt 2) ^ r : ℝ)⁻¹ : ℂ))) *
            (star (zetaNeg r ℓ₁) ^ w.val * zetaNeg r ℓ₂ ^ w.val) := by
            simp only [Complex.star_def]; ring
      _ = ((2 : ℂ) ^ r)⁻¹ * (star (zetaNeg r ℓ₁) * zetaNeg r ℓ₂) ^ w.val := by
            rw [hinv, mul_pow]
  simp_rw [hpull, ← Finset.mul_sum]
  by_cases hℓ : ℓ₁ = ℓ₂
  · subst hℓ
    simp only [star_zetaNeg_mul_self, one_pow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, ↓reduceIte, Nat.cast_pow, Nat.cast_ofNat]
    exact inv_mul_cancel₀ (pow_ne_zero r (by norm_num))
  · simp only [hℓ, ↓reduceIte]
    set q := star (zetaNeg r ℓ₁) * zetaNeg r ℓ₂
    have hsum_range : (∑ w : Fin (2 ^ r), q ^ w.val) = ∑ k ∈ Finset.range (2 ^ r), q ^ k :=
      Fin.sum_univ_eq_sum_range (fun k => q ^ k) (2 ^ r)
    rw [hsum_range]
    have hq_pow : q ^ (2 ^ r) = 1 := by
      dsimp only [q]
      rw [mul_pow, ← star_pow, zetaNeg_pow_two_pow, zetaNeg_pow_two_pow]
      simp
    have hq_ne : q - 1 ≠ 0 := sub_ne_zero.mpr (star_zetaNeg_mul_ne_one_of_ne r hℓ)
    have hgeom : (∑ k ∈ Finset.range (2 ^ r), q ^ k) * (q - 1) = 0 := by
      rw [geom_sum_mul, hq_pow, sub_self]
    have hsum0 : (∑ k ∈ Finset.range (2 ^ r), q ^ k) = 0 :=
      (mul_eq_zero.mp hgeom).resolve_right hq_ne
    rw [hsum0, mul_zero]

/-- `U_neg r` is unitary: `U * Uᴴ = I`. -/
theorem U_neg_mul_conjTranspose_self (r : ℕ) :
    U_neg r * (U_neg r)ᴴ = 1 :=
  mul_eq_one_comm.mp (U_neg_conjTranspose_mul_self r)

theorem T_neg_mul_U_neg (r : ℕ) :
    T_neg ℂ r * U_neg r = U_neg r * Matrix.diagonal (zetaNeg r) := by
  ext w ℓ
  rw [Matrix.mul_diagonal]
  simp only [Matrix.mul_apply, T_neg, U_neg]
  by_cases hstep : w.val + 1 < 2 ^ r
  · simp only [hstep, ↓reduceIte]
    let z₀ : Fin (2 ^ r) := ⟨w.val + 1, hstep⟩
    rw [Finset.sum_eq_single z₀]
    · simp only [z₀, ↓reduceIte, one_mul, pow_succ]
      ring
    · intro z _ hz
      have hzv : z.val ≠ w.val + 1 := fun hv => hz (Fin.ext hv)
      simp [hzv]
    · intro hmem
      exact absurd (Finset.mem_univ z₀) hmem
  · simp only [hstep, ↓reduceIte]
    let z₀ : Fin (2 ^ r) := ⟨0, by positivity⟩
    rw [Finset.sum_eq_single z₀]
    · have hw_top : w.val + 1 = 2 ^ r := by have := w.isLt; omega
      have hpow_w : (zetaNeg r ℓ) ^ w.val * zetaNeg r ℓ = -1 := by
        rw [← pow_succ, hw_top, zetaNeg_pow_two_pow]
      simp only [z₀, ↓reduceIte, pow_zero, mul_one, neg_mul, one_mul]
      calc -(((Real.sqrt 2 ^ r : ℝ)⁻¹ : ℂ))
          = (((Real.sqrt 2 ^ r : ℝ)⁻¹ : ℂ)) * (-1) := by ring
        _ = (((Real.sqrt 2 ^ r : ℝ)⁻¹ : ℂ)) * ((zetaNeg r ℓ) ^ w.val * zetaNeg r ℓ) := by
            rw [hpow_w]
        _ = (((Real.sqrt 2 ^ r : ℝ)⁻¹ : ℂ) * (zetaNeg r ℓ) ^ w.val) * zetaNeg r ℓ := by ring
    · intro z _ hz
      have hzv : z.val ≠ 0 := fun hv => hz (Fin.ext hv)
      simp [hzv]
    · intro hmem
      exact absurd (Finset.mem_univ z₀) hmem

/-- **Theorem 4.1(c), Negacyclic Shift Diagonalization**:
`U_negᴴ * T_neg * U_neg = diag(ζ_0, ..., ζ_{2^r - 1})`. -/
theorem U_neg_conj_T_neg (r : ℕ) :
    (U_neg r)ᴴ * T_neg ℂ r * U_neg r = Matrix.diagonal (zetaNeg r) := by
  rw [Matrix.mul_assoc, T_neg_mul_U_neg, ← Matrix.mul_assoc,
    U_neg_conjTranspose_mul_self, Matrix.one_mul]

private lemma unitary_conj_mul {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n ℂ} (hU2 : U * Uᴴ = 1) (A B : Matrix n n ℂ) :
    Uᴴ * (A * B) * U = (Uᴴ * A * U) * (Uᴴ * B * U) := by
  calc Uᴴ * (A * B) * U
      = Uᴴ * A * (U * Uᴴ) * B * U := by simp [Matrix.mul_assoc, hU2]
    _ = (Uᴴ * A * U) * (Uᴴ * B * U) := by simp [Matrix.mul_assoc]

private lemma unitary_conj_pow {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n ℂ} (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1)
    (A : Matrix n n ℂ) (k : ℕ) :
    Uᴴ * (A ^ k) * U = (Uᴴ * A * U) ^ k := by
  induction k with
  | zero => simp [hU1]
  | succ k ih =>
    rw [pow_succ, unitary_conj_mul hU2, ih, pow_succ]

private lemma unitary_conj_list_prod {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n ℂ} (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1)
    (L : List (Matrix n n ℂ)) :
    Uᴴ * L.prod * U = (L.map fun M => Uᴴ * M * U).prod := by
  induction L with
  | nil => simp [hU1]
  | cons M L ih =>
    rw [List.prod_cons, unitary_conj_mul hU2, ih, List.map_cons, List.prod_cons]

private lemma list_prod_diagonal {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    {ι : Type*} (L : List ι) (f : ι → n → R) :
    (L.map fun j => Matrix.diagonal (f j)).prod =
      Matrix.diagonal (fun i => (L.map fun j => f j i).prod) := by
  induction L with
  | nil => simp [Matrix.diagonal_one]
  | cons j L ih =>
    simp [List.map_cons, List.prod_cons, ih, Matrix.diagonal_mul_diagonal]

/-- Eigenvalues `λ_ℓ = ∏_{j=0}^{r-1} (1 + (-1)^{α_j} ζ_ℓ^{2^j})` of `G_α(T)`. -/
noncomputable def lambdaAlpha (s r : ℕ) (α : Fin s → ZMod 2) (ℓ : Fin (2 ^ r)) : ℂ :=
  ∏ j ∈ Finset.range r, (1 + ((-1 : ℂ) ^ (alphaCoeff s α j).val) * (zetaNeg r ℓ) ^ (2 ^ j))

/-- **Theorem 4.1(c), Unitary Diagonalization of `G_α(T)`**:
`U_negᴴ * G_α(T) * U_neg = diag(λ_0, ..., λ_{2^r - 1})`. -/
theorem U_neg_conj_G_alpha (s r : ℕ) (α : Fin s → ZMod 2) :
    (U_neg r)ᴴ * G_alphaMat ℂ s r α * U_neg r = Matrix.diagonal (lambdaAlpha s r α) := by
  have hU1 := U_neg_conjTranspose_mul_self r
  have hU2 := U_neg_mul_conjTranspose_self r
  rw [G_alphaMat, unitary_conj_list_prod hU1 hU2, List.map_map, Function.comp_def]
  have hfac :
      (fun j : ℕ => (U_neg r)ᴴ * G_alphaFactor ℂ s r α j * U_neg r) =
        fun j : ℕ =>
          Matrix.diagonal (fun ℓ => 1 + ((-1 : ℂ) ^ (alphaCoeff s α j).val) * (zetaNeg r ℓ) ^ (2 ^ j)) := by
    funext j
    simp only [G_alphaFactor, mul_add, add_mul, Matrix.mul_one, hU1, Matrix.mul_smul,
      Matrix.smul_mul, unitary_conj_pow hU1 hU2, U_neg_conj_T_neg, Matrix.diagonal_pow]
    ext ℓ₁ ℓ₂
    by_cases hℓ : ℓ₁ = ℓ₂
    · subst hℓ; simp
    · simp [hℓ]
  rw [hfac, list_prod_diagonal]
  congr 1

/-- Every factor `1 + (-1)^{α_j} ζ_ℓ^{2^j}` (`j < r`) is strictly nonzero because `ζ_ℓ^{2^j}` is a
primitive `2^{r+1-j}`-th root of unity of order `≥ 4`, hence `(ζ_ℓ^{2^j})^2 ≠ 1`. -/
theorem factor_lambdaAlpha_ne_zero {s r j : ℕ} (hjr : j < r) (α : Fin s → ZMod 2)
    (ℓ : Fin (2 ^ r)) :
    1 + ((-1 : ℂ) ^ (alphaCoeff s α j).val) * (zetaNeg r ℓ) ^ (2 ^ j) ≠ 0 := by
  intro hzero
  set sgn : ℂ := (-1 : ℂ) ^ (alphaCoeff s α j).val
  set z : ℂ := (zetaNeg r ℓ) ^ (2 ^ j)
  have hmul : sgn * z = -1 := by
    change 1 + sgn * z = 0 at hzero
    linear_combination hzero
  have hsgn_sq : sgn * sgn = 1 := neg_one_pow_zmod2_mul_self (alphaCoeff s α j)
  have hz_sq : z ^ 2 = 1 := by
    calc z ^ 2 = 1 * (z * z) := by ring
      _ = (sgn * sgn) * (z * z) := by rw [hsgn_sq]
      _ = (sgn * z) * (sgn * z) := by ring
      _ = (-1) * (-1) := by rw [hmul]
      _ = 1 := by ring
  have hexp_eq : 2 ^ j * (2 * 2 ^ (r - 1 - j)) = 2 ^ r := by
    calc 2 ^ j * (2 * 2 ^ (r - 1 - j))
        = (2 ^ j * 2) * 2 ^ (r - 1 - j) := by ring
      _ = 2 ^ (j + 1) * 2 ^ (r - 1 - j) := by rw [pow_succ]
      _ = 2 ^ (j + 1 + (r - 1 - j)) := by rw [← pow_add]
      _ = 2 ^ r := by congr 1; omega
  have hpow1 : (z ^ 2) ^ (2 ^ (r - 1 - j)) = 1 := by rw [hz_sq, one_pow]
  have hpow_neg1 : (z ^ 2) ^ (2 ^ (r - 1 - j)) = -1 := by
    dsimp only [z]
    rw [← pow_mul, ← pow_mul, hexp_eq, zetaNeg_pow_two_pow]
  have h1_eq_neg1 : (1 : ℂ) = -1 := hpow1.symm.trans hpow_neg1
  norm_num at h1_eq_neg1

/-- **Theorem 4.1(c), Nonvanishing of All Eigenvalues `λ_ℓ`**: `λ_ℓ ≠ 0` for all `ℓ < 2^r`. -/
theorem lambdaAlpha_ne_zero (s r : ℕ) (α : Fin s → ZMod 2) (ℓ : Fin (2 ^ r)) :
    lambdaAlpha s r α ℓ ≠ 0 := by
  rw [lambdaAlpha]
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro j hj
  exact factor_lambdaAlpha_ne_zero (Finset.mem_range.mp hj) α ℓ

/-- Closed-form nonzero singular values `σ_ℓ(H_α) = 2^{s - r} ‖λ_ℓ‖ > 0` (`0 ≤ ℓ < 2^r`;
Paper 2, Theorem 4.1(c)). -/
noncomputable def sigmaHAlpha (s r : ℕ) (α : Fin s → ZMod 2) (ℓ : Fin (2 ^ r)) : ℝ :=
  (2 : ℝ) ^ (s - r) * ‖lambdaAlpha s r α ℓ‖

theorem sigmaHAlpha_pos (s r : ℕ) (α : Fin s → ZMod 2) (ℓ : Fin (2 ^ r)) :
    0 < sigmaHAlpha s r α ℓ := by
  unfold sigmaHAlpha
  exact mul_pos (by positivity) (norm_pos_iff.mpr (lambdaAlpha_ne_zero s r α ℓ))

/-- Unitary eigenvector matrix `Ṽ_α = D_sign * U_neg` diagonalizing `H̃_αᴴ * H̃_α`. -/
noncomputable def V_Htilde (s r : ℕ) (α : Fin s → ZMod 2) :
    Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℂ :=
  D_sign ℂ s r α * U_neg r

@[simp]
lemma D_sign_conjTranspose_C (s r : ℕ) (α : Fin s → ZMod 2) :
    (D_sign ℂ s r α)ᴴ = D_sign ℂ s r α := by
  ext w z
  by_cases hwz : w = z
  · subst hwz
    simp [D_sign]
  · simp [D_sign, hwz, Ne.symm hwz]

theorem V_Htilde_conjTranspose_mul_self (s r : ℕ) (α : Fin s → ZMod 2) :
    (V_Htilde s r α)ᴴ * V_Htilde s r α = 1 := by
  simp only [V_Htilde, Matrix.conjTranspose_mul, D_sign_conjTranspose_C]
  calc ((U_neg r)ᴴ * D_sign ℂ s r α) * (D_sign ℂ s r α * U_neg r)
      = (U_neg r)ᴴ * (D_sign ℂ s r α * D_sign ℂ s r α) * U_neg r := by simp [Matrix.mul_assoc]
    _ = (U_neg r)ᴴ * U_neg r := by rw [D_sign_mul_self, Matrix.mul_one]
    _ = 1 := U_neg_conjTranspose_mul_self r

theorem V_Htilde_mul_conjTranspose_self (s r : ℕ) (α : Fin s → ZMod 2) :
    V_Htilde s r α * (V_Htilde s r α)ᴴ = 1 :=
  mul_eq_one_comm.mp (V_Htilde_conjTranspose_mul_self s r α)

/-- Unitary diagonalization of `H̃_αᴴ * H̃_α` into `diag(‖λ_ℓ‖²)`. -/
theorem V_Htilde_conj_gram {s r : ℕ} {α : Fin s → ZMod 2} (h : HasHighestBit s α r) :
    (V_Htilde s r α)ᴴ * ((Htilde_alpha ℂ s r α)ᴴ * Htilde_alpha ℂ s r α) * V_Htilde s r α =
      Matrix.diagonal (fun ℓ => ((‖lambdaAlpha s r α ℓ‖ ^ 2 : ℝ) : ℂ)) := by
  have hD := D_sign_conj_Htilde_eq_G_alpha ℂ h
  have hH_mul_V :
      Htilde_alpha ℂ s r α * V_Htilde s r α =
        D_sign ℂ s r α * U_neg r * Matrix.diagonal (lambdaAlpha s r α) := by
    have hGU : G_alphaMat ℂ s r α * U_neg r = U_neg r * Matrix.diagonal (lambdaAlpha s r α) := by
      calc G_alphaMat ℂ s r α * U_neg r
          = (U_neg r * (U_neg r)ᴴ) * G_alphaMat ℂ s r α * U_neg r := by
              rw [U_neg_mul_conjTranspose_self, Matrix.one_mul]
        _ = U_neg r * ((U_neg r)ᴴ * G_alphaMat ℂ s r α * U_neg r) := by simp [Matrix.mul_assoc]
        _ = U_neg r * Matrix.diagonal (lambdaAlpha s r α) := by rw [U_neg_conj_G_alpha]
    calc Htilde_alpha ℂ s r α * (D_sign ℂ s r α * U_neg r)
        = (D_sign ℂ s r α * D_sign ℂ s r α) * Htilde_alpha ℂ s r α * D_sign ℂ s r α * U_neg r := by
            simp [D_sign_mul_self, Matrix.mul_assoc]
      _ = D_sign ℂ s r α * (D_sign ℂ s r α * Htilde_alpha ℂ s r α * D_sign ℂ s r α) * U_neg r := by
            simp [Matrix.mul_assoc]
      _ = D_sign ℂ s r α * (G_alphaMat ℂ s r α * U_neg r) := by
            rw [hD, Matrix.mul_assoc]
      _ = D_sign ℂ s r α * U_neg r * Matrix.diagonal (lambdaAlpha s r α) := by
            rw [hGU, Matrix.mul_assoc]
  calc (V_Htilde s r α)ᴴ * ((Htilde_alpha ℂ s r α)ᴴ * Htilde_alpha ℂ s r α) * V_Htilde s r α
      = (Htilde_alpha ℂ s r α * V_Htilde s r α)ᴴ * (Htilde_alpha ℂ s r α * V_Htilde s r α) := by
          simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (Matrix.diagonal (lambdaAlpha s r α))ᴴ *
          ((V_Htilde s r α)ᴴ * V_Htilde s r α) * Matrix.diagonal (lambdaAlpha s r α) := by
          rw [hH_mul_V]
          simp only [V_Htilde, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (Matrix.diagonal (lambdaAlpha s r α))ᴴ * Matrix.diagonal (lambdaAlpha s r α) := by
          rw [V_Htilde_conjTranspose_mul_self, Matrix.mul_one]
    _ = Matrix.diagonal (fun ℓ => ((‖lambdaAlpha s r α ℓ‖ ^ 2 : ℝ) : ℂ)) := by
          rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
          congr 1
          funext ℓ
          simpa [Complex.star_def, mul_comm] using
            (Complex.normSq_eq_conj_mul_self (z := lambdaAlpha s r α ℓ)).symm.trans
              (by simp [Complex.normSq_eq_norm_sq])

/-- `det(H̃_α) ≠ 0` over `ℂ` when `α` has highest nonzero bit `r`. -/
theorem det_Htilde_alpha_C_ne_zero {s r : ℕ} {α : Fin s → ZMod 2} (h : HasHighestBit s α r) :
    (Htilde_alpha ℂ s r α).det ≠ 0 := by
  have hG_det : (G_alphaMat ℂ s r α).det ≠ 0 := by
    have hconj := U_neg_conj_G_alpha s r α
    have hdet_eq : ((U_neg r)ᴴ * G_alphaMat ℂ s r α * U_neg r).det =
        (G_alphaMat ℂ s r α).det := by
      rw [Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul,
        U_neg_conjTranspose_mul_self, Matrix.det_one, one_mul]
    rw [← hdet_eq, hconj, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun ℓ _ => lambdaAlpha_ne_zero s r α ℓ
  have hD := D_sign_conj_Htilde_eq_G_alpha ℂ h
  have hD_det_sq : (D_sign ℂ s r α).det * (D_sign ℂ s r α).det = 1 := by
    rw [← Matrix.det_mul, D_sign_mul_self, Matrix.det_one]
  rw [← hD, Matrix.det_mul, Matrix.det_mul, mul_right_comm, hD_det_sq, one_mul] at hG_det
  exact hG_det

/-- `det(H̃_α) ≠ 0` over `ℚ` when `α` has highest nonzero bit `r`. -/
theorem det_Htilde_alpha_Q_ne_zero {s r : ℕ} {α : Fin s → ZMod 2} (h : HasHighestBit s α r) :
    (Htilde_alpha ℚ s r α).det ≠ 0 := by
  intro hdet0
  have hmap : (algebraMap ℚ ℂ).mapMatrix (Htilde_alpha ℚ s r α) = Htilde_alpha ℂ s r α := by
    ext w z
    simp [Htilde_alpha]
  have hdetC : (Htilde_alpha ℂ s r α).det = 0 := by
    rw [← hmap, ← RingHom.map_det, hdet0, map_zero]
  exact det_Htilde_alpha_C_ne_zero h hdetC

/-- `H̃_α` is invertible over `ℂ` and `ℚ` when `α` has highest nonzero bit `r`. -/
theorem isUnit_Htilde_alpha_C {s r : ℕ} {α : Fin s → ZMod 2} (h : HasHighestBit s α r) :
    IsUnit (Htilde_alpha ℂ s r α) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (IsUnit.mk0 _ (det_Htilde_alpha_C_ne_zero h))

theorem isUnit_Htilde_alpha_Q {s r : ℕ} {α : Fin s → ZMod 2} (h : HasHighestBit s α r) :
    IsUnit (Htilde_alpha ℚ s r α) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (IsUnit.mk0 _ (det_Htilde_alpha_Q_ne_zero h))

private lemma isUnit_det_of_mul_eq_one {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (A B : Matrix n n R) (h : A * B = 1) : IsUnit A.det :=
  (Matrix.isUnit_iff_isUnit_det A).mp ⟨⟨A, B, h, mul_eq_one_comm.mp h⟩, rfl⟩

/-- Exact rank of a block-diagonal square matrix over any field `𝔽`. -/
theorem rank_blockDiagonal_field {𝔽 m o : Type*} [Field 𝔽]
    [Fintype m] [DecidableEq m] [Fintype o] [DecidableEq o]
    (M : o → Matrix m m 𝔽) :
    (Matrix.blockDiagonal M).rank = ∑ k : o, (M k).rank := by
  classical
  have hnf : ∀ k : o, ∃ (V U : Matrix m m 𝔽)
      (e : m ≃ Fin (M k).rank ⊕ Fin (Fintype.card m - (M k).rank)),
        IsUnit V ∧ IsUnit U ∧ V * M k * U = (Matrix.fromBlocks 1 0 0 0).submatrix e e :=
    fun k => Matrix.exists_rank_normal_form (M k)
  choose V U e hV hU hEq using hnf
  choose V_u hVu using hV
  choose U_u hUu using hU
  let V_inv : Matrix (m × o) (m × o) 𝔽 := Matrix.blockDiagonal fun k => (↑(V_u k)⁻¹ : Matrix m m 𝔽)
  let U_inv : Matrix (m × o) (m × o) 𝔽 := Matrix.blockDiagonal fun k => (↑(U_u k)⁻¹ : Matrix m m 𝔽)
  have hV_bd_unit : IsUnit (Matrix.blockDiagonal V).det := by
    refine isUnit_det_of_mul_eq_one _ V_inv ?_
    rw [← Matrix.blockDiagonal_mul]
    have h1 : (fun k : o => V k * (↑(V_u k)⁻¹ : Matrix m m 𝔽)) = 1 := by
      funext k
      rw [← hVu k, Units.mul_inv]
      rfl
    rw [h1, Matrix.blockDiagonal_one]
  have hU_bd_unit : IsUnit (Matrix.blockDiagonal U).det := by
    refine isUnit_det_of_mul_eq_one _ U_inv ?_
    rw [← Matrix.blockDiagonal_mul]
    have h1 : (fun k : o => U k * (↑(U_u k)⁻¹ : Matrix m m 𝔽)) = 1 := by
      funext k
      rw [← hUu k, Units.mul_inv]
      rfl
    rw [h1, Matrix.blockDiagonal_one]
  let d : ∀ k : o, m → 𝔽 := fun k i =>
    Sum.elim (fun _ => (1 : 𝔽)) (fun _ => (0 : 𝔽)) (e k i)
  have hdiag_k : ∀ k : o,
      (Matrix.fromBlocks (1 : Matrix (Fin (M k).rank) (Fin (M k).rank) 𝔽) 0 0
        (0 : Matrix (Fin (Fintype.card m - (M k).rank))
          (Fin (Fintype.card m - (M k).rank)) 𝔽)).submatrix (e k) (e k) =
        Matrix.diagonal (d k) := by
    intro k
    ext i j
    simp only [Matrix.submatrix_apply, d]
    by_cases hij : i = j
    · subst hij
      cases hcase : e k i <;> simp [hcase]
    · have he_ne : e k i ≠ e k j := fun heq => hij ((e k).injective heq)
      simp only [Matrix.diagonal_apply_ne _ hij]
      cases hi : e k i <;> cases hj : e k j <;> simp_all
  have hbd_eq :
      Matrix.blockDiagonal V * Matrix.blockDiagonal M * Matrix.blockDiagonal U =
        Matrix.diagonal (fun ik : m × o => d ik.2 ik.1) := by
    rw [← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_mul]
    ext ⟨i₁, k₁⟩ ⟨i₂, k₂⟩
    by_cases hk : k₁ = k₂
    · subst hk
      rw [Matrix.blockDiagonal_apply_eq, hEq k₁, hdiag_k k₁]
      by_cases hi : i₁ = i₂
      · subst hi; simp
      · have hne : (i₁, k₁) ≠ (i₂, k₁) := fun h => hi (Prod.mk.inj h).1
        simp [hi, hne]
    · have hne : (i₁, k₁) ≠ (i₂, k₂) := fun h => hk (Prod.mk.inj h).2
      simp [Matrix.blockDiagonal_apply, hk, hne]
  have hrk_k : ∀ k : o, Fintype.card {i : m // d k i ≠ 0} = (M k).rank := by
    intro k
    have hVdet : IsUnit (V k).det := (Matrix.isUnit_iff_isUnit_det _).mp (hVu k ▸ (V_u k).isUnit)
    have hUdet : IsUnit (U k).det := (Matrix.isUnit_iff_isUnit_det _).mp (hUu k ▸ (U_u k).isUnit)
    have hr := Matrix.rank_diagonal (d k)
    rw [← hdiag_k k, ← hEq k, Matrix.rank_mul_eq_left_of_isUnit_det (U k) _ hUdet,
      Matrix.rank_mul_eq_right_of_isUnit_det (V k) _ hVdet] at hr
    exact hr.symm
  have hrk_bd : (Matrix.blockDiagonal M).rank =
      Fintype.card {ik : m × o // d ik.2 ik.1 ≠ 0} := by
    rw [← Matrix.rank_mul_eq_right_of_isUnit_det (Matrix.blockDiagonal V) _ hV_bd_unit,
      ← Matrix.rank_mul_eq_left_of_isUnit_det (Matrix.blockDiagonal U) _ hU_bd_unit,
      hbd_eq, Matrix.rank_diagonal]
  rw [hrk_bd]
  have hequiv : {ik : m × o // d ik.2 ik.1 ≠ 0} ≃ Σ k : o, {i : m // d k i ≠ 0} :=
    { toFun := fun ⟨⟨i, k⟩, h⟩ => ⟨k, ⟨i, h⟩⟩
      invFun := fun ⟨k, ⟨i, h⟩⟩ => ⟨(i, k), h⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, ⟨_, _⟩⟩ => rfl }
  rw [Fintype.card_congr hequiv, Fintype.card_sigma]
  exact Finset.sum_congr rfl fun k _ => hrk_k k

/-- Exact rank of a Kronecker product of square matrices over any field `𝔽`. -/
theorem rank_kronecker_field {𝔽 l m : Type*} [Field 𝔽]
    [Fintype l] [DecidableEq l] [Fintype m] [DecidableEq m]
    (A : Matrix l l 𝔽) (B : Matrix m m 𝔽) :
    (Matrix.kroneckerMap (· * ·) A B).rank = A.rank * B.rank := by
  classical
  obtain ⟨VA, UA, eA, hVA, hUA, hEqA⟩ := Matrix.exists_rank_normal_form A
  obtain ⟨VB, UB, eB, hVB, hUB, hEqB⟩ := Matrix.exists_rank_normal_form B
  obtain ⟨VA_u, rfl⟩ := hVA
  obtain ⟨UA_u, rfl⟩ := hUA
  obtain ⟨VB_u, rfl⟩ := hVB
  obtain ⟨UB_u, rfl⟩ := hUB
  have hV_unit : IsUnit (Matrix.kroneckerMap (· * ·) (VA_u : Matrix l l 𝔽) (VB_u : Matrix m m 𝔽)).det := by
    refine isUnit_det_of_mul_eq_one _
      (Matrix.kroneckerMap (· * ·) (↑VA_u⁻¹ : Matrix l l 𝔽) (↑VB_u⁻¹ : Matrix m m 𝔽)) ?_
    rw [← Matrix.mul_kronecker_mul, Units.mul_inv, Units.mul_inv, Matrix.one_kronecker_one]
  have hU_unit : IsUnit (Matrix.kroneckerMap (· * ·) (UA_u : Matrix l l 𝔽) (UB_u : Matrix m m 𝔽)).det := by
    refine isUnit_det_of_mul_eq_one _
      (Matrix.kroneckerMap (· * ·) (↑UA_u⁻¹ : Matrix l l 𝔽) (↑UB_u⁻¹ : Matrix m m 𝔽)) ?_
    rw [← Matrix.mul_kronecker_mul, Units.mul_inv, Units.mul_inv, Matrix.one_kronecker_one]
  let dA : l → 𝔽 := fun i => Sum.elim (fun _ => (1 : 𝔽)) (fun _ => (0 : 𝔽)) (eA i)
  let dB : m → 𝔽 := fun j => Sum.elim (fun _ => (1 : 𝔽)) (fun _ => (0 : 𝔽)) (eB j)
  have hdiagA :
      (Matrix.fromBlocks (1 : Matrix (Fin A.rank) (Fin A.rank) 𝔽) 0 0
        (0 : Matrix (Fin (Fintype.card l - A.rank)) (Fin (Fintype.card l - A.rank)) 𝔽)).submatrix eA eA =
        Matrix.diagonal dA := by
    ext i j
    simp only [Matrix.submatrix_apply, dA]
    by_cases hij : i = j
    · subst hij; cases hcase : eA i <;> simp [hcase]
    · have he_ne : eA i ≠ eA j := fun heq => hij (eA.injective heq)
      simp only [Matrix.diagonal_apply_ne _ hij]
      cases hi : eA i <;> cases hj : eA j <;> simp_all
  have hdiagB :
      (Matrix.fromBlocks (1 : Matrix (Fin B.rank) (Fin B.rank) 𝔽) 0 0
        (0 : Matrix (Fin (Fintype.card m - B.rank)) (Fin (Fintype.card m - B.rank)) 𝔽)).submatrix eB eB =
        Matrix.diagonal dB := by
    ext i j
    simp only [Matrix.submatrix_apply, dB]
    by_cases hij : i = j
    · subst hij; cases hcase : eB i <;> simp [hcase]
    · have he_ne : eB i ≠ eB j := fun heq => hij (eB.injective heq)
      simp only [Matrix.diagonal_apply_ne _ hij]
      cases hi : eB i <;> cases hj : eB j <;> simp_all
  have hprod_eq :
      Matrix.kroneckerMap (· * ·) (VA_u : Matrix l l 𝔽) (VB_u : Matrix m m 𝔽) *
        Matrix.kroneckerMap (· * ·) A B *
        Matrix.kroneckerMap (· * ·) (UA_u : Matrix l l 𝔽) (UB_u : Matrix m m 𝔽) =
      Matrix.diagonal (fun ij : l × m => dA ij.1 * dB ij.2) := by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hEqA, hEqB, hdiagA, hdiagB]
    ext ⟨i₁, j₁⟩ ⟨i₂, j₂⟩
    simp only [Matrix.kroneckerMap_apply]
    by_cases hij : (i₁, j₁) = (i₂, j₂)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hij
      simp
    · simp only [Matrix.diagonal_apply_ne _ hij]
      by_cases hi : i₁ = i₂
      · subst hi
        have hj : j₁ ≠ j₂ := fun h => hij (congrArg _ h)
        simp [hj]
      · simp [hi]
  have hrA : Fintype.card {i : l // dA i ≠ 0} = A.rank := by
    have hVAdet : IsUnit (VA_u : Matrix l l 𝔽).det := (Matrix.isUnit_iff_isUnit_det _).mp VA_u.isUnit
    have hUAdet : IsUnit (UA_u : Matrix l l 𝔽).det := (Matrix.isUnit_iff_isUnit_det _).mp UA_u.isUnit
    have hr := Matrix.rank_diagonal dA
    rw [← hdiagA, ← hEqA, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hUAdet,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hVAdet] at hr
    exact hr.symm
  have hrB : Fintype.card {j : m // dB j ≠ 0} = B.rank := by
    have hVBdet : IsUnit (VB_u : Matrix m m 𝔽).det := (Matrix.isUnit_iff_isUnit_det _).mp VB_u.isUnit
    have hUBdet : IsUnit (UB_u : Matrix m m 𝔽).det := (Matrix.isUnit_iff_isUnit_det _).mp UB_u.isUnit
    have hr := Matrix.rank_diagonal dB
    rw [← hdiagB, ← hEqB, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hUBdet,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hVBdet] at hr
    exact hr.symm
  rw [← Matrix.rank_mul_eq_right_of_isUnit_det _ (Matrix.kroneckerMap (· * ·) A B) hV_unit,
    ← Matrix.rank_mul_eq_left_of_isUnit_det _ _ hU_unit, hprod_eq, Matrix.rank_diagonal]
  have hequiv : {ij : l × m // dA ij.1 * dB ij.2 ≠ 0} ≃
      {i : l // dA i ≠ 0} × {j : m // dB j ≠ 0} :=
    { toFun := fun ⟨⟨i, j⟩, h⟩ =>
        ⟨⟨i, left_ne_zero_of_mul h⟩, ⟨j, right_ne_zero_of_mul h⟩⟩
      invFun := fun ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ => ⟨(i, j), mul_ne_zero hi hj⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl }
  rw [Fintype.card_congr hequiv, Fintype.card_prod, hrA, hrB]

/-- Exact rank `1` of any nonempty `allOnesMat 𝔽 n` (`n ≥ 1`) over a field `𝔽`. -/
theorem rank_allOnesMat {𝔽 : Type*} [Field 𝔽] {n : ℕ} (hn : 0 < n) :
    (allOnesMat 𝔽 n).rank = 1 := by
  have hvec : allOnesMat 𝔽 n = Matrix.vecMulVec (fun _ : Fin n => (1 : 𝔽)) (fun _ : Fin n => (1 : 𝔽)) := by
    ext i j
    simp [allOnesMat, Matrix.vecMulVec_apply]
  have hle : (allOnesMat 𝔽 n).rank ≤ 1 := by
    rw [hvec]
    exact Matrix.rank_vecMulVec_le _ _
  have hge : 1 ≤ (allOnesMat 𝔽 n).rank := by
    let idx0 : Fin n := ⟨0, hn⟩
    have hsub := Matrix.rank_submatrix_le (allOnesMat 𝔽 n) (fun _ : Fin 1 => idx0) (fun _ : Fin 1 => idx0)
    have hsub_eq : (allOnesMat 𝔽 n).submatrix (fun _ : Fin 1 => idx0) (fun _ : Fin 1 => idx0) =
        (1 : Matrix (Fin 1) (Fin 1) 𝔽) := by
      ext i j
      fin_cases i; fin_cases j
      simp [allOnesMat]
    rw [hsub_eq, Matrix.rank_one, Fintype.card_fin] at hsub
    exact hsub
  omega

/-- `H_0 = J_{2^s}` has rank `1` over any field `𝔽` (including `ℂ` and `ℚ`). -/
theorem rank_H_alpha_zero (𝔽 : Type*) [Field 𝔽] (s : ℕ) :
    (H_alpha 𝔽 s 0).rank = 1 := by
  have heq : H_alpha 𝔽 s 0 = allOnesMat 𝔽 (2 ^ s) := by
    ext w z
    simp [H_alpha, allOnesMat]
  rw [heq]
  exact rank_allOnesMat (by positivity)

theorem rank_H_alpha_zero_C (s : ℕ) : (H_alpha ℂ s 0).rank = 1 :=
  rank_H_alpha_zero ℂ s

theorem rank_H_alpha_zero_Q (s : ℕ) : (H_alpha ℚ s 0).rank = 1 :=
  rank_H_alpha_zero ℚ s

/-- **Theorem 4.1(b), Exact Rank of `H_α` (`α ≠ 0` with highest bit `r`)** over `ℂ` and `ℚ`. -/
theorem rank_H_alpha_C {s r : ℕ} {α : Fin s → ZMod 2} (h : HasHighestBit s α r) :
    (H_alpha ℂ s α).rank = 2 ^ r := by
  rw [← Matrix.rank_reindex (divModPowTwoEquiv s r h.2.1) (divModPowTwoEquiv s r h.2.1),
    H_alpha_reindex_eq_kronecker ℂ h, rank_kronecker_field,
    rank_allOnesMat (by positivity), one_mul,
    Matrix.rank_of_det_ne_zero (det_Htilde_alpha_C_ne_zero h), Fintype.card_fin]

theorem rank_H_alpha_Q {s r : ℕ} {α : Fin s → ZMod 2} (h : HasHighestBit s α r) :
    (H_alpha ℚ s α).rank = 2 ^ r := by
  rw [← Matrix.rank_reindex (divModPowTwoEquiv s r h.2.1) (divModPowTwoEquiv s r h.2.1),
    H_alpha_reindex_eq_kronecker ℚ h, rank_kronecker_field,
    rank_allOnesMat (by positivity), one_mul,
    Matrix.rank_of_det_ne_zero (det_Htilde_alpha_Q_ne_zero h), Fintype.card_fin]

open Classical in
private lemma card_hasHighestBit {s r : ℕ} (hr1 : 1 ≤ r) (hrs : r ≤ s) :
    ((Finset.univ : Finset (Fin s → ZMod 2)).filter fun α => HasHighestBit s α r).card =
      2 ^ (r - 1) := by
  let f : (Fin (r - 1) → ZMod 2) → (Fin s → ZMod 2) := fun β i =>
    if hi : i.val < r - 1 then β ⟨i.val, hi⟩
    else if i.val = r - 1 then 1 else 0
  have hf_mem : ∀ β : Fin (r - 1) → ZMod 2,
      f β ∈ (Finset.univ : Finset (Fin s → ZMod 2)).filter fun α => HasHighestBit s α r := by
    intro β
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, hr1, hrs, ?_, ?_⟩
    · simp [f]
    · intro i hi
      have h1 : ¬(i.val < r - 1) := by omega
      have h2 : i.val ≠ r - 1 := by omega
      simp [f, h1, h2]
  have hf_inj : Function.Injective f := by
    intro β₁ β₂ heq
    ext j
    have hj_lt : j.val < s := by have := j.isLt; omega
    have hv := congr_fun heq ⟨j.val, hj_lt⟩
    simpa [f, j.isLt] using hv
  have hf_surj : ∀ α ∈ (Finset.univ : Finset (Fin s → ZMod 2)).filter (fun α => HasHighestBit s α r),
      ∃ β : Fin (r - 1) → ZMod 2, f β = α := by
    intro α hα
    obtain ⟨_, _, _, htop, hzero⟩ := Finset.mem_filter.mp hα
    refine ⟨fun j => α ⟨j.val, by have := j.isLt; omega⟩, ?_⟩
    ext i
    dsimp only [f]
    split_ifs with hlt heq
    · rfl
    · have hidx : i = ⟨r - 1, by omega⟩ := by ext; exact heq
      rw [hidx, htop]
    · exact (hzero i (by omega)).symm
  have hcard_dom : Fintype.card (Fin (r - 1) → ZMod 2) = 2 ^ (r - 1) := by
    simp
  rw [← hcard_dom, ← Finset.card_univ]
  symm
  refine Finset.card_bij (fun β _ => f β) (fun β _ => hf_mem β)
    (fun β₁ _ β₂ _ h => hf_inj h) (fun α hα => ?_)
  obtain ⟨β, rfl⟩ := hf_surj α hα
  exact ⟨β, Finset.mem_univ β, rfl⟩

private lemma rank_K_coreMat_eq_sum_field (𝔽 : Type*) [Field 𝔽] [CharZero 𝔽] (s : ℕ) :
    (K_coreMat 𝔽 s).rank = ∑ α : Fin s → ZMod 2, (H_alpha 𝔽 s α).rank := by
  classical
  let W_I := Matrix.kroneckerMap (· * ·) (W_unnorm 𝔽 s) (1 : Matrix (Fin (2 ^ s)) (Fin (2 ^ s)) 𝔽)
  have h2ne : ((2 : 𝔽) ^ s) ≠ 0 := pow_ne_zero s (by norm_num)
  have hW_inv : W_I * ((((2 : 𝔽) ^ s)⁻¹) • W_I) = 1 := by
    rw [Matrix.mul_smul]
    have hmul : W_I * W_I = ((2 : 𝔽) ^ s) • 1 := by
      dsimp only [W_I]
      rw [← Matrix.mul_kronecker_mul, W_unnorm_mul_self, mul_one]
      ext ⟨α₁, w₁⟩ ⟨α₂, w₂⟩
      by_cases h1 : α₁ = α₂ <;> by_cases h2 : w₁ = w₂ <;>
        simp [Matrix.kroneckerMap_apply, h1, h2]
    rw [hmul, smul_smul, inv_mul_cancel₀ h2ne, one_smul]
  have hW_unit : IsUnit W_I.det := isUnit_det_of_mul_eq_one W_I _ hW_inv
  have hconj :
      (W_I * K_coreMat 𝔽 s * W_I).reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _) =
        Matrix.blockDiagonal (fun α : Fin s → ZMod 2 => ((2 : 𝔽) ^ s) • H_alpha 𝔽 s α) := by
    ext ⟨w, α⟩ ⟨z, β⟩
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodComm_symm,
      Equiv.coe_prodComm, Prod.swap_prod_mk]
    dsimp only [W_I]
    rw [walsh_conj_K_coreMat_unnorm]
    by_cases hαβ : α = β
    · subst hαβ
      simp
    · simp [Matrix.blockDiagonal_apply, hαβ]
  have hrk : (K_coreMat 𝔽 s).rank =
      (Matrix.blockDiagonal (fun α : Fin s → ZMod 2 => ((2 : 𝔽) ^ s) • H_alpha 𝔽 s α)).rank := by
    rw [← hconj, Matrix.rank_reindex, Matrix.rank_mul_eq_left_of_isUnit_det W_I _ hW_unit,
      Matrix.rank_mul_eq_right_of_isUnit_det W_I _ hW_unit]
  rw [hrk, rank_blockDiagonal_field]
  refine Finset.sum_congr rfl fun α _ => ?_
  exact Matrix.rank_smul_of_mem_nonZeroDivisors (H_alpha 𝔽 s α)
    (mem_nonZeroDivisors_of_ne_zero h2ne)

private lemma geom_sum_ranks (s : ℕ) :
    3 * (1 + ∑ r ∈ Finset.Icc 1 s, 2 ^ (r - 1) * 2 ^ r) = 2 * 4 ^ s + 1 := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hicc : Finset.Icc 1 (s + 1) = insert (s + 1) (Finset.Icc 1 s) := by
      ext r; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hmem : s + 1 ∉ Finset.Icc 1 s := by simp
    rw [hicc, Finset.sum_insert hmem]
    have hterm : 2 ^ (s + 1 - 1) * 2 ^ (s + 1) = 2 * 4 ^ s := by
      have h4 : (4 : ℕ) ^ s = 2 ^ s * 2 ^ s := by
        calc (4 : ℕ) ^ s = (2 * 2) ^ s := by norm_num
          _ = 2 ^ s * 2 ^ s := mul_pow 2 2 s
      simp only [Nat.add_sub_cancel, pow_succ, h4]
      ring
    rw [hterm, pow_succ 4 s]
    linarith

/-- **Theorem 4.1(b), Exact Rational Rank of `C_t` (`K_coreMat`)**:
`3 * rank_ℚ(C_{s+1}) = 2 * 4^s + 1`, i.e., `rank(C_t) = (2 · 4^s + 1) / 3` (Paper 2, eq. (4.5)). -/
theorem rank_K_coreMat_Q (s : ℕ) :
    3 * (K_coreMat ℚ s).rank = 2 * 4 ^ s + 1 := by
  classical
  rw [rank_K_coreMat_eq_sum_field ℚ s]
  have hsplit :
      (∑ α : Fin s → ZMod 2, (H_alpha ℚ s α).rank) =
        (H_alpha ℚ s 0).rank +
          ∑ α ∈ (Finset.univ : Finset (Fin s → ZMod 2)).erase 0, (H_alpha ℚ s α).rank := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin s → ZMod 2))]
  rw [hsplit, rank_H_alpha_zero_Q]
  have hpart :
      (Finset.univ : Finset (Fin s → ZMod 2)).erase 0 =
        (Finset.Icc 1 s).biUnion (fun r => Finset.univ.filter fun α : Fin s → ZMod 2 => HasHighestBit s α r) := by
    ext α
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_biUnion,
      Finset.mem_Icc, Finset.mem_filter]
    constructor
    · intro hα
      obtain ⟨r, hr, _⟩ := existsUnique_hasHighestBit s hα
      exact ⟨r, ⟨hr.1, hr.2.1⟩, trivial, hr⟩
    · rintro ⟨r, _, _, _, _, htop, _⟩ h0
      subst h0
      change (0 : ZMod 2) = 1 at htop
      revert htop; decide
  have hdisj :
      Set.PairwiseDisjoint (Finset.Icc 1 s : Set ℕ)
        (fun r => Finset.univ.filter fun α : Fin s → ZMod 2 => HasHighestBit s α r) := by
    intro r₁ _ r₂ _ hrne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro α h₁ h₂
    have h1 := (Finset.mem_filter.mp h₁).2
    have h2 := (Finset.mem_filter.mp h₂).2
    have hα0 : α ≠ 0 := by
      intro h0; subst h0
      rcases h1 with ⟨_, _, htop, _⟩
      simp at htop
    obtain ⟨r₀, _, huniq⟩ := existsUnique_hasHighestBit s hα0
    exact hrne ((huniq r₁ h1).trans (huniq r₂ h2).symm)
  rw [hpart, Finset.sum_biUnion hdisj]
  have hinner :
      ∀ r ∈ Finset.Icc 1 s,
        (∑ α ∈ Finset.univ.filter (fun α : Fin s → ZMod 2 => HasHighestBit s α r),
            (H_alpha ℚ s α).rank) =
          2 ^ (r - 1) * 2 ^ r := by
    intro r hr
    obtain ⟨hr1, hrs⟩ := Finset.mem_Icc.mp hr
    have hconst :
        ∀ α ∈ Finset.univ.filter (fun α : Fin s → ZMod 2 => HasHighestBit s α r),
          (H_alpha ℚ s α).rank = 2 ^ r :=
      fun α hα => rank_H_alpha_Q (Finset.mem_filter.mp hα).2
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, card_hasHighestBit hr1 hrs]
  rw [Finset.sum_congr rfl hinner]
  exact geom_sum_ranks s

/-- Exact complex rank of `K_t`: `3 * rank_ℂ(K_{s+1}) = 2 * 4^s + 1`. -/
theorem rank_K_coreMat_C (s : ℕ) :
    3 * (K_coreMat ℂ s).rank = 2 * 4 ^ s + 1 := by
  classical
  rw [rank_K_coreMat_eq_sum_field ℂ s]
  have h_eq : ∀ α : Fin s → ZMod 2, (H_alpha ℂ s α).rank = (H_alpha ℚ s α).rank := by
    intro α
    by_cases hα : α = 0
    · subst hα
      rw [rank_H_alpha_zero_C, rank_H_alpha_zero_Q]
    · obtain ⟨r, hr, _⟩ := existsUnique_hasHighestBit s hα
      rw [rank_H_alpha_C hr, rank_H_alpha_Q hr]
  simp_rw [h_eq, ← rank_K_coreMat_eq_sum_field ℚ s]
  exact rank_K_coreMat_Q s

/-! #### Local Affine-XOR Isomorphism `M_{s+1} ≅ I_2 ⊗ K_{s+1} ⊗ J_2` for `M_t` Rank & Spectrum -/

private lemma natBit_eq_of_testBit (n j : ℕ) :
    natBit n j = if Nat.testBit n j then 1 else 0 := by
  rw [natBit, Nat.testBit_eq_decide_div_mod_eq]
  have hmod : (n / 2 ^ j) % 2 = 0 ∨ (n / 2 ^ j) % 2 = 1 := Nat.mod_two_eq_zero_or_one _
  have hcast : ((n / 2 ^ j : ℕ) : ZMod 2) = (((n / 2 ^ j) % 2 : ℕ) : ZMod 2) := by
    rw [← ZMod.natCast_mod]
  rw [hcast]
  rcases hmod with h0 | h1
  · simp [h0]
  · simp [h1]

private lemma nat_xor_xor_cancel_right (a b : ℕ) : (a ^^^ b) ^^^ b = a :=
  Nat.eq_of_testBit_eq fun i => by simp [Nat.testBit_xor]

private lemma natBit_xor (a b j : ℕ) :
    natBit (a ^^^ b) j = natBit a j + natBit b j := by
  rw [natBit_eq_of_testBit, natBit_eq_of_testBit, natBit_eq_of_testBit, Nat.testBit_xor]
  cases Nat.testBit a j <;> cases Nat.testBit b j <;> decide

private lemma eq_of_natBit_eq {s a b : ℕ} (ha : a < 2 ^ s) (hb : b < 2 ^ s)
    (hbits : ∀ j < s, natBit a j = natBit b j) : a = b := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  by_cases hj : j < s
  · have h := hbits j hj
    rw [natBit_eq_of_testBit, natBit_eq_of_testBit] at h
    cases hta : Nat.testBit a j <;> cases htb : Nat.testBit b j
    · rfl
    · simp [hta, htb] at h
    · simp [hta, htb] at h
    · rfl
  · have hge : 2 ^ s ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hge),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hge)]

private noncomputable def mCoordEquiv (s : ℕ) :
    Fin (2 ^ (s + 1)) × Fin (2 ^ (s + 1)) ≃
      Fin 2 × (((Fin s → ZMod 2) × Fin (2 ^ s)) × Fin 2) := by
  classical
  let toF : Fin (2 ^ (s + 1)) × Fin (2 ^ (s + 1)) →
      Fin 2 × (((Fin s → ZMod 2) × Fin (2 ^ s)) × Fin 2) := fun ⟨u, w⟩ =>
    let x := u.val ^^^ w.val
    (⟨x % 2, Nat.mod_lt _ (by decide)⟩,
     ((fun i : Fin s => natBit x (i.val + 1)),
      ⟨w.val % 2 ^ s, Nat.mod_lt _ (by positivity)⟩),
     ⟨w.val / 2 ^ s, by
       have hw : w.val < 2 * 2 ^ s := by simpa [pow_succ, mul_comm] using w.isLt
       exact Nat.div_lt_of_lt_mul (by simpa [mul_comm] using hw)⟩)
  have hinj : Function.Injective toF := by
    rintro ⟨u₁, w₁⟩ ⟨u₂, w₂⟩ heq
    have hx0 : (u₁.val ^^^ w₁.val) % 2 = (u₂.val ^^^ w₂.val) % 2 :=
      congrArg Fin.val (Prod.mk.inj heq).1
    have hxp : (fun i : Fin s => natBit (u₁.val ^^^ w₁.val) (i.val + 1)) =
        (fun i : Fin s => natBit (u₂.val ^^^ w₂.val) (i.val + 1)) :=
      (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj heq).2).1).1
    have hw_mod : w₁.val % 2 ^ s = w₂.val % 2 ^ s :=
      congrArg Fin.val (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj heq).2).1).2
    have hw_div : w₁.val / 2 ^ s = w₂.val / 2 ^ s :=
      congrArg Fin.val (Prod.mk.inj (Prod.mk.inj heq).2).2
    have hw_eq : w₁.val = w₂.val := by
      rw [← Nat.div_add_mod w₁.val (2 ^ s), ← Nat.div_add_mod w₂.val (2 ^ s), hw_div, hw_mod]
    have hx_lt₁ : u₁.val ^^^ w₁.val < 2 ^ (s + 1) := Nat.xor_lt_two_pow u₁.isLt w₁.isLt
    have hx_lt₂ : u₂.val ^^^ w₂.val < 2 ^ (s + 1) := Nat.xor_lt_two_pow u₂.isLt w₂.isLt
    have hx_eq : u₁.val ^^^ w₁.val = u₂.val ^^^ w₂.val := by
      refine eq_of_natBit_eq hx_lt₁ hx_lt₂ fun j hj => ?_
      cases j with
      | zero =>
        simp only [natBit, pow_zero, Nat.div_one]
        exact (ZMod.natCast_eq_natCast_iff' _ _ 2).mpr hx0
      | succ j' =>
        exact congr_fun hxp ⟨j', by omega⟩
    have hu_eq : u₁.val = u₂.val := by
      calc u₁.val = (u₁.val ^^^ w₁.val) ^^^ w₁.val := (nat_xor_xor_cancel_right u₁.val w₁.val).symm
        _ = (u₂.val ^^^ w₂.val) ^^^ w₂.val := by rw [hx_eq, hw_eq]
        _ = u₂.val := nat_xor_xor_cancel_right u₂.val w₂.val
    exact Prod.ext (Fin.ext hu_eq) (Fin.ext hw_eq)
  have hcard :
      Fintype.card (Fin (2 ^ (s + 1)) × Fin (2 ^ (s + 1))) =
        Fintype.card (Fin 2 × (((Fin s → ZMod 2) × Fin (2 ^ s)) × Fin 2)) := by
    simp [pow_succ]
    ring
  exact Equiv.ofBijective toF ((Fintype.bijective_iff_injective_and_card toF).mpr ⟨hinj, hcard⟩)

private lemma M_rel_iff_mCoordEquiv (s : ℕ)
    (r c : Fin (2 ^ (s + 1)) × Fin (2 ^ (s + 1))) :
    M_rel (s + 1) r c ↔
      (mCoordEquiv s r).1 = (mCoordEquiv s c).1 ∧
        K_coreRel s (mCoordEquiv s r).2.1 (mCoordEquiv s c).2.1 := by
  rcases r with ⟨u, w⟩
  rcases c with ⟨v, z⟩
  let M := 2 ^ (s + 1)
  have hM : 0 < M := by positivity
  let d := (z.val + M - w.val) % M
  have hd_lt : d < M := Nat.mod_lt _ hM
  have hwd_mod : (w.val + d) % M = z.val := by
    have hw : w.val ≤ M := w.isLt.le
    have h1 : (w.val + ((z.val + M - w.val) % M)) % M = (w.val + (z.val + M - w.val)) % M := by
      rw [Nat.add_mod_mod]
    have h2 : w.val + (z.val + M - w.val) = z.val + M := by omega
    rw [h1, h2, Nat.add_mod_right, Nat.mod_eq_of_lt z.isLt]
  have huv_lt : u.val ^^^ v.val < M := Nat.xor_lt_two_pow u.isLt v.isLt
  have hrel_iff_d : M_rel (s + 1) (u, w) (v, z) ↔ u.val ^^^ v.val = d := by
    simp only [M_rel]
    constructor
    · intro hmod
      change ((u.val ^^^ v.val) + w.val) % M = z.val at hmod
      have hw : w.val < M := w.isLt
      have h1 : d = ((w.val + (u.val ^^^ v.val)) % M + M - w.val) % M := by
        dsimp only [d]
        rw [← hmod, add_comm (u.val ^^^ v.val) w.val]
      rw [h1]
      by_cases hwrap : w.val + (u.val ^^^ v.val) < M
      · rw [Nat.mod_eq_of_lt hwrap]
        have h2 : w.val + (u.val ^^^ v.val) + M - w.val = (u.val ^^^ v.val) + M := by omega
        rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt huv_lt]
      · have hsub : (w.val + (u.val ^^^ v.val)) % M = w.val + (u.val ^^^ v.val) - M := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [hsub]
        have h2 : w.val + (u.val ^^^ v.val) - M + M - w.val = u.val ^^^ v.val := by omega
        rw [h2, Nat.mod_eq_of_lt huv_lt]
    · intro heq
      change ((u.val ^^^ v.val) + w.val) % M = z.val
      rw [heq, add_comm, hwd_mod]
  rw [hrel_iff_d]
  have hwd_mod' : (w.val + d) % 2 ^ (s + 1) = z.val % 2 ^ (s + 1) := by
    change (w.val + d) % M = z.val % M
    rw [hwd_mod, Nat.mod_eq_of_lt z.isLt]
  have hd_bit0 : natBit d 0 = natBit w.val 0 + natBit z.val 0 := by
    have h0 := binary_sub_carry_bit (r := s + 1) (j := 0) (w := w.val) (k := d) (z := z.val)
      (by omega) hwd_mod'
    have hbb0 : borrowBit 0 w.val z.val = 0 := by simp [borrowBit, pow_zero, Nat.mod_one]
    simpa [hbb0] using h0
  have hd_bits : ∀ i : Fin s,
      natBit d (i.val + 1) =
        natBit w.val (i.val + 1) + natBit z.val (i.val + 1) +
          borrowBit (i.val + 1) (w.val % 2 ^ s) (z.val % 2 ^ s) := by
    intro i
    have hi := binary_sub_carry_bit (r := s + 1) (j := i.val + 1) (w := w.val) (k := d) (z := z.val)
      (by omega) hwd_mod'
    rw [hi, borrowBit_mod_pow (by omega)]
  constructor
  · intro huv_eq
    constructor
    · simp only [mCoordEquiv, Equiv.ofBijective_apply]
      ext
      dsimp only
      have hb0 : natBit (u.val ^^^ v.val) 0 = natBit d 0 := by rw [huv_eq]
      rw [natBit_xor, hd_bit0] at hb0
      have hxwyz : natBit (u.val ^^^ w.val) 0 = natBit (v.val ^^^ z.val) 0 := by
        rw [natBit_xor, natBit_xor]
        calc natBit u.val 0 + natBit w.val 0
            = (natBit u.val 0 + natBit v.val 0) + natBit v.val 0 + natBit w.val 0 := by
                rw [add_assoc (natBit u.val 0) (natBit v.val 0), zmod2_add_self, add_zero]
          _ = (natBit w.val 0 + natBit z.val 0) + natBit v.val 0 + natBit w.val 0 := by rw [hb0]
          _ = natBit v.val 0 + (natBit w.val 0 + natBit w.val 0) + natBit z.val 0 := by ring
          _ = natBit v.val 0 + natBit z.val 0 := by rw [zmod2_add_self, add_zero]
      simp only [natBit, pow_zero, Nat.div_one] at hxwyz
      exact (ZMod.natCast_eq_natCast_iff' _ _ 2).mp hxwyz
    · simp only [mCoordEquiv, Equiv.ofBijective_apply, K_coreRel]
      ext i
      dsimp only [Pi.add_apply, borrowVec]
      have hbi : natBit (u.val ^^^ v.val) (i.val + 1) = natBit d (i.val + 1) := by rw [huv_eq]
      rw [natBit_xor, hd_bits i] at hbi
      rw [natBit_xor, natBit_xor]
      calc (natBit u.val (i.val + 1) + natBit w.val (i.val + 1)) +
            (natBit v.val (i.val + 1) + natBit z.val (i.val + 1))
          = (natBit u.val (i.val + 1) + natBit v.val (i.val + 1)) +
              natBit w.val (i.val + 1) + natBit z.val (i.val + 1) := by ring
        _ = (natBit w.val (i.val + 1) + natBit z.val (i.val + 1) +
              borrowBit (i.val + 1) (w.val % 2 ^ s) (z.val % 2 ^ s)) +
              natBit w.val (i.val + 1) + natBit z.val (i.val + 1) := by rw [hbi]
        _ = (natBit w.val (i.val + 1) + natBit w.val (i.val + 1)) +
              (natBit z.val (i.val + 1) + natBit z.val (i.val + 1)) +
              borrowBit (i.val + 1) (w.val % 2 ^ s) (z.val % 2 ^ s) := by ring
        _ = borrowBit (i.val + 1) (w.val % 2 ^ s) (z.val % 2 ^ s) := by
              rw [zmod2_add_self, zmod2_add_self, add_zero, zero_add]
  · rintro ⟨hx0, hcore⟩
    refine eq_of_natBit_eq huv_lt hd_lt fun j hj => ?_
    cases j with
    | zero =>
      simp only [mCoordEquiv, Equiv.ofBijective_apply] at hx0
      have hmod0 : (u.val ^^^ w.val) % 2 = (v.val ^^^ z.val) % 2 := congrArg Fin.val hx0
      have hxwyz : natBit (u.val ^^^ w.val) 0 = natBit (v.val ^^^ z.val) 0 := by
        simp only [natBit, pow_zero, Nat.div_one]
        exact (ZMod.natCast_eq_natCast_iff' _ _ 2).mpr hmod0
      rw [natBit_xor, natBit_xor] at hxwyz
      rw [natBit_xor, hd_bit0]
      calc natBit u.val 0 + natBit v.val 0
          = (natBit u.val 0 + natBit w.val 0) + natBit w.val 0 + natBit v.val 0 := by
              rw [add_assoc (natBit u.val 0), zmod2_add_self, add_zero]
        _ = (natBit v.val 0 + natBit z.val 0) + natBit w.val 0 + natBit v.val 0 := by rw [hxwyz]
        _ = (natBit v.val 0 + natBit v.val 0) + natBit w.val 0 + natBit z.val 0 := by ring
        _ = natBit w.val 0 + natBit z.val 0 := by rw [zmod2_add_self, zero_add]
    | succ j' =>
      let i : Fin s := ⟨j', by omega⟩
      simp only [mCoordEquiv, Equiv.ofBijective_apply, K_coreRel] at hcore
      have hi := congr_fun hcore i
      dsimp only [Pi.add_apply, borrowVec, i] at hi
      rw [natBit_xor, natBit_xor] at hi
      rw [natBit_xor, hd_bits i]
      dsimp only [i]
      calc natBit u.val (j' + 1) + natBit v.val (j' + 1)
          = ((natBit u.val (j' + 1) + natBit w.val (j' + 1)) +
              (natBit v.val (j' + 1) + natBit z.val (j' + 1))) +
              natBit w.val (j' + 1) + natBit z.val (j' + 1) := by
                have hw2 := zmod2_add_self (natBit w.val (j' + 1))
                have hz2 := zmod2_add_self (natBit z.val (j' + 1))
                calc natBit u.val (j' + 1) + natBit v.val (j' + 1)
                    = natBit u.val (j' + 1) + natBit v.val (j' + 1) +
                        (natBit w.val (j' + 1) + natBit w.val (j' + 1)) +
                        (natBit z.val (j' + 1) + natBit z.val (j' + 1)) := by
                          rw [hw2, hz2, add_zero, add_zero]
                  _ = _ := by ring
        _ = borrowBit (j' + 1) (w.val % 2 ^ s) (z.val % 2 ^ s) +
              natBit w.val (j' + 1) + natBit z.val (j' + 1) := by rw [hi]
        _ = natBit w.val (j' + 1) + natBit z.val (j' + 1) +
              borrowBit (j' + 1) (w.val % 2 ^ s) (z.val % 2 ^ s) := by ring

private lemma M_mat_reindex_eq_kronecker (R : Type*) [CommRing R] (s : ℕ) :
    (M_mat R (s + 1)).reindex (mCoordEquiv s) (mCoordEquiv s) =
      Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) R)
        (Matrix.kroneckerMap (· * ·) (K_coreMat R s) (allOnesMat R 2)) := by
  ext r c
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, allOnesMat, mul_one, M_mat, K_coreMat]
  have hiff := M_rel_iff_mCoordEquiv s ((mCoordEquiv s).symm r) ((mCoordEquiv s).symm c)
  simp only [Equiv.apply_symm_apply] at hiff
  by_cases h1 : r.1 = c.1
  · by_cases h2 : K_coreRel s r.2.1 c.2.1
    · have hm : M_rel (s + 1) ((mCoordEquiv s).symm r) ((mCoordEquiv s).symm c) :=
        hiff.mpr ⟨h1, h2⟩
      simp [h1, h2, hm]
    · have hm : ¬ M_rel (s + 1) ((mCoordEquiv s).symm r) ((mCoordEquiv s).symm c) :=
        fun h => h2 (hiff.mp h).2
      simp [h1, h2, hm]
  · have hm : ¬ M_rel (s + 1) ((mCoordEquiv s).symm r) ((mCoordEquiv s).symm c) :=
      fun h => h1 (hiff.mp h).1
    simp [h1, hm]

/-- **Theorem 4.1(b), Exact Rational Rank of `M_t`**:
`3 * rank_ℚ(M_{s+1}) = 4^{s+1} + 2`, i.e., `rank(M_t) = (4^t + 2) / 3` (Paper 2, eq. (4.5)). -/
theorem rank_M_mat_Q (s : ℕ) :
    3 * (M_mat ℚ (s + 1)).rank = 4 ^ (s + 1) + 2 := by
  have hrk : (M_mat ℚ (s + 1)).rank = 2 * (K_coreMat ℚ s).rank := by
    rw [← Matrix.rank_reindex (mCoordEquiv s) (mCoordEquiv s), M_mat_reindex_eq_kronecker ℚ s,
      rank_kronecker_field, rank_kronecker_field, Matrix.rank_one, Fintype.card_fin,
      rank_allOnesMat (by decide), mul_one]
  have hK := rank_K_coreMat_Q s
  rw [hrk, pow_succ 4 s]
  linarith

/-- Exact complex rank of `M_t`: `3 * rank_ℂ(M_{s+1}) = 4^{s+1} + 2`. -/
theorem rank_M_mat_C (s : ℕ) :
    3 * (M_mat ℂ (s + 1)).rank = 4 ^ (s + 1) + 2 := by
  have hrk : (M_mat ℂ (s + 1)).rank = 2 * (K_coreMat ℂ s).rank := by
    rw [← Matrix.rank_reindex (mCoordEquiv s) (mCoordEquiv s), M_mat_reindex_eq_kronecker ℂ s,
      rank_kronecker_field, rank_kronecker_field, Matrix.rank_one, Fintype.card_fin,
      rank_allOnesMat (by decide), mul_one]
  have hK := rank_K_coreMat_C s
  rw [hrk, pow_succ 4 s]
  linarith

/-! ### 4. Sharp Spectral Envelope, Equality Criterion, and Centered Spectral Norm (Theorem 4.1(c)) -/

/-- `‖1 + exp(i θ)‖ = 2 |cos(θ / 2)|`. -/
theorem norm_one_add_exp_mul_I (θ : ℝ) :
    ‖1 + Complex.exp ((θ : ℂ) * Complex.I)‖ = 2 * |Real.cos (θ / 2)| := by
  have hfac :
      1 + Complex.exp ((θ : ℂ) * Complex.I) =
        Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) *
          ((2 * Real.cos (θ / 2) : ℝ) : ℂ) := by
    have hsum :
        Complex.exp (((-(θ / 2) : ℝ) : ℂ) * Complex.I) +
            Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) =
          ((2 * Real.cos (θ / 2) : ℝ) : ℂ) := by
      rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
      push_cast
      ring
    calc 1 + Complex.exp ((θ : ℂ) * Complex.I)
        = Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) *
            Complex.exp (((-(θ / 2) : ℝ) : ℂ) * Complex.I) +
          Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) *
            Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) := by
              rw [← Complex.exp_add, ← Complex.exp_add]
              have h0 : (((θ / 2 : ℝ) : ℂ) * Complex.I + ((-(θ / 2) : ℝ) : ℂ) * Complex.I) = 0 := by
                push_cast; ring
              have h1 : (((θ / 2 : ℝ) : ℂ) * Complex.I + ((θ / 2 : ℝ) : ℂ) * Complex.I) =
                  (θ : ℂ) * Complex.I := by
                push_cast; ring
              rw [h0, h1, Complex.exp_zero]
      _ = Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) *
            (Complex.exp (((-(θ / 2) : ℝ) : ℂ) * Complex.I) +
              Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I)) := by ring
      _ = Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) *
            ((2 * Real.cos (θ / 2) : ℝ) : ℂ) := by rw [hsum]
  rw [hfac, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2)]

/-- `‖1 - exp(i θ)‖ = 2 |sin(θ / 2)|`. -/
theorem norm_one_sub_exp_mul_I (θ : ℝ) :
    ‖1 - Complex.exp ((θ : ℂ) * Complex.I)‖ = 2 * |Real.sin (θ / 2)| := by
  have hfac :
      1 - Complex.exp ((θ : ℂ) * Complex.I) =
        Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) *
          (-(((2 * Real.sin (θ / 2) : ℝ) : ℂ) * Complex.I)) := by
    have hdiff :
        Complex.exp (((-(θ / 2) : ℝ) : ℂ) * Complex.I) -
            Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) =
          -(((2 * Real.sin (θ / 2) : ℝ) : ℂ) * Complex.I) := by
      rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
      push_cast
      ring
    calc 1 - Complex.exp ((θ : ℂ) * Complex.I)
        = Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) *
            Complex.exp (((-(θ / 2) : ℝ) : ℂ) * Complex.I) -
          Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) *
            Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) := by
              rw [← Complex.exp_add, ← Complex.exp_add]
              have h0 : (((θ / 2 : ℝ) : ℂ) * Complex.I + ((-(θ / 2) : ℝ) : ℂ) * Complex.I) = 0 := by
                push_cast; ring
              have h1 : (((θ / 2 : ℝ) : ℂ) * Complex.I + ((θ / 2 : ℝ) : ℂ) * Complex.I) =
                  (θ : ℂ) * Complex.I := by
                push_cast; ring
              rw [h0, h1, Complex.exp_zero]
      _ = Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) *
            (Complex.exp (((-(θ / 2) : ℝ) : ℂ) * Complex.I) -
              Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I)) := by ring
      _ = Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) *
            (-(((2 * Real.sin (θ / 2) : ℝ) : ℂ) * Complex.I)) := by rw [hdiff]
  rw [hfac, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_neg, norm_mul,
    Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 2)]

/-- Combined trigonometric factor identity `‖1 + (-1)^b exp(i θ)‖ = 2|cos(θ/2)|` or `2|sin(θ/2)|`. -/
theorem norm_one_add_sign_exp_mul_I (b : ZMod 2) (θ : ℝ) :
    ‖1 + ((-1 : ℂ) ^ b.val) * Complex.exp ((θ : ℂ) * Complex.I)‖ =
      if b = 0 then 2 * |Real.cos (θ / 2)| else 2 * |Real.sin (θ / 2)| := by
  rcases zmod2_eq_zero_or_one b with rfl | rfl
  · simp [norm_one_add_exp_mul_I]
  · simp [sub_eq_add_neg, ← norm_one_sub_exp_mul_I]

/-- Exact telescoping product `|sin θ| * ∏_{j=0}^{r-1} (2 |cos(2^j θ)|) = |sin(2^r θ)|`. -/
theorem abs_sin_mul_prod_two_abs_cos (r : ℕ) (θ : ℝ) :
    |Real.sin θ| * (∏ j ∈ Finset.range r, (2 * |Real.cos ((2 : ℝ) ^ j * θ)|)) =
      |Real.sin ((2 : ℝ) ^ r * θ)| := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ih]
    have h2 : (2 : ℝ) ^ (r + 1) * θ = 2 * ((2 : ℝ) ^ r * θ) := by
      rw [pow_succ]; ring
    rw [h2, Real.sin_two_mul, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2)]
    ring

/-- Telescoping division form `∏_{j=0}^{r-1} (2 |cos(2^j θ)|) = |sin(2^r θ)| / |sin θ|`. -/
theorem prod_two_abs_cos_eq_div {θ : ℝ} (r : ℕ) (hsin : Real.sin θ ≠ 0) :
    (∏ j ∈ Finset.range r, (2 * |Real.cos ((2 : ℝ) ^ j * θ)|)) =
      |Real.sin ((2 : ℝ) ^ r * θ)| / |Real.sin θ| := by
  have habs : |Real.sin θ| ≠ 0 := abs_ne_zero.mpr hsin
  rw [eq_div_iff habs, mul_comm]
  exact abs_sin_mul_prod_two_abs_cos r θ

/-- Dyadic specialization `∏_{j=0}^{r-1} (2 cos(π / 2^{r - j + 1})) = 1 / sin(π / 2^{r+1})`. -/
theorem prod_two_cos_pi_div_two_pow (r : ℕ) :
    (∏ j ∈ Finset.range r, (2 * Real.cos (Real.pi / (2 : ℝ) ^ (r - j + 1)))) =
      1 / Real.sin (Real.pi / (2 : ℝ) ^ (r + 1)) := by
  set θ := Real.pi / (2 : ℝ) ^ (r + 1)
  have hpow_gt1 : (1 : ℝ) < (2 : ℝ) ^ (r + 1) := by
    calc (1 : ℝ) < 2 := by norm_num
      _ = (2 : ℝ) ^ 1 := by ring
      _ ≤ (2 : ℝ) ^ (r + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hθ_pos : 0 < θ := div_pos Real.pi_pos (by positivity)
  have hθ_lt_pi : θ < Real.pi := div_lt_self Real.pi_pos hpow_gt1
  have hsin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ_pos hθ_lt_pi
  have htop : (2 : ℝ) ^ r * θ = Real.pi / 2 := by
    dsimp only [θ]
    rw [pow_succ]
    have h2r : (2 : ℝ) ^ r ≠ 0 := by positivity
    field_simp [h2r]
  have hcongr :
      (∏ j ∈ Finset.range r, (2 * Real.cos (Real.pi / (2 : ℝ) ^ (r - j + 1)))) =
        ∏ j ∈ Finset.range r, (2 * |Real.cos ((2 : ℝ) ^ j * θ)|) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    have hjlt : j < r := Finset.mem_range.mp hj
    have hexp : (2 : ℝ) ^ j * θ = Real.pi / (2 : ℝ) ^ (r - j + 1) := by
      dsimp only [θ]
      have hsplit : (2 : ℝ) ^ (r + 1) = (2 : ℝ) ^ j * (2 : ℝ) ^ (r - j + 1) := by
        rw [← pow_add]; congr 1; omega
      rw [hsplit]
      have hne1 : (2 : ℝ) ^ j ≠ 0 := by positivity
      have hne2 : (2 : ℝ) ^ (r - j + 1) ≠ 0 := by positivity
      field_simp [hne1, hne2]
    rw [hexp]
    have hge4 : (4 : ℝ) ≤ (2 : ℝ) ^ (r - j + 1) := by
      calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
        _ ≤ (2 : ℝ) ^ (r - j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hang_pos : 0 < Real.pi / (2 : ℝ) ^ (r - j + 1) :=
      div_pos Real.pi_pos (by positivity)
    have hang_lt : Real.pi / (2 : ℝ) ^ (r - j + 1) < Real.pi / 2 := by
      have hpi : 0 < Real.pi := Real.pi_pos
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have hcos_pos : 0 < Real.cos (Real.pi / (2 : ℝ) ^ (r - j + 1)) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hang_lt⟩
    rw [abs_of_pos hcos_pos]
  rw [hcongr, prod_two_abs_cos_eq_div r hsin_pos.ne', htop, Real.sin_pi_div_two,
    abs_one, abs_of_pos hsin_pos]

private lemma abs_cos_add_nat_mul_pi (x : ℝ) (q : ℕ) :
    |Real.cos (x + (q : ℝ) * Real.pi)| = |Real.cos x| := by
  induction q with
  | zero => simp
  | succ q ih =>
    have heq : x + ((q + 1 : ℕ) : ℝ) * Real.pi = (x + (q : ℝ) * Real.pi) + Real.pi := by
      push_cast; ring
    rw [heq, Real.cos_add_pi, abs_neg, ih]

/-- Sharp cosine bound for odd numerators `k`:
`|cos(k π / 2^{m+1})| ≤ cos(π / 2^{m+1})` (`m ≥ 1`, `k` odd), with equality iff
`k mod 2^{m+1} ∈ {1, 2^{m+1} - 1}`. -/
theorem abs_cos_odd_mul_pi_div_two_pow_le_and_eq_iff {m k : ℕ} (hm : 1 ≤ m) (hodd : k % 2 = 1) :
    |Real.cos ((k : ℝ) * Real.pi / (2 : ℝ) ^ (m + 1))| ≤
        Real.cos (Real.pi / (2 : ℝ) ^ (m + 1)) ∧
      (|Real.cos ((k : ℝ) * Real.pi / (2 : ℝ) ^ (m + 1))| =
          Real.cos (Real.pi / (2 : ℝ) ^ (m + 1)) ↔
        k % 2 ^ (m + 1) = 1 ∨ k % 2 ^ (m + 1) = 2 ^ (m + 1) - 1) := by
  set M := 2 ^ (m + 1)
  have hM_pos : 0 < M := by positivity
  have hM_R_ne : (M : ℝ) ≠ 0 := by exact_mod_cast hM_pos.ne'
  have hM_eq : M = 2 ^ m * 2 := by dsimp [M]; rw [pow_succ]
  have h2m_ge2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by ring
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hm
  set rem := k % M
  set q := k / M
  have hk_dm : k = M * q + rem := (Nat.div_add_mod k M).symm
  have hrem_lt : rem < M := Nat.mod_lt k hM_pos
  have hrem_odd : rem % 2 = 1 := by
    have hdvd2 : 2 ∣ M := ⟨2 ^ m, by omega⟩
    have hmod2 : k % 2 = rem % 2 := by
      conv_lhs => rw [hk_dm]
      obtain ⟨t, ht⟩ := hdvd2
      have hmq : M * q + rem = 2 * (t * q) + rem := by rw [ht]; ring
      rw [hmq, Nat.mul_add_mod_self_left]
    omega
  have hrem_ge1 : 1 ≤ rem := by omega
  have hrem_ne_half : rem ≠ 2 ^ m := by
    intro heq
    have heven : (2 ^ m) % 2 = 0 := by
      obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      rw [pow_succ]
      omega
    omega
  have hper :
      |Real.cos ((k : ℝ) * Real.pi / (2 : ℝ) ^ (m + 1))| =
        |Real.cos ((rem : ℝ) * Real.pi / (M : ℝ))| := by
    have hcastM : ((2 : ℝ) ^ (m + 1)) = (M : ℝ) := by dsimp [M]; push_cast; rfl
    have hsplit : (k : ℝ) * Real.pi / (M : ℝ) =
        (rem : ℝ) * Real.pi / (M : ℝ) + (q : ℝ) * Real.pi := by
      have hkR : (k : ℝ) = (M : ℝ) * (q : ℝ) + (rem : ℝ) := by exact_mod_cast hk_dm
      rw [hkR]
      field_simp [hM_R_ne]
      ring
    rw [hcastM, hsplit, abs_cos_add_nat_mul_pi]
  have hcastM : ((2 : ℝ) ^ (m + 1)) = (M : ℝ) := by dsimp [M]; push_cast; rfl
  rw [hper, hcastM]
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hM_R_ge4 : (4 : ℝ) ≤ (M : ℝ) := by
    have h4 : 4 ≤ M := by omega
    exact_mod_cast h4
  have hbase_mem : Real.pi / (M : ℝ) ∈ Set.Icc 0 Real.pi := by
    refine ⟨by positivity, ?_⟩
    exact le_of_lt (div_lt_self hpi_pos (by linarith))
  by_cases hlt_half : rem < 2 ^ m
  · have hrem_R_lt : (rem : ℝ) * Real.pi / (M : ℝ) < Real.pi / 2 := by
      have hlt2 : 2 * rem < M := by omega
      have hlt2R : 2 * (rem : ℝ) < (M : ℝ) := by exact_mod_cast hlt2
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have hrem_pos : 0 < (rem : ℝ) * Real.pi / (M : ℝ) := by
      have hrp : (0 : ℝ) < (rem : ℝ) := by exact_mod_cast hrem_ge1
      positivity
    have hcos_pos : 0 < Real.cos ((rem : ℝ) * Real.pi / (M : ℝ)) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith, hrem_R_lt⟩
    rw [abs_of_pos hcos_pos]
    have hrem_mem : (rem : ℝ) * Real.pi / (M : ℝ) ∈ Set.Icc 0 Real.pi :=
      ⟨hrem_pos.le, by linarith⟩
    have hge_base : Real.pi / (M : ℝ) ≤ (rem : ℝ) * Real.pi / (M : ℝ) := by
      have hr1 : (1 : ℝ) ≤ (rem : ℝ) := by exact_mod_cast hrem_ge1
      rw [div_le_div_iff_of_pos_right (by positivity)]
      nlinarith
    have hle : Real.cos ((rem : ℝ) * Real.pi / (M : ℝ)) ≤ Real.cos (Real.pi / (M : ℝ)) :=
      Real.strictAntiOn_cos.antitoneOn hbase_mem hrem_mem hge_base
    refine ⟨hle, ?_⟩
    constructor
    · intro heq
      have hinj := Real.strictAntiOn_cos.injOn hrem_mem hbase_mem heq
      field_simp [hM_R_ne, hpi_pos.ne'] at hinj
      left
      exact_mod_cast hinj
    · rintro (h1 | htop)
      · change rem = 1 at h1
        rw [h1, Nat.cast_one, one_mul]
      · change rem = M - 1 at htop
        omega
  · have hgt_half : 2 ^ m < rem := by omega
    set rem' := M - rem
    have hrem'_ge1 : 1 ≤ rem' := by omega
    have hrem'_lt : rem' < 2 ^ m := by omega
    have hsub_angle : (rem : ℝ) * Real.pi / (M : ℝ) =
        Real.pi - (rem' : ℝ) * Real.pi / (M : ℝ) := by
      have hsumR : (rem : ℝ) + (rem' : ℝ) = (M : ℝ) := by
        have hsumN : rem + rem' = M := by omega
        exact_mod_cast hsumN
      field_simp [hM_R_ne]
      nlinarith
    have hrem'_R_lt : (rem' : ℝ) * Real.pi / (M : ℝ) < Real.pi / 2 := by
      have hlt2 : 2 * rem' < M := by omega
      have hlt2R : 2 * (rem' : ℝ) < (M : ℝ) := by exact_mod_cast hlt2
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have hrem'_pos : 0 < (rem' : ℝ) * Real.pi / (M : ℝ) := by
      have hrp : (0 : ℝ) < (rem' : ℝ) := by exact_mod_cast hrem'_ge1
      positivity
    have hcos_pos' : 0 < Real.cos ((rem' : ℝ) * Real.pi / (M : ℝ)) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith, hrem'_R_lt⟩
    rw [hsub_angle, Real.cos_pi_sub, abs_neg, abs_of_pos hcos_pos']
    have hrem'_mem : (rem' : ℝ) * Real.pi / (M : ℝ) ∈ Set.Icc 0 Real.pi :=
      ⟨hrem'_pos.le, by linarith⟩
    have hge_base' : Real.pi / (M : ℝ) ≤ (rem' : ℝ) * Real.pi / (M : ℝ) := by
      have hr1 : (1 : ℝ) ≤ (rem' : ℝ) := by exact_mod_cast hrem'_ge1
      rw [div_le_div_iff_of_pos_right (by positivity)]
      nlinarith
    have hle' : Real.cos ((rem' : ℝ) * Real.pi / (M : ℝ)) ≤ Real.cos (Real.pi / (M : ℝ)) :=
      Real.strictAntiOn_cos.antitoneOn hbase_mem hrem'_mem hge_base'
    refine ⟨hle', ?_⟩
    constructor
    · intro heq
      have hinj := Real.strictAntiOn_cos.injOn hrem'_mem hbase_mem heq
      field_simp [hM_R_ne, hpi_pos.ne'] at hinj
      have hrem'1 : rem' = 1 := by exact_mod_cast hinj
      right
      omega
    · rintro (h1 | htop)
      · change rem = 1 at h1
        omega
      · change rem = M - 1 at htop
        have hrem'1 : rem' = 1 := by omega
        rw [hrem'1, Nat.cast_one, one_mul]

private lemma factor_norm_eq_two_abs_cos {s r j : ℕ} (hjr : j < r) (α : Fin s → ZMod 2)
    (ℓ : Fin (2 ^ r)) :
    ‖1 + ((-1 : ℂ) ^ (alphaCoeff s α j).val) * (zetaNeg r ℓ) ^ (2 ^ j)‖ =
      2 * |Real.cos (((2 * ℓ.val + 1 + (alphaCoeff s α j).val * 2 ^ (r - j) : ℕ) : ℝ) *
        Real.pi / (2 : ℝ) ^ (r - j + 1))| := by
  set m := r - j
  set b := alphaCoeff s α j
  have hm : 1 ≤ m := by omega
  have hzeta_pow :
      (zetaNeg r ℓ) ^ (2 ^ j) =
        Complex.exp (((((2 * ℓ.val + 1 : ℕ) : ℝ) * Real.pi / (2 : ℝ) ^ m : ℝ) : ℂ) * Complex.I) := by
    rw [zetaNeg_eq_div, ← Complex.exp_nat_mul]
    congr 1
    have hsplit : (2 : ℂ) ^ r = (2 : ℂ) ^ j * (2 : ℂ) ^ m := by
      rw [← pow_add]; congr 1; omega
    have hne1 : (2 : ℂ) ^ j ≠ 0 := pow_ne_zero j (by norm_num)
    have hne2 : (2 : ℂ) ^ m ≠ 0 := pow_ne_zero m (by norm_num)
    rw [hsplit]
    push_cast
    field_simp [hne1, hne2]
  have hsgn_exp :
      ((-1 : ℂ) ^ b.val) * (zetaNeg r ℓ) ^ (2 ^ j) =
        Complex.exp (((((2 * ℓ.val + 1 + b.val * 2 ^ m : ℕ) : ℝ) *
          Real.pi / (2 : ℝ) ^ m : ℝ) : ℂ) * Complex.I) := by
    rw [hzeta_pow]
    have hne_m : (2 : ℂ) ^ m ≠ 0 := pow_ne_zero m (by norm_num)
    rcases zmod2_eq_zero_or_one b with hb0 | hb1
    · rw [hb0]; simp
    · rw [hb1, zmod2_val_one, pow_one, ← Complex.exp_pi_mul_I, ← Complex.exp_add]
      congr 1
      push_cast
      field_simp [hne_m]
      ring
  rw [hsgn_exp, norm_one_add_exp_mul_I, div_div, ← pow_succ]

private lemma factor_norm_le_and_eq_iff {s r j : ℕ} (hjr : j < r) (α : Fin s → ZMod 2)
    (ℓ : Fin (2 ^ r)) :
    ‖1 + ((-1 : ℂ) ^ (alphaCoeff s α j).val) * (zetaNeg r ℓ) ^ (2 ^ j)‖ ≤
        2 * Real.cos (Real.pi / (2 : ℝ) ^ (r - j + 1)) ∧
      (‖1 + ((-1 : ℂ) ^ (alphaCoeff s α j).val) * (zetaNeg r ℓ) ^ (2 ^ j)‖ =
          2 * Real.cos (Real.pi / (2 : ℝ) ^ (r - j + 1)) ↔
        (2 * ℓ.val + 1 + (alphaCoeff s α j).val * 2 ^ (r - j)) % 2 ^ (r - j + 1) = 1 ∨
          (2 * ℓ.val + 1 + (alphaCoeff s α j).val * 2 ^ (r - j)) % 2 ^ (r - j + 1) =
            2 ^ (r - j + 1) - 1) := by
  rw [factor_norm_eq_two_abs_cos hjr α ℓ]
  have hm : 1 ≤ r - j := by omega
  have heven : ((alphaCoeff s α j).val * 2 ^ (r - j)) % 2 = 0 := by
    obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r - j ≠ 0)
    have hmul2 : (alphaCoeff s α j).val * 2 ^ (r - j) = 2 * ((alphaCoeff s α j).val * 2 ^ m') := by
      rw [hm', pow_succ]; ring
    rw [hmul2, Nat.mul_mod_right]
  have hodd : (2 * ℓ.val + 1 + (alphaCoeff s α j).val * 2 ^ (r - j)) % 2 = 1 := by omega
  obtain ⟨hle, heq_iff⟩ := abs_cos_odd_mul_pi_div_two_pow_le_and_eq_iff hm hodd
  refine ⟨by linarith, ?_⟩
  constructor
  · intro hmul
    exact heq_iff.mp (by linarith)
  · intro hmod
    rw [heq_iff.mpr hmod]

private lemma finset_prod_le_prod {ι : Type*} (S : Finset ι) {f g : ι → ℝ}
    (hf : ∀ i ∈ S, 0 ≤ f i) (hle : ∀ i ∈ S, f i ≤ g i) :
    (∏ i ∈ S, f i) ≤ ∏ i ∈ S, g i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hfa0 : 0 ≤ f a := hf a (Finset.mem_insert_self a S)
    have hfa_le : f a ≤ g a := hle a (Finset.mem_insert_self a S)
    have hfS0 : 0 ≤ ∏ i ∈ S, f i :=
      Finset.prod_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hS_le : (∏ i ∈ S, f i) ≤ ∏ i ∈ S, g i :=
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        (fun i hi => hle i (Finset.mem_insert_of_mem hi))
    calc f a * (∏ i ∈ S, f i)
        ≤ g a * (∏ i ∈ S, f i) := mul_le_mul_of_nonneg_right hfa_le hfS0
      _ ≤ g a * (∏ i ∈ S, g i) := mul_le_mul_of_nonneg_left hS_le (hfa0.trans hfa_le)

/-- **Theorem 4.1(c), Eigenvalue Envelope**:
`‖λ_ℓ‖ ≤ 1 / sin(π / 2^{r+1})` for all `r ≥ 1`, `α`, and `ℓ < 2^r`. -/
theorem norm_lambdaAlpha_le {s r : ℕ} (_hr1 : 1 ≤ r) (α : Fin s → ZMod 2) (ℓ : Fin (2 ^ r)) :
    ‖lambdaAlpha s r α ℓ‖ ≤ 1 / Real.sin (Real.pi / (2 : ℝ) ^ (r + 1)) := by
  rw [lambdaAlpha, norm_prod, ← prod_two_cos_pi_div_two_pow r]
  refine finset_prod_le_prod (Finset.range r) (fun j _ => norm_nonneg _) fun j hj => ?_
  exact (factor_norm_le_and_eq_iff (Finset.mem_range.mp hj) α ℓ).1

/-- Pointwise singular-value envelope `σ_ℓ(H_α) ≤ 2^{s - r} / sin(π / 2^{r+1})`. -/
theorem sigmaHAlpha_le_envelope {s r : ℕ} (hr1 : 1 ≤ r) (α : Fin s → ZMod 2) (ℓ : Fin (2 ^ r)) :
    sigmaHAlpha s r α ℓ ≤ (2 : ℝ) ^ (s - r) / Real.sin (Real.pi / (2 : ℝ) ^ (r + 1)) := by
  unfold sigmaHAlpha
  have h := norm_lambdaAlpha_le hr1 α ℓ
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (s - r) := by positivity
  calc (2 : ℝ) ^ (s - r) * ‖lambdaAlpha s r α ℓ‖
      ≤ (2 : ℝ) ^ (s - r) * (1 / Real.sin (Real.pi / (2 : ℝ) ^ (r + 1))) :=
        mul_le_mul_of_nonneg_left h h2
    _ = (2 : ℝ) ^ (s - r) / Real.sin (Real.pi / (2 : ℝ) ^ (r + 1)) := by ring

private lemma prod_eq_prod_iff_of_pos_of_le {ι : Type*} (S : Finset ι) {f g : ι → ℝ}
    (hf : ∀ i ∈ S, 0 < f i) (hle : ∀ i ∈ S, f i ≤ g i) :
    (∏ i ∈ S, f i) = (∏ i ∈ S, g i) ↔ ∀ i ∈ S, f i = g i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    have hfa_pos : 0 < f a := hf a (Finset.mem_insert_self a S)
    have hfa_le : f a ≤ g a := hle a (Finset.mem_insert_self a S)
    have hga_pos : 0 < g a := lt_of_lt_of_le hfa_pos hfa_le
    have hfS_pos : 0 < ∏ i ∈ S, f i :=
      Finset.prod_pos fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hprod_le : (∏ i ∈ S, f i) ≤ ∏ i ∈ S, g i :=
      finset_prod_le_prod S (fun i hi => (hf i (Finset.mem_insert_of_mem hi)).le)
        (fun i hi => hle i (Finset.mem_insert_of_mem hi))
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    constructor
    · intro heq
      have h1 : f a = g a := by
        by_contra hne
        have hlt : f a < g a := lt_of_le_of_ne hfa_le hne
        have hlt1 : f a * (∏ i ∈ S, f i) < g a * (∏ i ∈ S, f i) :=
          mul_lt_mul_of_pos_right hlt hfS_pos
        have hle2 : g a * (∏ i ∈ S, f i) ≤ g a * (∏ i ∈ S, g i) :=
          mul_le_mul_of_nonneg_left hprod_le hga_pos.le
        linarith
      have h2 : (∏ i ∈ S, f i) = ∏ i ∈ S, g i := by
        rw [h1] at heq
        exact mul_left_cancel₀ hga_pos.ne' heq
      have hallS := (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        (fun i hi => hle i (Finset.mem_insert_of_mem hi))).mp h2
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hiS
      · exact h1
      · exact hallS i hiS
    · intro hall
      rw [hall a (Finset.mem_insert_self a S),
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
          (fun i hi => hle i (Finset.mem_insert_of_mem hi))).mpr
          (fun i hi => hall i (Finset.mem_insert_of_mem hi))]

/-! #### Euclidean `ℓ₂` Vector Norm and `2 → 2` Matrix Spectral Norm -/

/-- Euclidean `ℓ₂` norm `‖x‖₂ = √(∑_i x_i²)` on `n → ℝ`. -/
noncomputable def l2Norm {n : Type*} [Fintype n] (x : n → ℝ) : ℝ :=
  Real.sqrt (∑ i : n, (x i) ^ 2)

/-- Spectral (`2 → 2` operator) norm `‖A‖₂ = sup_{‖x‖₂ ≤ 1} ‖A x‖₂` on `Matrix m n ℝ`. -/
noncomputable def spectralNorm2 {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : ℝ :=
  sSup { q : ℝ | ∃ x : n → ℝ, l2Norm x ≤ 1 ∧ q = l2Norm (A *ᵥ x) }

lemma l2Norm_nonneg {n : Type*} [Fintype n] (x : n → ℝ) : 0 ≤ l2Norm x :=
  Real.sqrt_nonneg _

@[simp]
lemma l2Norm_zero {n : Type*} [Fintype n] : l2Norm (0 : n → ℝ) = 0 := by
  simp [l2Norm]

lemma sq_l2Norm {n : Type*} [Fintype n] (x : n → ℝ) :
    (l2Norm x) ^ 2 = ∑ i : n, (x i) ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma sq_l2Norm_eq_dotProduct {n : Type*} [Fintype n] (x : n → ℝ) :
    (l2Norm x) ^ 2 = dotProduct x x := by
  rw [sq_l2Norm]
  simp [dotProduct, sq]

lemma l2Norm_smul {n : Type*} [Fintype n] (c : ℝ) (x : n → ℝ) :
    l2Norm (c • x) = |c| * l2Norm x := by
  unfold l2Norm
  have hsum : (∑ i : n, (c * x i) ^ 2) = c ^ 2 * ∑ i : n, (x i) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  simp only [Pi.smul_apply, smul_eq_mul, hsum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

lemma abs_dotProduct_le_l2Norm_mul_l2Norm {n : Type*} [Fintype n] (x y : n → ℝ) :
    |dotProduct x y| ≤ l2Norm x * l2Norm y := by
  have hcs : (∑ i : n, x i * y i) ^ 2 ≤ (∑ i : n, (x i) ^ 2) * (∑ i : n, (y i) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  have hprod_nonneg : 0 ≤ l2Norm x * l2Norm y := mul_nonneg (l2Norm_nonneg x) (l2Norm_nonneg y)
  have hsq : |dotProduct x y| ^ 2 ≤ (l2Norm x * l2Norm y) ^ 2 := by
    rw [sq_abs, mul_pow, sq_l2Norm, sq_l2Norm]
    exact hcs
  nlinarith [abs_nonneg (dotProduct x y)]

private lemma bddAbove_spectralNorm2_set {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) :
    BddAbove { q : ℝ | ∃ x : n → ℝ, l2Norm x ≤ 1 ∧ q = l2Norm (A *ᵥ x) } := by
  refine ⟨Real.sqrt (∑ i : m, ∑ j : n, (A i j) ^ 2), ?_⟩
  rintro q ⟨x, hx1, rfl⟩
  have hx_sq : ∑ j : n, (x j) ^ 2 ≤ 1 := by
    have := sq_l2Norm x
    nlinarith [l2Norm_nonneg x]
  have hrow : ∀ i : m, ((A *ᵥ x) i) ^ 2 ≤ ∑ j : n, (A i j) ^ 2 := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    calc (∑ j : n, A i j * x j) ^ 2
        ≤ (∑ j : n, (A i j) ^ 2) * (∑ j : n, (x j) ^ 2) :=
          Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => A i j) x
      _ ≤ (∑ j : n, (A i j) ^ 2) * 1 :=
          mul_le_mul_of_nonneg_left hx_sq (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      _ = ∑ j : n, (A i j) ^ 2 := mul_one _
  unfold l2Norm
  exact Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => hrow i)

lemma spectralNorm2_nonneg {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) :
    0 ≤ spectralNorm2 A := by
  refine le_csSup (bddAbove_spectralNorm2_set A) ?_
  exact ⟨0, by simp, by simp⟩

lemma l2Norm_mulVec_le_spectralNorm2 {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (x : n → ℝ) :
    l2Norm (A *ᵥ x) ≤ spectralNorm2 A * l2Norm x := by
  by_cases hx0 : l2Norm x = 0
  · have hsum0 : ∑ i : n, (x i) ^ 2 = 0 := by rw [← sq_l2Norm, hx0, zero_pow (by decide)]
    have hx_zero : x = 0 := by
      funext i
      have hle : (x i) ^ 2 ≤ ∑ j : n, (x j) ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
      rw [hsum0] at hle
      exact sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg (x i)))
    subst hx_zero
    simp
  · have hx_pos : 0 < l2Norm x := lt_of_le_of_ne (l2Norm_nonneg x) (Ne.symm hx0)
    let x_u : n → ℝ := (l2Norm x)⁻¹ • x
    have hnorm_u : l2Norm x_u ≤ 1 := by
      rw [l2Norm_smul, abs_of_pos (inv_pos.mpr hx_pos), inv_mul_cancel₀ hx_pos.ne']
    have hmem : l2Norm (A *ᵥ x_u) ∈ { q : ℝ | ∃ y : n → ℝ, l2Norm y ≤ 1 ∧ q = l2Norm (A *ᵥ y) } :=
      ⟨x_u, hnorm_u, rfl⟩
    have hle_sup : l2Norm (A *ᵥ x_u) ≤ spectralNorm2 A :=
      le_csSup (bddAbove_spectralNorm2_set A) hmem
    have hscale : l2Norm (A *ᵥ x_u) = (l2Norm x)⁻¹ * l2Norm (A *ᵥ x) := by
      simp only [x_u, Matrix.mulVec_smul, l2Norm_smul, abs_of_pos (inv_pos.mpr hx_pos)]
    rw [hscale] at hle_sup
    rw [mul_comm]
    exact (inv_mul_le_iff₀ hx_pos).mp hle_sup

/-- Universal bilinear form bound `|⟨x, A y⟩| ≤ ‖A‖₂ ‖x‖₂ ‖y‖₂`. -/
theorem abs_dotProduct_mulVec_le_spectralNorm2 {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (x : m → ℝ) (y : n → ℝ) :
    |dotProduct x (A *ᵥ y)| ≤ spectralNorm2 A * l2Norm x * l2Norm y := by
  calc |dotProduct x (A *ᵥ y)|
      ≤ l2Norm x * l2Norm (A *ᵥ y) := abs_dotProduct_le_l2Norm_mul_l2Norm x (A *ᵥ y)
    _ ≤ l2Norm x * (spectralNorm2 A * l2Norm y) :=
        mul_le_mul_of_nonneg_left (l2Norm_mulVec_le_spectralNorm2 A y) (l2Norm_nonneg x)
    _ = spectralNorm2 A * l2Norm x * l2Norm y := by ring

lemma spectralNorm2_eq_of_le_and_witness {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (S : ℝ) (hS0 : 0 ≤ S)
    (hub : ∀ x : n → ℝ, l2Norm (A *ᵥ x) ≤ S * l2Norm x)
    (hwit : S = 0 ∨ ∃ x : n → ℝ, l2Norm x ≠ 0 ∧ l2Norm (A *ᵥ x) = S * l2Norm x) :
    spectralNorm2 A = S := by
  apply le_antisymm
  · refine csSup_le ⟨0, ⟨0, by simp, by simp⟩⟩ ?_
    rintro q ⟨x, hx1, rfl⟩
    calc l2Norm (A *ᵥ x) ≤ S * l2Norm x := hub x
      _ ≤ S * 1 := mul_le_mul_of_nonneg_left hx1 hS0
      _ = S := mul_one S
  · rcases hwit with rfl | ⟨x, hx_ne, hxeq⟩
    · exact spectralNorm2_nonneg A
    · have hx_pos : 0 < l2Norm x := lt_of_le_of_ne (l2Norm_nonneg x) (Ne.symm hx_ne)
      let x_u : n → ℝ := (l2Norm x)⁻¹ • x
      have hnorm_u : l2Norm x_u ≤ 1 := by
        rw [l2Norm_smul, abs_of_pos (inv_pos.mpr hx_pos), inv_mul_cancel₀ hx_pos.ne']
      have hAu : l2Norm (A *ᵥ x_u) = S := by
        rw [Matrix.mulVec_smul, l2Norm_smul, abs_of_pos (inv_pos.mpr hx_pos), hxeq]
        field_simp [hx_pos.ne']
      exact le_csSup (bddAbove_spectralNorm2_set A) ⟨x_u, hnorm_u, hAu.symm⟩

private lemma l2Norm_comp_equiv {k k₀ : Type*} [Fintype k] [Fintype k₀]
    (ek : k ≃ k₀) (v : k₀ → ℝ) :
    l2Norm (v ∘ ek) = l2Norm v := by
  unfold l2Norm
  congr 1
  exact Equiv.sum_comp ek (fun i => (v i) ^ 2)

lemma spectralNorm2_reindex {m m₀ n n₀ : Type*} [Fintype m] [Fintype m₀]
    [Fintype n] [Fintype n₀] (em : m ≃ m₀) (en : n ≃ n₀) (A : Matrix m n ℝ) :
    spectralNorm2 (A.reindex em en) = spectralNorm2 A := by
  unfold spectralNorm2
  congr 1
  ext q
  constructor
  · rintro ⟨x, hx1, rfl⟩
    refine ⟨x ∘ en, ?_, ?_⟩
    · rwa [l2Norm_comp_equiv en x]
    · have hmv : ((A.reindex em en) *ᵥ x) = (A *ᵥ (x ∘ en)) ∘ em.symm := by
        ext i₀
        simp only [Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply,
          Function.comp_apply]
        exact (Equiv.sum_comp en (fun j₀ : n₀ => A (em.symm i₀) (en.symm j₀) * x j₀)).symm.trans
          (Finset.sum_congr rfl fun j _ => by simp)
      rw [hmv, l2Norm_comp_equiv em.symm]
  · rintro ⟨y, hy1, rfl⟩
    refine ⟨y ∘ en.symm, ?_, ?_⟩
    · rwa [l2Norm_comp_equiv en.symm y]
    · have hmv : ((A.reindex em en) *ᵥ (y ∘ en.symm)) = (A *ᵥ y) ∘ em.symm := by
        ext i₀
        simp only [Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply,
          Function.comp_apply]
        exact (Equiv.sum_comp en
          (fun j₀ : n₀ => A (em.symm i₀) (en.symm j₀) * y (en.symm j₀))).symm.trans
          (Finset.sum_congr rfl fun j _ => by simp)
      rw [hmv, l2Norm_comp_equiv em.symm]

lemma spectralNorm2_orth_conj {n : Type*} [Fintype n] [DecidableEq n]
    {Q : Matrix n n ℝ} (hQt : Qᵀ = Q) (hQ2 : Q * Q = 1) (M : Matrix n n ℝ) :
    spectralNorm2 (Q * M * Q) = spectralNorm2 M := by
  have hl2_Q : ∀ v : n → ℝ, l2Norm (Q *ᵥ v) = l2Norm v := by
    intro v
    have hsq : (l2Norm (Q *ᵥ v)) ^ 2 = (l2Norm v) ^ 2 := by
      rw [sq_l2Norm_eq_dotProduct, sq_l2Norm_eq_dotProduct, Matrix.dotProduct_mulVec,
        Matrix.vecMul_mulVec, ← Matrix.mulVec_transpose, hQt, hQ2, Matrix.transpose_one,
        Matrix.one_mulVec]
    nlinarith [l2Norm_nonneg (Q *ᵥ v), l2Norm_nonneg v]
  unfold spectralNorm2
  congr 1
  ext q
  constructor
  · rintro ⟨x, hx1, rfl⟩
    refine ⟨Q *ᵥ x, by rwa [hl2_Q], ?_⟩
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hl2_Q]
  · rintro ⟨y, hy1, rfl⟩
    refine ⟨Q *ᵥ y, by rwa [hl2_Q], ?_⟩
    have hQQy : Q *ᵥ (Q *ᵥ y) = y := by rw [Matrix.mulVec_mulVec, hQ2, Matrix.one_mulVec]
    rw [← Matrix.mulVec_mulVec, hQQy, ← Matrix.mulVec_mulVec, hl2_Q]

private noncomputable def cNormSq {n : Type*} [Fintype n] (v : n → ℂ) : ℝ :=
  ∑ i : n, ‖v i‖ ^ 2

private lemma dotProduct_star_self_re {n : Type*} [Fintype n] (v : n → ℂ) :
    (dotProduct (star v) v).re = cNormSq v := by
  simp only [dotProduct, Pi.star_apply, cNormSq, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : star (v i) * v i = ((Complex.normSq (v i) : ℝ) : ℂ) := by
    simpa [Complex.star_def, mul_comm] using (Complex.normSq_eq_conj_mul_self (z := v i)).symm
  rw [h1, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

private lemma unitary_cNormSq_conjTranspose_mulVec {n : Type*} [Fintype n] [DecidableEq n]
    {V : Matrix n n ℂ} (hV2 : V * Vᴴ = 1) (v : n → ℂ) :
    cNormSq (Vᴴ *ᵥ v) = cNormSq v := by
  rw [← dotProduct_star_self_re, ← dotProduct_star_self_re]
  congr 1
  calc dotProduct (star (Vᴴ *ᵥ v)) (Vᴴ *ᵥ v)
      = dotProduct (star v ᵥ* V) (Vᴴ *ᵥ v) := by
          rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
    _ = dotProduct (star v) (V *ᵥ (Vᴴ *ᵥ v)) := by rw [← Matrix.dotProduct_mulVec]
    _ = dotProduct (star v) ((V * Vᴴ) *ᵥ v) := by rw [Matrix.mulVec_mulVec]
    _ = dotProduct (star v) v := by rw [hV2, Matrix.one_mulVec]

private lemma Htilde_alpha_sq_l2Norm_le {s r : ℕ} {α : Fin s → ZMod 2}
    (h : HasHighestBit s α r) (B : ℝ)
    (hB : ∀ ℓ : Fin (2 ^ r), ‖lambdaAlpha s r α ℓ‖ ≤ B)
    (x : Fin (2 ^ r) → ℝ) :
    (l2Norm (Htilde_alpha ℝ s r α *ᵥ x)) ^ 2 ≤ B ^ 2 * (l2Norm x) ^ 2 := by
  let xC : Fin (2 ^ r) → ℂ := fun w => (x w : ℂ)
  let y : Fin (2 ^ r) → ℂ := (V_Htilde s r α)ᴴ *ᵥ xC
  have hV2 := V_Htilde_mul_conjTranspose_self s r α
  have hxC_eq : xC = V_Htilde s r α *ᵥ y := by
    dsimp only [y]
    rw [Matrix.mulVec_mulVec, hV2, Matrix.one_mulVec]
  have hAx_cast :
      (Htilde_alpha ℂ s r α *ᵥ xC) = fun w => (((Htilde_alpha ℝ s r α *ᵥ x) w : ℝ) : ℂ) := by
    ext w
    simp only [Matrix.mulVec, dotProduct, xC, Htilde_alpha]
    push_cast
    rfl
  have hlhs : (l2Norm (Htilde_alpha ℝ s r α *ᵥ x)) ^ 2 =
      cNormSq (Htilde_alpha ℂ s r α *ᵥ xC) := by
    rw [sq_l2Norm, hAx_cast]
    simp [cNormSq, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hgram :
      dotProduct (star (Htilde_alpha ℂ s r α *ᵥ xC)) (Htilde_alpha ℂ s r α *ᵥ xC) =
        ∑ ℓ : Fin (2 ^ r),
          (((‖lambdaAlpha s r α ℓ‖ ^ 2 : ℝ) : ℂ)) * (star (y ℓ) * y ℓ) := by
    rw [hxC_eq]
    calc dotProduct (star (Htilde_alpha ℂ s r α *ᵥ (V_Htilde s r α *ᵥ y)))
            (Htilde_alpha ℂ s r α *ᵥ (V_Htilde s r α *ᵥ y))
        = dotProduct (star ((Htilde_alpha ℂ s r α * V_Htilde s r α) *ᵥ y))
            ((Htilde_alpha ℂ s r α * V_Htilde s r α) *ᵥ y) := by
              rw [Matrix.mulVec_mulVec]
      _ = dotProduct (star y ᵥ* (Htilde_alpha ℂ s r α * V_Htilde s r α)ᴴ)
            ((Htilde_alpha ℂ s r α * V_Htilde s r α) *ᵥ y) := by
              rw [Matrix.star_mulVec]
      _ = dotProduct (star y)
            (((V_Htilde s r α)ᴴ * ((Htilde_alpha ℂ s r α)ᴴ * Htilde_alpha ℂ s r α) *
              V_Htilde s r α) *ᵥ y) := by
              rw [← Matrix.dotProduct_mulVec, Matrix.conjTranspose_mul,
                Matrix.mulVec_mulVec]
              simp [Matrix.mul_assoc]
      _ = dotProduct (star y)
            (Matrix.diagonal (fun ℓ => ((‖lambdaAlpha s r α ℓ‖ ^ 2 : ℝ) : ℂ)) *ᵥ y) := by
              rw [V_Htilde_conj_gram h]
      _ = ∑ ℓ : Fin (2 ^ r),
            (((‖lambdaAlpha s r α ℓ‖ ^ 2 : ℝ) : ℂ)) * (star (y ℓ) * y ℓ) := by
              simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
              refine Finset.sum_congr rfl fun ℓ _ => by ring
  have hlhs_sum :
      (l2Norm (Htilde_alpha ℝ s r α *ᵥ x)) ^ 2 =
        ∑ ℓ : Fin (2 ^ r), ‖lambdaAlpha s r α ℓ‖ ^ 2 * ‖y ℓ‖ ^ 2 := by
    rw [hlhs, ← dotProduct_star_self_re, hgram, Complex.re_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    have hy_re : (star (y ℓ) * y ℓ) = ((‖y ℓ‖ ^ 2 : ℝ) : ℂ) := by
      simpa [Complex.star_def, mul_comm, Complex.normSq_eq_norm_sq] using
        (Complex.normSq_eq_conj_mul_self (z := y ℓ)).symm
    rw [hy_re, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hy_norm : (∑ ℓ : Fin (2 ^ r), ‖y ℓ‖ ^ 2) = (l2Norm x) ^ 2 := by
    change cNormSq y = (l2Norm x) ^ 2
    rw [unitary_cNormSq_conjTranspose_mulVec hV2 xC, sq_l2Norm]
    simp [cNormSq, xC, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hlhs_sum, ← hy_norm, Finset.mul_sum]
  refine Finset.sum_le_sum fun ℓ _ => ?_
  have hle_sq : ‖lambdaAlpha s r α ℓ‖ ^ 2 ≤ B ^ 2 := by
    have hl := hB ℓ
    have hnn := norm_nonneg (lambdaAlpha s r α ℓ)
    nlinarith
  exact mul_le_mul_of_nonneg_right hle_sq (sq_nonneg _)

private lemma Htilde_alpha_exists_real_witness {s r : ℕ} {α : Fin s → ZMod 2}
    (h : HasHighestBit s α r) (ℓ₀ : Fin (2 ^ r)) :
    ∃ u : Fin (2 ^ r) → ℝ,
      l2Norm u ≠ 0 ∧
        (l2Norm (Htilde_alpha ℝ s r α *ᵥ u)) ^ 2 =
          ‖lambdaAlpha s r α ℓ₀‖ ^ 2 * (l2Norm u) ^ 2 := by
  let A := Htilde_alpha ℝ s r α
  let AC := Htilde_alpha ℂ s r α
  let G := Aᵀ * A
  let GC := ACᴴ * AC
  let v : Fin (2 ^ r) → ℂ := fun w => V_Htilde s r α w ℓ₀
  have hGC_real : ∀ w z : Fin (2 ^ r), GC w z = ((G w z : ℝ) : ℂ) := by
    intro w z
    simp only [GC, G, AC, A, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.transpose_apply, Htilde_alpha]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    simp
  have hV_eig :
      GC * V_Htilde s r α =
        V_Htilde s r α * Matrix.diagonal (fun ℓ => ((‖lambdaAlpha s r α ℓ‖ ^ 2 : ℝ) : ℂ)) := by
    calc GC * V_Htilde s r α
        = (V_Htilde s r α * (V_Htilde s r α)ᴴ) * (GC * V_Htilde s r α) := by
            rw [V_Htilde_mul_conjTranspose_self, Matrix.one_mul]
      _ = V_Htilde s r α * ((V_Htilde s r α)ᴴ * GC * V_Htilde s r α) := by
            simp [Matrix.mul_assoc]
      _ = V_Htilde s r α * Matrix.diagonal (fun ℓ => ((‖lambdaAlpha s r α ℓ‖ ^ 2 : ℝ) : ℂ)) := by
            rw [V_Htilde_conj_gram h]
  have hv_eig : ∀ w : Fin (2 ^ r),
      (GC *ᵥ v) w = (((‖lambdaAlpha s r α ℓ₀‖ ^ 2 : ℝ) : ℂ)) * v w := by
    intro w
    have hentry := congr_fun (congr_fun hV_eig w) ℓ₀
    rw [Matrix.mul_diagonal] at hentry
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, v] at hentry ⊢
    exact hentry.trans (mul_comm _ _)
  let u_re : Fin (2 ^ r) → ℝ := fun z => (v z).re
  let u_im : Fin (2 ^ r) → ℝ := fun z => (v z).im
  have hre_eig : G *ᵥ u_re = (‖lambdaAlpha s r α ℓ₀‖ ^ 2) • u_re := by
    ext w
    have hw := congr_arg Complex.re (hv_eig w)
    simp only [Matrix.mulVec, dotProduct, hGC_real, Complex.re_sum, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Pi.smul_apply, smul_eq_mul,
      u_re] at hw ⊢
    exact hw
  have him_eig : G *ᵥ u_im = (‖lambdaAlpha s r α ℓ₀‖ ^ 2) • u_im := by
    ext w
    have hw := congr_arg Complex.im (hv_eig w)
    simp only [Matrix.mulVec, dotProduct, hGC_real, Complex.im_sum, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, Pi.smul_apply, smul_eq_mul,
      u_im] at hw ⊢
    exact hw
  have hv_unit : ∑ z : Fin (2 ^ r), ((u_re z) ^ 2 + (u_im z) ^ 2) = 1 := by
    have hdiag1 := congr_arg Complex.re
      (congr_fun (congr_fun (V_Htilde_conjTranspose_mul_self s r α) ℓ₀) ℓ₀)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, ↓reduceIte,
      Complex.one_re, Complex.re_sum] at hdiag1
    rw [← hdiag1]
    refine Finset.sum_congr rfl fun z _ => ?_
    dsimp only [u_re, u_im, v]
    have h1 : (star (V_Htilde s r α z ℓ₀) * V_Htilde s r α z ℓ₀).re =
        Complex.normSq (V_Htilde s r α z ℓ₀) := by
      have hc : star (V_Htilde s r α z ℓ₀) * V_Htilde s r α z ℓ₀ =
          ((Complex.normSq (V_Htilde s r α z ℓ₀) : ℝ) : ℂ) := by
        simpa [Complex.star_def, mul_comm] using
          (Complex.normSq_eq_conj_mul_self (z := V_Htilde s r α z ℓ₀)).symm
      rw [hc, Complex.ofReal_re]
    rw [h1, Complex.normSq_apply]
    ring
  have hor : (∑ z : Fin (2 ^ r), (u_re z) ^ 2 ≠ 0) ∨ (∑ z : Fin (2 ^ r), (u_im z) ^ 2 ≠ 0) := by
    by_contra hboth
    push Not at hboth
    rw [Finset.sum_add_distrib, hboth.1, hboth.2, add_zero] at hv_unit
    norm_num at hv_unit
  have quad_eq : ∀ u : Fin (2 ^ r) → ℝ,
      G *ᵥ u = (‖lambdaAlpha s r α ℓ₀‖ ^ 2) • u →
        (l2Norm (A *ᵥ u)) ^ 2 = ‖lambdaAlpha s r α ℓ₀‖ ^ 2 * (l2Norm u) ^ 2 := by
    intro u heig
    rw [sq_l2Norm_eq_dotProduct, sq_l2Norm_eq_dotProduct, Matrix.dotProduct_mulVec,
      ← Matrix.vecMul_transpose A u, Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec]
    change dotProduct u (G *ᵥ u) = _
    rw [heig, dotProduct_smul, smul_eq_mul]
  rcases hor with hre_ne | him_ne
  · refine ⟨u_re, ?_, quad_eq u_re hre_eig⟩
    intro h0
    rw [← sq_l2Norm, h0, zero_pow (by decide)] at hre_ne
    exact hre_ne rfl
  · refine ⟨u_im, ?_, quad_eq u_im him_eig⟩
    intro h0
    rw [← sq_l2Norm, h0, zero_pow (by decide)] at him_ne
    exact him_ne rfl

/-- Exact spectral norm `‖H_0‖₂ = 2^s` of the `α = 0` character block `H_0 = J_{2^s}`. -/
theorem spectralNorm2_H_alpha_zero (s : ℕ) :
    spectralNorm2 (H_alpha ℝ s 0) = (2 : ℝ) ^ s := by
  have heq : H_alpha ℝ s 0 = allOnesMat ℝ (2 ^ s) := by
    ext w z; simp [H_alpha, allOnesMat]
  rw [heq]
  refine spectralNorm2_eq_of_le_and_witness _ ((2 : ℝ) ^ s) (by positivity) ?_ ?_
  · intro x
    have hsq : (l2Norm (allOnesMat ℝ (2 ^ s) *ᵥ x)) ^ 2 ≤ ((2 : ℝ) ^ s * l2Norm x) ^ 2 := by
      rw [sq_l2Norm, mul_pow, sq_l2Norm]
      have hconst : ∀ w : Fin (2 ^ s), (allOnesMat ℝ (2 ^ s) *ᵥ x) w = ∑ z : Fin (2 ^ s), x z := by
        intro w; simp [Matrix.mulVec, dotProduct, allOnesMat]
      simp_rw [hconst, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_pow, Nat.cast_ofNat]
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin (2 ^ s) => (1 : ℝ)) x
      simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat] at hcs
      nlinarith [ (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ s) ]
    nlinarith [l2Norm_nonneg (allOnesMat ℝ (2 ^ s) *ᵥ x),
      mul_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ s) (l2Norm_nonneg x)]
  · right
    let x1 : Fin (2 ^ s) → ℝ := fun _ => 1
    have hx1_sq : (l2Norm x1) ^ 2 = (2 : ℝ) ^ s := by
      rw [sq_l2Norm]; simp [x1]
    have hx1_ne : l2Norm x1 ≠ 0 := by
      intro h0; rw [h0, zero_pow (by decide)] at hx1_sq
      linarith [(by positivity : (0 : ℝ) < (2 : ℝ) ^ s)]
    refine ⟨x1, hx1_ne, ?_⟩
    have hAx : allOnesMat ℝ (2 ^ s) *ᵥ x1 = ((2 : ℝ) ^ s) • x1 := by
      ext w; simp [Matrix.mulVec, dotProduct, allOnesMat, x1]
    rw [hAx, l2Norm_smul, abs_of_pos (by positivity)]

/-- **Theorem 4.1(c), Exact Spectral Norm of `H_α` (`α ≠ 0` with highest bit `r`)**:
`‖H_α‖₂ = max_{0 ≤ ℓ < 2^r} σ_ℓ(H_α)`. -/
theorem spectralNorm2_H_alpha_eq_sup_sigma {s r : ℕ} {α : Fin s → ZMod 2}
    (h : HasHighestBit s α r) :
    spectralNorm2 (H_alpha ℝ s α) =
      (Finset.univ : Finset (Fin (2 ^ r))).sup' Finset.univ_nonempty (sigmaHAlpha s r α) := by
  let e := divModPowTwoEquiv s r h.2.1
  rw [← spectralNorm2_reindex e e (H_alpha ℝ s α), H_alpha_reindex_eq_kronecker ℝ h]
  set K_mat_r := Matrix.kroneckerMap (· * ·) (allOnesMat ℝ (2 ^ (s - r))) (Htilde_alpha ℝ s r α)
  let S := (Finset.univ : Finset (Fin (2 ^ r))).sup' Finset.univ_nonempty (sigmaHAlpha s r α)
  obtain ⟨ℓ₀, _, hℓ₀_eq⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (sigmaHAlpha s r α)
  have hS_pos : 0 < S := by
    dsimp only [S]; rw [hℓ₀_eq]; exact sigmaHAlpha_pos s r α ℓ₀
  let B := (Finset.univ : Finset (Fin (2 ^ r))).sup' Finset.univ_nonempty
    (fun ℓ => ‖lambdaAlpha s r α ℓ‖)
  have hS_eq_B : S = (2 : ℝ) ^ (s - r) * B := by
    have hB_le : ∀ ℓ : Fin (2 ^ r), sigmaHAlpha s r α ℓ ≤ (2 : ℝ) ^ (s - r) * B := by
      intro ℓ
      unfold sigmaHAlpha
      exact mul_le_mul_of_nonneg_left
        (Finset.le_sup' (fun k => ‖lambdaAlpha s r α k‖) (Finset.mem_univ ℓ)) (by positivity)
    obtain ⟨ℓ₁, _, hℓ₁⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun ℓ => ‖lambdaAlpha s r α ℓ‖)
    apply le_antisymm
    · exact Finset.sup'_le Finset.univ_nonempty _ fun ℓ _ => hB_le ℓ
    · calc (2 : ℝ) ^ (s - r) * B
          = sigmaHAlpha s r α ℓ₁ := by dsimp only [B]; rw [hℓ₁]; rfl
        _ ≤ S := Finset.le_sup' (sigmaHAlpha s r α) (Finset.mem_univ ℓ₁)
  refine spectralNorm2_eq_of_le_and_witness K_mat_r S hS_pos.le ?_ ?_
  · intro x
    let x_sum : Fin (2 ^ r) → ℝ := fun z => ∑ qz : Fin (2 ^ (s - r)), x (qz, z)
    have hmv_eq : ∀ qw : Fin (2 ^ (s - r)), ∀ w : Fin (2 ^ r),
        (K_mat_r *ᵥ x) (qw, w) = (Htilde_alpha ℝ s r α *ᵥ x_sum) w := by
      intro qw w
      simp only [K_mat_r, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, allOnesMat,
        one_mul, x_sum]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Finset.mul_sum]
    have hlhs_sq :
        (l2Norm (K_mat_r *ᵥ x)) ^ 2 =
          (2 : ℝ) ^ (s - r) * (l2Norm (Htilde_alpha ℝ s r α *ᵥ x_sum)) ^ 2 := by
      rw [sq_l2Norm, sq_l2Norm, Fintype.sum_prod_type]
      simp_rw [hmv_eq]
      simp [Finset.sum_const]
    have hxsum_sq : (l2Norm x_sum) ^ 2 ≤ (2 : ℝ) ^ (s - r) * (l2Norm x) ^ 2 := by
      rw [sq_l2Norm, sq_l2Norm, Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_le_sum fun z _ => ?_
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun _ : Fin (2 ^ (s - r)) => (1 : ℝ)) (fun qz => x (qz, z))
      simpa [x_sum] using hcs
    have hHtilde := Htilde_alpha_sq_l2Norm_le h B
      (fun ℓ => Finset.le_sup' (fun k => ‖lambdaAlpha s r α k‖) (Finset.mem_univ ℓ)) x_sum
    have hB_nonneg : 0 ≤ B :=
      le_trans (norm_nonneg (lambdaAlpha s r α ℓ₀))
        (Finset.le_sup' (fun k => ‖lambdaAlpha s r α k‖) (Finset.mem_univ ℓ₀))
    have htotal_sq : (l2Norm (K_mat_r *ᵥ x)) ^ 2 ≤ (S * l2Norm x) ^ 2 := by
      calc (l2Norm (K_mat_r *ᵥ x)) ^ 2
          = (2 : ℝ) ^ (s - r) * (l2Norm (Htilde_alpha ℝ s r α *ᵥ x_sum)) ^ 2 := hlhs_sq
        _ ≤ (2 : ℝ) ^ (s - r) * (B ^ 2 * (l2Norm x_sum) ^ 2) :=
            mul_le_mul_of_nonneg_left hHtilde (by positivity)
        _ ≤ (2 : ℝ) ^ (s - r) * (B ^ 2 * ((2 : ℝ) ^ (s - r) * (l2Norm x) ^ 2)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hxsum_sq (sq_nonneg B)) (by positivity)
        _ = (((2 : ℝ) ^ (s - r) * B) * l2Norm x) ^ 2 := by ring
        _ = (S * l2Norm x) ^ 2 := by rw [← hS_eq_B]
    nlinarith [l2Norm_nonneg (K_mat_r *ᵥ x), mul_nonneg hS_pos.le (l2Norm_nonneg x)]
  · right
    obtain ⟨u, hu_ne, hu_eq⟩ := Htilde_alpha_exists_real_witness h ℓ₀
    let x_wit : Fin (2 ^ (s - r)) × Fin (2 ^ r) → ℝ := fun ⟨_, z⟩ => u z
    have hxw_sq : (l2Norm x_wit) ^ 2 = (2 : ℝ) ^ (s - r) * (l2Norm u) ^ 2 := by
      rw [sq_l2Norm, sq_l2Norm, Fintype.sum_prod_type]
      simp [x_wit, Finset.sum_const]
    have hxw_ne : l2Norm x_wit ≠ 0 := by
      intro h0
      rw [h0, zero_pow (by decide)] at hxw_sq
      have hu_sq_pos : 0 < (l2Norm u) ^ 2 :=
        sq_pos_of_ne_zero hu_ne
      have hprod_pos : 0 < (2 : ℝ) ^ (s - r) * (l2Norm u) ^ 2 :=
        mul_pos (by positivity) hu_sq_pos
      linarith
    refine ⟨x_wit, hxw_ne, ?_⟩
    have hmv_wit : ∀ qw : Fin (2 ^ (s - r)), ∀ w : Fin (2 ^ r),
        (K_mat_r *ᵥ x_wit) (qw, w) = (2 : ℝ) ^ (s - r) * (Htilde_alpha ℝ s r α *ᵥ u) w := by
      intro qw w
      simp only [K_mat_r, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, allOnesMat,
        one_mul, x_wit]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_pow, Nat.cast_ofNat]
      rw [Finset.mul_sum]
    have hlhs_wit : (l2Norm (K_mat_r *ᵥ x_wit)) ^ 2 = (S * l2Norm x_wit) ^ 2 := by
      rw [sq_l2Norm, Fintype.sum_prod_type]
      simp_rw [hmv_wit]
      have hinner :
          (∑ w : Fin (2 ^ r), ((2 : ℝ) ^ (s - r) * (Htilde_alpha ℝ s r α *ᵥ u) w) ^ 2) =
            ((2 : ℝ) ^ (s - r)) ^ 2 * (l2Norm (Htilde_alpha ℝ s r α *ᵥ u)) ^ 2 := by
        rw [sq_l2Norm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => by ring
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_pow, Nat.cast_ofNat, hinner]
      dsimp only [S]
      rw [hu_eq, mul_pow, hxw_sq, hℓ₀_eq]
      unfold sigmaHAlpha
      ring
    nlinarith [l2Norm_nonneg (K_mat_r *ᵥ x_wit), mul_nonneg hS_pos.le (l2Norm_nonneg x_wit)]

/-- **Theorem 4.1(c), Sharp Spectral Envelope**:
For every `α ≠ 0` with highest nonzero bit `r`,
`‖H_α‖₂ ≤ 2^{s - r} / sin(π / 2^{r+1})` (Paper 2, eq. (4.6)). -/
theorem spectralNorm2_H_alpha_le_envelope {s r : ℕ} {α : Fin s → ZMod 2}
    (h : HasHighestBit s α r) :
    spectralNorm2 (H_alpha ℝ s α) ≤
      (2 : ℝ) ^ (s - r) / Real.sin (Real.pi / (2 : ℝ) ^ (r + 1)) := by
  rw [spectralNorm2_H_alpha_eq_sup_sigma h]
  exact Finset.sup'_le Finset.univ_nonempty _ fun ℓ _ => sigmaHAlpha_le_envelope h.1 α ℓ

private lemma sigmaHAlpha_eq_envelope_iff_factors {s r : ℕ} (_hr1 : 1 ≤ r)
    (α : Fin s → ZMod 2) (ℓ : Fin (2 ^ r)) :
    sigmaHAlpha s r α ℓ = (2 : ℝ) ^ (s - r) / Real.sin (Real.pi / (2 : ℝ) ^ (r + 1)) ↔
      ∀ j < r,
        (2 * ℓ.val + 1 + (alphaCoeff s α j).val * 2 ^ (r - j)) % 2 ^ (r - j + 1) = 1 ∨
          (2 * ℓ.val + 1 + (alphaCoeff s α j).val * 2 ^ (r - j)) % 2 ^ (r - j + 1) =
            2 ^ (r - j + 1) - 1 := by
  unfold sigmaHAlpha
  have h2_ne : (2 : ℝ) ^ (s - r) ≠ 0 := by positivity
  have hdiv_eq :
      (2 : ℝ) ^ (s - r) / Real.sin (Real.pi / (2 : ℝ) ^ (r + 1)) =
        (2 : ℝ) ^ (s - r) * (1 / Real.sin (Real.pi / (2 : ℝ) ^ (r + 1))) := by ring
  rw [hdiv_eq, mul_right_inj' h2_ne, lambdaAlpha, norm_prod, ← prod_two_cos_pi_div_two_pow r]
  have hf_pos : ∀ j ∈ Finset.range r,
      0 < ‖1 + ((-1 : ℂ) ^ (alphaCoeff s α j).val) * (zetaNeg r ℓ) ^ (2 ^ j)‖ :=
    fun j hj => norm_pos_iff.mpr (factor_lambdaAlpha_ne_zero (Finset.mem_range.mp hj) α ℓ)
  have hf_le : ∀ j ∈ Finset.range r,
      ‖1 + ((-1 : ℂ) ^ (alphaCoeff s α j).val) * (zetaNeg r ℓ) ^ (2 ^ j)‖ ≤
        2 * Real.cos (Real.pi / (2 : ℝ) ^ (r - j + 1)) :=
    fun j hj => (factor_norm_le_and_eq_iff (Finset.mem_range.mp hj) α ℓ).1
  rw [prod_eq_prod_iff_of_pos_of_le (Finset.range r) hf_pos hf_le]
  constructor
  · intro hall j hj
    exact (factor_norm_le_and_eq_iff hj α ℓ).2.mp (hall j (Finset.mem_range.mpr hj))
  · intro hall j hj
    exact (factor_norm_le_and_eq_iff (Finset.mem_range.mp hj) α ℓ).2.mpr
      (hall j (Finset.mem_range.mp hj))

/-- **Theorem 4.1(c), Exact Equality Criterion (`r ≥ 2`)**:
For `α` with highest bit `r ≥ 2`,
`‖H_α‖₂ = 2^{s - r} / sin(π / 2^{r+1}) ↔ α ∈ {e_r, e_r + e_{r-1}}`. -/
theorem spectralNorm2_H_alpha_eq_envelope_iff {s r : ℕ} {α : Fin s → ZMod 2}
    (h : HasHighestBit s α r) (hr2 : 2 ≤ r) :
    spectralNorm2 (H_alpha ℝ s α) =
        (2 : ℝ) ^ (s - r) / Real.sin (Real.pi / (2 : ℝ) ^ (r + 1)) ↔
      α = stdUnitVec s r ∨ α = stdUnitVec s r + stdUnitVec s (r - 1) := by
  have hr1 : 1 ≤ r := by omega
  have hrs : r ≤ s := h.2.1
  have htop : α ⟨r - 1, by omega⟩ = 1 := h.2.2.1
  have hzero_above : ∀ i : Fin s, r ≤ i.val → α i = 0 := h.2.2.2
  rw [spectralNorm2_H_alpha_eq_sup_sigma h]
  have hsup_eq_iff :
      (Finset.univ : Finset (Fin (2 ^ r))).sup' Finset.univ_nonempty (sigmaHAlpha s r α) =
          (2 : ℝ) ^ (s - r) / Real.sin (Real.pi / (2 : ℝ) ^ (r + 1)) ↔
        ∃ ℓ : Fin (2 ^ r),
          sigmaHAlpha s r α ℓ = (2 : ℝ) ^ (s - r) / Real.sin (Real.pi / (2 : ℝ) ^ (r + 1)) := by
    constructor
    · intro heq
      obtain ⟨ℓ₀, _, hℓ₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (sigmaHAlpha s r α)
      exact ⟨ℓ₀, hℓ₀.symm.trans heq⟩
    · rintro ⟨ℓ₀, hℓ₀⟩
      apply le_antisymm
      · exact Finset.sup'_le Finset.univ_nonempty _ fun ℓ _ => sigmaHAlpha_le_envelope hr1 α ℓ
      · rw [← hℓ₀]
        exact Finset.le_sup' (sigmaHAlpha s r α) (Finset.mem_univ ℓ₀)
  rw [hsup_eq_iff]
  have hlow_zero_iff_pair :
      (∀ j : ℕ, 1 ≤ j → j ≤ r - 2 → alphaCoeff s α j = 0) ↔
        (α = stdUnitVec s r ∨ α = stdUnitVec s r + stdUnitVec s (r - 1)) := by
    constructor
    · intro hlow
      rcases zmod2_eq_zero_or_one (α ⟨r - 2, by omega⟩) with hb0 | hb1
      · left
        ext i
        simp only [stdUnitVec]
        by_cases hi_top : i.val + 1 = r
        · have hidx : i = ⟨r - 1, by omega⟩ := Fin.ext (by dsimp only; omega)
          simp only [hi_top, ↓reduceIte]
          rw [hidx, htop]
        · simp only [hi_top, ↓reduceIte]
          by_cases hi_ge : r ≤ i.val
          · exact hzero_above i hi_ge
          · by_cases hi_sub : i.val = r - 2
            · have hidx : i = ⟨r - 2, by omega⟩ := Fin.ext hi_sub
              rw [hidx, hb0]
            · have hlt : i.val + 1 ≤ r - 2 := by omega
              have hc := hlow (i.val + 1) (by omega) hlt
              rwa [alphaCoeff_succ_of_lt i.isLt] at hc
      · right
        ext i
        simp only [Pi.add_apply, stdUnitVec]
        by_cases hi_top : i.val + 1 = r
        · have hrr : r ≠ r - 1 := by omega
          have hidx : i = ⟨r - 1, by omega⟩ := Fin.ext (by dsimp only; omega)
          simp only [hi_top, hrr, ↓reduceIte, add_zero]
          rw [hidx, htop]
        · by_cases hi_sub : i.val + 1 = r - 1
          · have hrr : r - 1 ≠ r := by omega
            have hidx : i = ⟨r - 2, by omega⟩ := Fin.ext (by dsimp only; omega)
            simp only [hi_sub, hrr, ↓reduceIte, zero_add]
            rw [hidx, hb1]
          · simp only [hi_top, hi_sub, ↓reduceIte, add_zero]
            by_cases hi_ge : r ≤ i.val
            · exact hzero_above i hi_ge
            · have hlt : i.val + 1 ≤ r - 2 := by omega
              have hc := hlow (i.val + 1) (by omega) hlt
              rwa [alphaCoeff_succ_of_lt i.isLt] at hc
    · rintro (rfl | rfl) j hj1 hjle
      · rw [show j = (j - 1) + 1 by omega, alphaCoeff_succ_of_lt (by omega)]
        simp only [stdUnitVec]
        have hne : (j - 1) + 1 ≠ r := by omega
        simp [hne]
      · rw [show j = (j - 1) + 1 by omega, alphaCoeff_succ_of_lt (by omega)]
        simp only [Pi.add_apply, stdUnitVec]
        have hne1 : (j - 1) + 1 ≠ r := by omega
        have hne2 : (j - 1) + 1 ≠ r - 1 := by omega
        simp [hne1, hne2]
  rw [← hlow_zero_iff_pair]
  constructor
  · rintro ⟨ℓ, hℓ⟩
    have hfac := (sigmaHAlpha_eq_envelope_iff_factors hr1 α ℓ).mp hℓ
    have hj0 := hfac 0 (by omega)
    simp only [alphaCoeff_zero, ZMod.val_zero, zero_mul, add_zero, Nat.sub_zero] at hj0
    have h2l_lt : 2 * ℓ.val + 1 < 2 ^ (r + 1) := by
      have hl := ℓ.isLt; rw [pow_succ]; omega
    rw [Nat.mod_eq_of_lt h2l_lt] at hj0
    have hl_ends : ℓ.val = 0 ∨ ℓ.val = 2 ^ r - 1 := by
      rcases hj0 with h0 | hmax
      · left; omega
      · right; have hl := ℓ.isLt; rw [pow_succ] at hmax; omega
    intro j hj1 hjle
    have hj_lt : j < r := by omega
    have hj_fac := hfac j hj_lt
    set m := r - j
    have hm_ge2 : 2 ≤ m := by omega
    have h4_le : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hm_ge2
    have h2m1 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
    by_contra hbj_ne
    have hbj1 : alphaCoeff s α j = 1 := (zmod2_ne_zero_iff _).mp hbj_ne
    rw [hbj1, zmod2_val_one, one_mul] at hj_fac
    rcases hl_ends with hl0 | hlmax
    · rw [hl0] at hj_fac
      change (2 * 0 + 1 + 2 ^ m) % 2 ^ (m + 1) = 1 ∨
        (2 * 0 + 1 + 2 ^ m) % 2 ^ (m + 1) = 2 ^ (m + 1) - 1 at hj_fac
      have hlt_mod : 1 + 2 ^ m < 2 ^ (m + 1) := by omega
      simp only [mul_zero, zero_add, Nat.mod_eq_of_lt hlt_mod] at hj_fac
      omega
    · rw [hlmax] at hj_fac
      change (2 * (2 ^ r - 1) + 1 + 2 ^ m) % 2 ^ (m + 1) = 1 ∨
        (2 * (2 ^ r - 1) + 1 + 2 ^ m) % 2 ^ (m + 1) = 2 ^ (m + 1) - 1 at hj_fac
      have h2r_pos : 1 ≤ 2 ^ r := Nat.one_le_pow r 2 (by decide)
      have h2j_pos : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by decide)
      have hr1_split : 2 ^ (r + 1) = 2 ^ (m + 1) * 2 ^ j := by
        rw [← pow_add]; congr 1; omega
      have hnum_eq :
          2 * (2 ^ r - 1) + 1 + 2 ^ m =
            2 ^ (m + 1) * 2 ^ j + (2 ^ m - 1) := by
        have h2r1 : 2 * 2 ^ r = 2 ^ (r + 1) := by rw [pow_succ]; ring
        have h2m_pos : 1 ≤ 2 ^ m := by omega
        omega
      have hmod_val : (2 * (2 ^ r - 1) + 1 + 2 ^ m) % 2 ^ (m + 1) = 2 ^ m - 1 := by
        rw [hnum_eq, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      rw [hmod_val] at hj_fac
      omega
  · intro hlow
    refine ⟨⟨0, by positivity⟩, (sigmaHAlpha_eq_envelope_iff_factors hr1 α ⟨0, by positivity⟩).mpr ?_⟩
    intro j hj_lt
    simp only [mul_zero, zero_add]
    by_cases hj0 : j = 0
    · subst hj0
      simp only [alphaCoeff_zero, ZMod.val_zero, zero_mul, add_zero, Nat.sub_zero]
      left
      exact Nat.mod_eq_of_lt (by
        calc 1 < 2 ^ 1 := by decide
          _ ≤ 2 ^ (r + 1) := Nat.pow_le_pow_right (by decide) (by omega))
    · by_cases hj_sub : j = r - 1
      · subst hj_sub
        have hm1 : r - (r - 1) = 1 := by omega
        rw [hm1]
        rcases zmod2_eq_zero_or_one (alphaCoeff s α (r - 1)) with hb0 | hb1
        · rw [hb0]; left; decide
        · rw [hb1]; right; decide
      · have hj_le : j ≤ r - 2 := by omega
        rw [hlow j (by omega) hj_le, ZMod.val_zero, zero_mul, add_zero]
        left
        exact Nat.mod_eq_of_lt (by
          calc 1 < 2 ^ 1 := by decide
            _ ≤ 2 ^ (r - j + 1) := Nat.pow_le_pow_right (by decide) (by omega))

/-- At `r = 1` (`s ≥ 1`, `α = e_1`), BOTH `ℓ = 0` and `ℓ = 1` achieve `σ_ℓ(H_{e_1}) = 2^{s - 1/2}`
(multiplicity `2`; Paper 2, Theorem 4.1(c), eq. (4.7)). -/
theorem sigmaHAlpha_e1_eq {s : ℕ} (hs : 1 ≤ s) (ℓ : Fin (2 ^ 1)) :
    sigmaHAlpha s 1 (stdUnitVec s 1) ℓ = (2 : ℝ) ^ ((s : ℝ) - 1 / 2) := by
  have heq_env : sigmaHAlpha s 1 (stdUnitVec s 1) ℓ =
      (2 : ℝ) ^ (s - 1) / Real.sin (Real.pi / (2 : ℝ) ^ (1 + 1)) := by
    refine (sigmaHAlpha_eq_envelope_iff_factors (by decide) (stdUnitVec s 1) ℓ).mpr ?_
    intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    simp only [alphaCoeff_zero, ZMod.val_zero, zero_mul, add_zero, Nat.sub_zero]
    fin_cases ℓ
    · left; decide
    · right; decide
  rw [heq_env]
  have hpi4 : Real.pi / (2 : ℝ) ^ (1 + 1) = Real.pi / 4 := by norm_num
  rw [hpi4, Real.sin_pi_div_four]
  have h2_pos : (0 : ℝ) < 2 := by positivity
  have hsqrt : (2 : ℝ) ^ (s - 1) / (Real.sqrt 2 / 2) =
      (2 : ℝ) ^ (s - 1) * (2 : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt h2_pos.le
    have hne : Real.sqrt 2 ≠ 0 := by positivity
    field_simp [hne]
    nlinarith [hsq2]
  rw [hsqrt, ← Real.rpow_natCast 2 (s - 1), ← Real.rpow_add h2_pos]
  congr 1
  have hs_cast : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by
    simpa using Nat.cast_sub (R := ℝ) hs
  linarith

/-- `‖H_{e_1}‖₂ = 2^{s - 1/2}` (`s ≥ 1`). -/
theorem spectralNorm2_H_alpha_e1 {s : ℕ} (hs : 1 ≤ s) :
    spectralNorm2 (H_alpha ℝ s (stdUnitVec s 1)) = (2 : ℝ) ^ ((s : ℝ) - 1 / 2) := by
  have hh1 : HasHighestBit s (stdUnitVec s 1) 1 := by
    refine ⟨by decide, hs, ?_, ?_⟩
    · simp [stdUnitVec]
    · intro i hi; simp [stdUnitVec]; omega
  rw [spectralNorm2_H_alpha_eq_sup_sigma hh1]
  apply le_antisymm
  · exact Finset.sup'_le Finset.univ_nonempty _ fun ℓ _ => (sigmaHAlpha_e1_eq hs ℓ).le
  · rw [← sigmaHAlpha_e1_eq hs ⟨0, by decide⟩]
    exact Finset.le_sup' (sigmaHAlpha s 1 (stdUnitVec s 1)) (Finset.mem_univ _)

private lemma envelope_strict_anti_step (s r : ℕ) (hr1 : 1 ≤ r) (hr1s : r + 1 ≤ s) :
    (2 : ℝ) ^ (s - (r + 1)) / Real.sin (Real.pi / (2 : ℝ) ^ (r + 2)) <
      (2 : ℝ) ^ (s - r) / Real.sin (Real.pi / (2 : ℝ) ^ (r + 1)) := by
  set φ := Real.pi / (2 : ℝ) ^ (r + 2)
  have hpow_ge8 : (8 : ℝ) ≤ (2 : ℝ) ^ (r + 2) := by
    calc (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
      _ ≤ (2 : ℝ) ^ (r + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hφ_pos : 0 < φ := div_pos Real.pi_pos (by positivity)
  have hφ_lt_pi4 : φ < Real.pi / 2 := by
    dsimp only [φ]
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.pi_pos]
  have hsin_pos : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ_pos (by linarith [Real.pi_pos])
  have hcos_pos : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hφ_lt_pi4⟩
  have hcos_lt1 : Real.cos φ < 1 := by
    rw [← Real.cos_zero]
    exact Real.strictAntiOn_cos ⟨le_refl 0, Real.pi_pos.le⟩
      ⟨hφ_pos.le, by linarith [Real.pi_pos]⟩ hφ_pos
  have h2φ : Real.pi / (2 : ℝ) ^ (r + 1) = 2 * φ := by
    dsimp only [φ]
    have hp2 : (2 : ℝ) ^ (r + 2) = (2 : ℝ) ^ (r + 1) * 2 := by
      rw [show r + 2 = (r + 1) + 1 by ring, pow_succ]
    rw [hp2]
    have hne : (2 : ℝ) ^ (r + 1) ≠ 0 := by positivity
    field_simp [hne]
  rw [h2φ, Real.sin_two_mul]
  have hsin2_pos : 0 < 2 * Real.sin φ * Real.cos φ := by positivity
  have hpow_step : (2 : ℝ) ^ (s - r) = 2 * (2 : ℝ) ^ (s - (r + 1)) := by
    have hsub : s - r = (s - (r + 1)) + 1 := by omega
    rw [hsub, pow_succ]; ring
  rw [hpow_step, div_lt_div_iff₀ hsin_pos hsin2_pos]
  have hp_pos : (0 : ℝ) < (2 : ℝ) ^ (s - (r + 1)) := by positivity
  have hprod_pos : 0 < (2 : ℝ) ^ (s - (r + 1)) * (2 * Real.sin φ) := by positivity
  calc (2 : ℝ) ^ (s - (r + 1)) * (2 * Real.sin φ * Real.cos φ)
      = ((2 : ℝ) ^ (s - (r + 1)) * (2 * Real.sin φ)) * Real.cos φ := by ring
    _ < ((2 : ℝ) ^ (s - (r + 1)) * (2 * Real.sin φ)) * 1 :=
        mul_lt_mul_of_pos_left hcos_lt1 hprod_pos
    _ = 2 * (2 : ℝ) ^ (s - (r + 1)) * Real.sin φ := by ring

private lemma envelope_le_r2 {s r : ℕ} (hr2 : 2 ≤ r) (hrs : r ≤ s) :
    (2 : ℝ) ^ (s - r) / Real.sin (Real.pi / (2 : ℝ) ^ (r + 1)) ≤
      (2 : ℝ) ^ s / (4 * Real.sin (Real.pi / 8)) := by
  have hr2_eq :
      (2 : ℝ) ^ (s - 2) / Real.sin (Real.pi / (2 : ℝ) ^ (2 + 1)) =
        (2 : ℝ) ^ s / (4 * Real.sin (Real.pi / 8)) := by
    have hs2 : (2 : ℝ) ^ s = 4 * (2 : ℝ) ^ (s - 2) := by
      have hsub : s = (s - 2) + 2 := by omega
      conv_lhs => rw [hsub, pow_add]
      norm_num; ring
    have h8 : (2 : ℝ) ^ (2 + 1) = 8 := by norm_num
    rw [hs2, h8]
    have hsin8 : Real.sin (Real.pi / 8) ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos (by norm_num))
        (div_lt_self Real.pi_pos (by norm_num))).ne'
    field_simp [hsin8]
  rw [← hr2_eq]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr2
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep := envelope_strict_anti_step s (2 + k) (by omega) (by omega)
    have hprev := ih (by omega) (by omega)
    exact (le_of_lt hstep).trans hprev

/-- **Theorem 4.1(c), Second-Tier Spectral Norm Bound (`s ≥ 2`, i.e., `t ≥ 3`)**:
For every `α ∉ {0, e_1}`, `‖H_α‖₂ ≤ 2^s / (4 sin(π / 8))` (Paper 2, Section 4, proof of Theorem 4.1(c)). -/
theorem second_tier_spectralNorm2_H_alpha_le {s : ℕ} (_hs : 2 ≤ s) {α : Fin s → ZMod 2}
    (h0 : α ≠ 0) (he1 : α ≠ stdUnitVec s 1) :
    spectralNorm2 (H_alpha ℝ s α) ≤ (2 : ℝ) ^ s / (4 * Real.sin (Real.pi / 8)) := by
  obtain ⟨r, hr, _⟩ := existsUnique_hasHighestBit s h0
  have hr2 : 2 ≤ r := by
    rcases hr with ⟨hr1, hrs, htop, hzero⟩
    by_contra hlt2
    have hr_eq1 : r = 1 := by omega
    subst hr_eq1
    apply he1
    ext i
    simp only [stdUnitVec]
    by_cases hi0 : i.val = 0
    · have hidx : i = ⟨0, by omega⟩ := by ext; exact hi0
      rw [hidx]
      simpa using htop
    · have hi_ge : 1 ≤ i.val := by omega
      rw [hzero i hi_ge]
      simp [hi0]
  exact (spectralNorm2_H_alpha_le_envelope hr).trans (envelope_le_r2 hr2 hr.2.1)

/-- Attainment of the second-tier spectral norm `2^s / (4 sin(π / 8))` at `α = e_2` (`s ≥ 2`). -/
theorem second_tier_spectralNorm2_attained_e2 {s : ℕ} (hs : 2 ≤ s) :
    spectralNorm2 (H_alpha ℝ s (stdUnitVec s 2)) =
      (2 : ℝ) ^ s / (4 * Real.sin (Real.pi / 8)) := by
  have hh2 : HasHighestBit s (stdUnitVec s 2) 2 := by
    refine ⟨by decide, hs, ?_, ?_⟩
    · simp [stdUnitVec]
    · intro i hi
      have hne : i.val + 1 ≠ 2 := by omega
      simp [stdUnitVec, hne]
  have heq := (spectralNorm2_H_alpha_eq_envelope_iff hh2 (by decide)).mpr (Or.inl rfl)
  rw [heq]
  have hs2 : (2 : ℝ) ^ s = 4 * (2 : ℝ) ^ (s - 2) := by
    have hsub : s = (s - 2) + 2 := by omega
    conv_lhs => rw [hsub, pow_add]
    norm_num; ring
  have h8 : (2 : ℝ) ^ (2 + 1) = 8 := by norm_num
  rw [hs2, h8]
  have hsin8 : Real.sin (Real.pi / 8) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos (by norm_num))
      (div_lt_self Real.pi_pos (by norm_num))).ne'
  field_simp [hsin8]

/-- Attainment of the second-tier spectral norm `2^s / (4 sin(π / 8))` at `α = e_2 + e_1` (`s ≥ 2`). -/
theorem second_tier_spectralNorm2_attained_e2_add_e1 {s : ℕ} (hs : 2 ≤ s) :
    spectralNorm2 (H_alpha ℝ s (stdUnitVec s 2 + stdUnitVec s 1)) =
      (2 : ℝ) ^ s / (4 * Real.sin (Real.pi / 8)) := by
  have hh2 : HasHighestBit s (stdUnitVec s 2 + stdUnitVec s 1) 2 := by
    refine ⟨by decide, hs, ?_, ?_⟩
    · simp [stdUnitVec]
    · intro i hi
      have hne1 : i.val + 1 ≠ 2 := by omega
      have hne0 : i.val ≠ 0 := by omega
      simp [stdUnitVec, hne1, hne0]
  have heq := (spectralNorm2_H_alpha_eq_envelope_iff hh2 (by decide)).mpr (Or.inr rfl)
  rw [heq]
  have hs2 : (2 : ℝ) ^ s = 4 * (2 : ℝ) ^ (s - 2) := by
    have hsub : s = (s - 2) + 2 := by omega
    conv_lhs => rw [hsub, pow_add]
    norm_num; ring
  have h8 : (2 : ℝ) ^ (2 + 1) = 8 := by norm_num
  rw [hs2, h8]
  have hsin8 : Real.sin (Real.pi / 8) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos (by norm_num))
      (div_lt_self Real.pi_pos (by norm_num))).ne'
  field_simp [hsin8]

/-- Strict spectral gap separation `2^s / (4 sin(π / 8)) < 2^s / √2` (for all `s : ℕ`). -/
theorem second_tier_lt_spectral_gap (s : ℕ) :
    (2 : ℝ) ^ s / (4 * Real.sin (Real.pi / 8)) < (2 : ℝ) ^ s / Real.sqrt 2 := by
  have hpi4 : Real.pi / 4 = 2 * (Real.pi / 8) := by ring
  have hsin_pi4 : Real.sin (Real.pi / 4) = 2 * Real.sin (Real.pi / 8) * Real.cos (Real.pi / 8) := by
    conv_lhs => rw [hpi4, Real.sin_two_mul]
  have hsin8_pos : 0 < Real.sin (Real.pi / 8) :=
    Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos (by norm_num))
      (div_lt_self Real.pi_pos (by norm_num))
  have hcos8_lt1 : Real.cos (Real.pi / 8) < 1 := by
    rw [← Real.cos_zero]
    exact Real.strictAntiOn_cos ⟨le_refl 0, Real.pi_pos.le⟩
      ⟨(div_pos Real.pi_pos (by norm_num)).le, (div_lt_self Real.pi_pos (by norm_num)).le⟩
      (div_pos Real.pi_pos (by norm_num))
  rw [Real.sin_pi_div_four] at hsin_pi4
  have hlt_denom : Real.sqrt 2 < 4 * Real.sin (Real.pi / 8) := by nlinarith
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have h2s_pos : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
  nlinarith

/-! #### Centered Matrix `M - p 1 1ᵀ` and Exact Centered Spectral Gap `Λ(K_t)`, `Λ(M_t)` -/

/-- Centered matrix `M - p · 1 1ᵀ`. -/
def centeredMat {m n : Type*} (M : Matrix m n ℝ) (p : ℝ) : Matrix m n ℝ :=
  M - p • Matrix.of (fun _ _ => 1)

/-- At `t = 1` (`s = 0`), `Λ(K_1) = 0`. -/
theorem centeredSpectralGap_K_one :
    spectralNorm2 (centeredMat (K_coreMat ℝ 0) 1) = 0 := by
  have hzero : centeredMat (K_coreMat ℝ 0) 1 = 0 := by
    ext ⟨x, w⟩ ⟨y, z⟩
    have hx : x + y = borrowVec 0 w z := Subsingleton.elim _ _
    simp [centeredMat, K_coreMat, K_coreRel, hx]
  rw [hzero]
  exact spectralNorm2_eq_of_le_and_witness 0 0 (le_refl 0)
    (fun x => by simp) (Or.inl rfl)

/-- **Theorem 4.1(c), Exact Centered Spectral Norm of `C_t` (`t = s + 1 ≥ 2`, i.e., `s ≥ 1`)**:
`Λ(C_t) = ‖C_t - 2^{-s} 1 1ᵀ‖₂ = 2^{s - 1/2}` (`= 2^{t - 3/2}`; Paper 2, eq. (4.7)). -/
theorem centeredSpectralGap_K_core {s : ℕ} (hs : 1 ≤ s) :
    spectralNorm2 (centeredMat (K_coreMat ℝ s) (((2 : ℝ) ^ s)⁻¹)) =
      (2 : ℝ) ^ ((s : ℝ) - 1 / 2) := by
  let Q := Matrix.kroneckerMap (· * ·) (H_s s) (1 : Matrix (Fin (2 ^ s)) (Fin (2 ^ s)) ℝ)
  have hQt : Qᵀ = Q := by
    dsimp only [Q]
    rw [← Matrix.kroneckerMap_transpose, H_s_transpose, Matrix.transpose_one]
  have hQ2 : Q * Q = 1 := by
    dsimp only [Q]
    rw [← Matrix.mul_kronecker_mul, H_s_mul_self, mul_one, Matrix.one_kronecker_one]
  rw [← spectralNorm2_orth_conj hQt hQ2 (centeredMat (K_coreMat ℝ s) (((2 : ℝ) ^ s)⁻¹))]
  let Ones : Matrix ((Fin s → ZMod 2) × Fin (2 ^ s)) ((Fin s → ZMod 2) × Fin (2 ^ s)) ℝ :=
    Matrix.of (fun _ _ => (1 : ℝ))
  have hconj_ones :
      ∀ (α β : Fin s → ZMod 2) (w z : Fin (2 ^ s)),
        (Q * ((((2 : ℝ) ^ s)⁻¹) • Ones) * Q) (α, w) (β, z) =
          if α = 0 ∧ β = 0 then 1 else 0 := by
    intro α β w z
    let W_I := Matrix.kroneckerMap (· * ·) (W_unnorm ℝ s) (1 : Matrix (Fin (2 ^ s)) (Fin (2 ^ s)) ℝ)
    have hW_I : Q = ((Real.sqrt 2) ^ s)⁻¹ • W_I := by
      ext ⟨a, u⟩ ⟨b, v⟩
      simp [Q, W_I, H_s, mul_assoc]
    have hsmul_pull :
        Q * ((((2 : ℝ) ^ s)⁻¹) • Ones) * Q =
          (((Real.sqrt 2) ^ s)⁻¹ * (((Real.sqrt 2) ^ s)⁻¹ * ((2 : ℝ) ^ s)⁻¹)) •
            (W_I * Ones * W_I) := by
      rw [hW_I, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.smul_mul, smul_smul, smul_smul, mul_assoc]
    rw [hsmul_pull, Matrix.smul_apply, smul_eq_mul]
    simp only [W_I, Ones, Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Matrix.of_apply, mul_one]
    have hinner :
        (∑ a : (Fin s → ZMod 2) × Fin (2 ^ s),
            W_unnorm ℝ s α a.1 * if w = a.2 then 1 else 0) =
          if α = 0 then (2 : ℝ) ^ s else 0 := by
      rw [Fintype.sum_prod_type]
      have hrow : ∀ a₁ : Fin s → ZMod 2,
          (∑ a₂ : Fin (2 ^ s), W_unnorm ℝ s α a₁ * if w = a₂ then (1 : ℝ) else 0) =
            W_unnorm ℝ s α a₁ := by
        intro a₁; simp
      have hsum_eq :
          (∑ a₁ : Fin s → ZMod 2, ∑ a₂ : Fin (2 ^ s),
              W_unnorm ℝ s α a₁ * if w = a₂ then (1 : ℝ) else 0) =
            ∑ a₁ : Fin s → ZMod 2, W_unnorm ℝ s α a₁ :=
        Finset.sum_congr rfl fun a₁ _ => hrow a₁
      rw [hsum_eq]
      exact sum_f2Inner_sign s α
    have houter :
        (∑ b : (Fin s → ZMod 2) × Fin (2 ^ s),
            (∑ a : (Fin s → ZMod 2) × Fin (2 ^ s),
                W_unnorm ℝ s α a.1 * if w = a.2 then 1 else 0) *
              (W_unnorm ℝ s b.1 β * if b.2 = z then 1 else 0)) =
          (if α = 0 then (2 : ℝ) ^ s else 0) * (if β = 0 then (2 : ℝ) ^ s else 0) := by
      have hstep1 :
          (∑ b : (Fin s → ZMod 2) × Fin (2 ^ s),
              (∑ a : (Fin s → ZMod 2) × Fin (2 ^ s),
                  W_unnorm ℝ s α a.1 * if w = a.2 then 1 else 0) *
                (W_unnorm ℝ s b.1 β * if b.2 = z then 1 else 0)) =
            ∑ b : (Fin s → ZMod 2) × Fin (2 ^ s),
              (if α = 0 then (2 : ℝ) ^ s else 0) *
                (W_unnorm ℝ s b.1 β * if b.2 = z then 1 else 0) :=
        Finset.sum_congr rfl fun _ _ => by rw [hinner]
      rw [hstep1, ← Finset.mul_sum, Fintype.sum_prod_type]
      congr 1
      have hcol2 : ∀ b₁ : Fin s → ZMod 2,
          (∑ b₂ : Fin (2 ^ s), W_unnorm ℝ s b₁ β * if b₂ = z then (1 : ℝ) else 0) =
            W_unnorm ℝ s β b₁ := by
        intro b₁; simp [W_unnorm, f2Inner_comm]
      have hsum2 :
          (∑ b₁ : Fin s → ZMod 2, ∑ b₂ : Fin (2 ^ s),
              W_unnorm ℝ s b₁ β * if b₂ = z then (1 : ℝ) else 0) =
            ∑ b₁ : Fin s → ZMod 2, W_unnorm ℝ s β b₁ :=
        Finset.sum_congr rfl fun b₁ _ => hcol2 b₁
      rw [hsum2]
      exact sum_f2Inner_sign s β
    rw [houter]
    have hscale :
        ((Real.sqrt 2) ^ s)⁻¹ * (((Real.sqrt 2) ^ s)⁻¹ * ((2 : ℝ) ^ s)⁻¹) *
          ((2 : ℝ) ^ s * (2 : ℝ) ^ s) = 1 := by
      have hpow : (Real.sqrt 2) ^ s * (Real.sqrt 2) ^ s = (2 : ℝ) ^ s := by
        rw [← mul_pow, Real.mul_self_sqrt (by positivity)]
      have hne_sq : (Real.sqrt 2) ^ s ≠ 0 := by positivity
      have hne_2 : (2 : ℝ) ^ s ≠ 0 := by positivity
      rw [← hpow]
      field_simp [hne_sq, hne_2]
    by_cases hα : α = 0 <;> by_cases hβ : β = 0
    · simp only [hα, hβ, and_self, ↓reduceIte]
      exact hscale
    · simp [hα, hβ]
    · simp [hα, hβ]
    · simp [hα, hβ]
  set C_conj := Q * centeredMat (K_coreMat ℝ s) (((2 : ℝ) ^ s)⁻¹) * Q
  have hC_blocks :
      ∀ (α β : Fin s → ZMod 2) (w z : Fin (2 ^ s)),
        C_conj (α, w) (β, z) = if α = β ∧ α ≠ 0 then H_alpha ℝ s α w z else 0 := by
    intro α β w z
    dsimp only [C_conj, centeredMat]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply]
    have h1 := walsh_conj_K_coreMat s α β w z
    change (Q * K_coreMat ℝ s * Q) (α, w) (β, z) = _ at h1
    rw [h1, hconj_ones]
    by_cases hαβ : α = β
    · subst hαβ
      by_cases hα0 : α = 0
      · subst hα0; simp [H_alpha]
      · simp [hα0]
    · have hnot00 : ¬(α = 0 ∧ β = 0) := fun ⟨h0a, h0b⟩ => hαβ (h0a.trans h0b.symm)
      simp [hαβ, hnot00]
  set gap := (2 : ℝ) ^ ((s : ℝ) - 1 / 2)
  have hgap_pos : 0 < gap := by positivity
  refine spectralNorm2_eq_of_le_and_witness C_conj gap hgap_pos.le ?_ ?_
  · intro x
    have hmv :
        ∀ (α : Fin s → ZMod 2) (w : Fin (2 ^ s)),
          (C_conj *ᵥ x) (α, w) =
            if α = 0 then 0 else (H_alpha ℝ s α *ᵥ (fun z => x (α, z))) w := by
      intro α w
      simp only [Matrix.mulVec, dotProduct]
      rw [Fintype.sum_prod_type]
      simp_rw [hC_blocks]
      by_cases hα0 : α = 0
      · subst hα0; simp
      · rw [Finset.sum_eq_single α]
        · simp [hα0]
        · intro β _ hβ
          have hne : ¬(α = β ∧ α ≠ 0) := fun h => hβ h.1.symm
          simp [hne]
        · intro hm; exact absurd (Finset.mem_univ α) hm
    have hblock_le :
        ∀ α : Fin s → ZMod 2, α ≠ 0 → spectralNorm2 (H_alpha ℝ s α) ≤ gap := by
      intro α hα0
      by_cases he1 : α = stdUnitVec s 1
      · subst he1
        exact (spectralNorm2_H_alpha_e1 hs).le
      · by_cases hs2 : 2 ≤ s
        · have h2nd := second_tier_spectralNorm2_H_alpha_le hs2 hα0 he1
          have hlt := second_tier_lt_spectral_gap s
          have hgap_eq : (2 : ℝ) ^ s / Real.sqrt 2 = gap := by
            dsimp only [gap]
            have h2_pos : (0 : ℝ) < 2 := by positivity
            rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast 2 s, ← Real.rpow_sub h2_pos]
          linarith
        · have hs_eq1 : s = 1 := by omega
          subst hs_eq1
          exfalso
          apply he1
          ext i
          fin_cases i
          have hne0 : α ⟨0, by decide⟩ ≠ 0 := by
            intro h0_i
            apply hα0
            ext j; fin_cases j; exact h0_i
          exact (zmod2_ne_zero_iff _).mp hne0
    have hsq : (l2Norm (C_conj *ᵥ x)) ^ 2 ≤ (gap * l2Norm x) ^ 2 := by
      rw [sq_l2Norm, mul_pow, sq_l2Norm, Fintype.sum_prod_type, Fintype.sum_prod_type,
        Finset.mul_sum]
      refine Finset.sum_le_sum fun α _ => ?_
      simp_rw [hmv α]
      by_cases hα0 : α = 0
      · subst hα0
        simp only [↓reduceIte, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
          Finset.sum_const_zero]
        exact mul_nonneg (sq_nonneg gap) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      · simp only [hα0, ↓reduceIte]
        rw [← sq_l2Norm (H_alpha ℝ s α *ᵥ fun z => x (α, z)), ← sq_l2Norm (fun z => x (α, z))]
        have h1 := l2Norm_mulVec_le_spectralNorm2 (H_alpha ℝ s α) (fun z => x (α, z))
        have h2 := hblock_le α hα0
        have hle_prod :
            l2Norm (H_alpha ℝ s α *ᵥ fun z => x (α, z)) ≤ gap * l2Norm (fun z => x (α, z)) :=
          h1.trans (mul_le_mul_of_nonneg_right h2 (l2Norm_nonneg _))
        have hnn1 := l2Norm_nonneg (H_alpha ℝ s α *ᵥ fun z => x (α, z))
        have hnn2 := mul_nonneg hgap_pos.le (l2Norm_nonneg fun z => x (α, z))
        calc (l2Norm (H_alpha ℝ s α *ᵥ fun z => x (α, z))) ^ 2
            ≤ (gap * l2Norm fun z => x (α, z)) ^ 2 := by nlinarith
          _ = gap ^ 2 * (l2Norm fun z => x (α, z)) ^ 2 := by ring
    nlinarith [l2Norm_nonneg (C_conj *ᵥ x), mul_nonneg hgap_pos.le (l2Norm_nonneg x)]
  · right
    let α₁ := stdUnitVec s 1
    have hα₁_ne0 : α₁ ≠ 0 := by
      intro h0
      have hv := congr_fun h0 ⟨0, hs⟩
      simp [α₁, stdUnitVec] at hv
    have hh1 : HasHighestBit s α₁ 1 := by
      refine ⟨by decide, hs, ?_, ?_⟩
      · simp [α₁, stdUnitVec]
      · intro i hi; simp [α₁, stdUnitVec]; omega
    obtain ⟨u, hu_ne, hu_eq⟩ := Htilde_alpha_exists_real_witness hh1 ⟨0, by decide⟩
    let x_e1 : (Fin s → ZMod 2) × Fin (2 ^ s) → ℝ := fun ⟨α, z⟩ =>
      if α = α₁ then u ⟨z.val % 2 ^ 1, Nat.mod_lt z.val (by decide)⟩ else 0
    have hnorm_x : (l2Norm x_e1) ^ 2 = (2 : ℝ) ^ (s - 1) * (l2Norm u) ^ 2 := by
      rw [sq_l2Norm, Fintype.sum_prod_type, Finset.sum_eq_single α₁]
      · simp only [x_e1, ↓reduceIte]
        let e := divModPowTwoEquiv s 1 hs
        rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
        have hmod : ∀ qz : Fin (2 ^ (s - 1)), ∀ r0 : Fin (2 ^ 1),
            (⟨(e.symm (qz, r0)).val % 2 ^ 1, Nat.mod_lt _ (by decide)⟩ : Fin (2 ^ 1)) = r0 := by
          intro qz r0
          fin_cases r0 <;> ext <;> simp [e, divModPowTwoEquiv, Nat.mul_add_mod_self_right]
        simp_rw [hmod]
        simp [sq_l2Norm, Finset.sum_const]
        ring
      · intro β _ hβ; simp [x_e1, hβ]
      · intro hm; exact absurd (Finset.mem_univ α₁) hm
    have hx_ne : l2Norm x_e1 ≠ 0 := by
      intro h0; rw [h0, zero_pow (by decide)] at hnorm_x
      have hpos : 0 < (2 : ℝ) ^ (s - 1) * (l2Norm u) ^ 2 :=
        mul_pos (by positivity) (sq_pos_of_ne_zero hu_ne)
      linarith
    refine ⟨x_e1, hx_ne, ?_⟩
    have hCx_sq : (l2Norm (C_conj *ᵥ x_e1)) ^ 2 = (gap * l2Norm x_e1) ^ 2 := by
      rw [sq_l2Norm, Fintype.sum_prod_type, Finset.sum_eq_single α₁]
      · have hrow_α₁ : ∀ w : Fin (2 ^ s),
            (C_conj *ᵥ x_e1) (α₁, w) =
              (2 : ℝ) ^ (s - 1) *
                (Htilde_alpha ℝ s 1 α₁ *ᵥ u) ⟨w.val % 2 ^ 1, Nat.mod_lt w.val (by decide)⟩ := by
          intro w
          simp only [Matrix.mulVec, dotProduct]
          rw [Fintype.sum_prod_type, Finset.sum_eq_single α₁]
          · have hCb : ∀ z : Fin (2 ^ s), C_conj (α₁, w) (α₁, z) = H_alpha ℝ s α₁ w z := by
              intro z; rw [hC_blocks]; simp [hα₁_ne0]
            simp_rw [hCb]
            simp only [x_e1, ↓reduceIte]
            let e := divModPowTwoEquiv s 1 hs
            rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
            have hcell : ∀ qz : Fin (2 ^ (s - 1)), ∀ r0 : Fin (2 ^ 1),
                H_alpha ℝ s α₁ w (e.symm (qz, r0)) *
                  u ⟨(e.symm (qz, r0)).val % 2 ^ 1, Nat.mod_lt _ (by decide)⟩ =
                Htilde_alpha ℝ s 1 α₁ ⟨w.val % 2 ^ 1, Nat.mod_lt w.val (by decide)⟩ r0 * u r0 := by
              intro qz r0
              rw [H_alpha_eq_Htilde_mod ℝ hh1]
              have hmod : (⟨(e.symm (qz, r0)).val % 2 ^ 1, Nat.mod_lt _ (by decide)⟩ : Fin (2 ^ 1)) = r0 := by
                fin_cases r0 <;> ext <;> simp [e, divModPowTwoEquiv, Nat.mul_add_mod_self_right]
              rw [hmod]
            simp_rw [hcell]
            rw [Finset.sum_comm]
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              Nat.cast_pow, Nat.cast_ofNat, ← Finset.mul_sum]
          · intro β _ hβ; simp [x_e1, hβ]
          · intro hm; exact absurd (Finset.mem_univ α₁) hm
        simp_rw [hrow_α₁]
        let e := divModPowTwoEquiv s 1 hs
        rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
        have hmod : ∀ qw : Fin (2 ^ (s - 1)), ∀ r0 : Fin (2 ^ 1),
            (⟨(e.symm (qw, r0)).val % 2 ^ 1, Nat.mod_lt _ (by decide)⟩ : Fin (2 ^ 1)) = r0 := by
          intro qw r0
          fin_cases r0 <;> ext <;> simp [e, divModPowTwoEquiv, Nat.mul_add_mod_self_right]
        simp_rw [hmod]
        have hsum_r0 :
            (∑ r0 : Fin (2 ^ 1), ((2 : ℝ) ^ (s - 1) * (Htilde_alpha ℝ s 1 α₁ *ᵥ u) r0) ^ 2) =
              ((2 : ℝ) ^ (s - 1)) ^ 2 * (l2Norm (Htilde_alpha ℝ s 1 α₁ *ᵥ u)) ^ 2 := by
          rw [sq_l2Norm, Finset.mul_sum]
          refine Finset.sum_congr rfl fun r0 _ => by ring
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_pow, Nat.cast_ofNat, hsum_r0]
        have hsig0 := sigmaHAlpha_e1_eq hs ⟨0, by decide⟩
        change (2 : ℝ) ^ (s - 1) * ‖lambdaAlpha s 1 α₁ ⟨0, by decide⟩‖ = gap at hsig0
        rw [hu_eq, mul_pow, hnorm_x, ← hsig0]
        ring
      · intro α _ hα
        have hrow0 : ∀ w : Fin (2 ^ s), (C_conj *ᵥ x_e1) (α, w) = 0 := by
          intro w
          simp only [Matrix.mulVec, dotProduct]
          rw [Fintype.sum_prod_type]
          refine Finset.sum_eq_zero fun β _ => Finset.sum_eq_zero fun z _ => ?_
          by_cases hβ : β = α₁
          · subst hβ
            have hne : α ≠ α₁ := hα
            simp [hC_blocks, hne]
          · simp [x_e1, hβ]
        simp [hrow0]
      · intro hm; exact absurd (Finset.mem_univ α₁) hm
    nlinarith [l2Norm_nonneg (C_conj *ᵥ x_e1), mul_nonneg hgap_pos.le (l2Norm_nonneg x_e1)]

/-- `Λ(M_t) = 2^t` for all `t = s + 1 ≥ 1` (Paper 2, Theorem 4.1(c), Table 1). -/
theorem centeredSpectralGap_M_mat (s : ℕ) :
    spectralNorm2 (centeredMat (M_mat ℝ (s + 1)) (((2 : ℝ) ^ (s + 1))⁻¹)) =
      (2 : ℝ) ^ (s + 1) := by
  let t := s + 1
  have hreindex :
      (centeredMat (M_mat ℝ t) (((2 : ℝ) ^ t)⁻¹)).reindex (mCoordEquiv s) (mCoordEquiv s) =
        centeredMat
          (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℝ)
            (Matrix.kroneckerMap (· * ·) (K_coreMat ℝ s) (allOnesMat ℝ 2)))
          (((2 : ℝ) ^ t)⁻¹) := by
    ext r c
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, centeredMat, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.of_apply]
    have hm := congr_fun (congr_fun (M_mat_reindex_eq_kronecker ℝ s) r) c
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply] at hm
    rw [hm]
  rw [← spectralNorm2_reindex (mCoordEquiv s) (mCoordEquiv s), hreindex]
  set B_core := Matrix.kroneckerMap (· * ·) (K_coreMat ℝ s) (allOnesMat ℝ 2)
  set M_re := Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℝ) B_core
  set C_M := centeredMat M_re (((2 : ℝ) ^ t)⁻¹)
  have hB_row : ∀ u : ((Fin s → ZMod 2) × Fin (2 ^ s)) × Fin 2,
      (∑ v : ((Fin s → ZMod 2) × Fin (2 ^ s)) × Fin 2, B_core u v) = (2 : ℝ) ^ t := by
    rintro ⟨⟨x', w'⟩, wt⟩
    simp only [B_core, Matrix.kroneckerMap_apply, allOnesMat, mul_one]
    rw [Fintype.sum_prod_type]
    have h1 : ∀ v1 : (Fin s → ZMod 2) × Fin (2 ^ s),
        (∑ _vt : Fin 2, K_coreMat ℝ s (x', w') v1) = 2 * K_coreMat ℝ s (x', w') v1 := by
      intro v1; simp [two_mul]
    simp_rw [h1, ← Finset.mul_sum]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    have h2 : ∀ z' : Fin (2 ^ s),
        (∑ y' : Fin s → ZMod 2, K_coreMat ℝ s (x', w') (y', z')) = 1 := by
      intro z'
      rw [Finset.sum_eq_single (x' + borrowVec s w' z')]
      · have hrel : K_coreRel s (x', w') (x' + borrowVec s w' z', z') := by
          simp only [K_coreRel, ← add_assoc, f2_vec_add_self, zero_add]
        simp [K_coreMat, hrel]
      · intro y' _ hy'
        have hnrel : ¬ K_coreRel s (x', w') (y', z') :=
          fun hr => hy' ((f2_vec_add_eq_iff s x' y' _).mp hr)
        simp [K_coreMat, hnrel]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    simp_rw [h2]
    simp [t, pow_succ, mul_comm]
  have hB_col : ∀ v : ((Fin s → ZMod 2) × Fin (2 ^ s)) × Fin 2,
      (∑ u : ((Fin s → ZMod 2) × Fin (2 ^ s)) × Fin 2, B_core u v) = (2 : ℝ) ^ t := by
    rintro ⟨⟨y', z'⟩, zt⟩
    simp only [B_core, Matrix.kroneckerMap_apply, allOnesMat, mul_one]
    rw [Fintype.sum_prod_type]
    have h1 : ∀ u1 : (Fin s → ZMod 2) × Fin (2 ^ s),
        (∑ _ut : Fin 2, K_coreMat ℝ s u1 (y', z')) = 2 * K_coreMat ℝ s u1 (y', z') := by
      intro u1; simp [two_mul]
    simp_rw [h1, ← Finset.mul_sum]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    have h2 : ∀ w' : Fin (2 ^ s),
        (∑ x' : Fin s → ZMod 2, K_coreMat ℝ s (x', w') (y', z')) = 1 := by
      intro w'
      rw [Finset.sum_eq_single (y' + borrowVec s w' z')]
      · have hrel : K_coreRel s (y' + borrowVec s w' z', w') (y', z') := by
          simp only [K_coreRel]
          rw [add_comm y' _, add_assoc, f2_vec_add_self, add_zero]
        simp [K_coreMat, hrel]
      · intro x' _ hx'
        have hnrel : ¬ K_coreRel s (x', w') (y', z') := by
          intro hr
          simp only [K_coreRel] at hr
          rw [add_comm] at hr
          exact hx' ((f2_vec_add_eq_iff s y' x' _).mp hr)
        simp [K_coreMat, hnrel]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    simp_rw [h2]
    simp [t, pow_succ, mul_comm]
  have hB_nonneg : ∀ u v, 0 ≤ B_core u v := by
    rintro ⟨u1, _⟩ ⟨v1, _⟩
    simp only [B_core, Matrix.kroneckerMap_apply, allOnesMat, mul_one, K_coreMat]
    split_ifs <;> norm_num
  have hM_row : ∀ r, (∑ c, M_re r c) = (2 : ℝ) ^ t := by
    rintro ⟨b, u⟩
    rw [Fintype.sum_prod_type, Finset.sum_eq_single b]
    · simp [M_re, hB_row u]
    · intro b' _ hb'; simp [M_re, Ne.symm hb']
    · intro hm; exact absurd (Finset.mem_univ b) hm
  have hM_col : ∀ c, (∑ r, M_re r c) = (2 : ℝ) ^ t := by
    rintro ⟨b, v⟩
    rw [Fintype.sum_prod_type, Finset.sum_eq_single b]
    · simp [M_re, hB_col v]
    · intro b' _ hb'; simp [M_re, hb']
    · intro hm; exact absurd (Finset.mem_univ b) hm
  have hM_nonneg : ∀ r c, 0 ≤ M_re r c := by
    rintro ⟨b1, u⟩ ⟨b2, v⟩
    simp only [M_re, Matrix.kroneckerMap_apply, Matrix.one_apply]
    split_ifs
    · simpa using hB_nonneg u v
    · norm_num
  have hN_card :
      (Fintype.card (Fin 2 × (((Fin s → ZMod 2) × Fin (2 ^ s)) × Fin 2)) : ℝ) =
        (2 : ℝ) ^ (2 * t) := by
    simp only [Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    push_cast
    have ht : 2 * t = 1 + s + s + 1 := by omega
    rw [ht]
    ring
  refine spectralNorm2_eq_of_le_and_witness C_M ((2 : ℝ) ^ t) (by positivity) ?_ ?_
  · intro x
    let N : ℝ := (2 : ℝ) ^ (2 * t)
    have hN_pos : 0 < N := by positivity
    let μ : ℝ := (∑ c, x c) / N
    let y : Fin 2 × (((Fin s → ZMod 2) × Fin (2 ^ s)) × Fin 2) → ℝ := fun c => x c - μ
    have hsum_y : ∑ c, y c = 0 := by
      simp only [y, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, hN_card]
      dsimp only [μ, N]
      field_simp [hN_pos.ne']
      ring
    have hCM_eq_My : C_M *ᵥ x = M_re *ᵥ y := by
      ext r
      have hlhs_r :
          (C_M *ᵥ x) r = (∑ c, M_re r c * x c) - ((2 : ℝ) ^ t)⁻¹ * (∑ c, x c) := by
        simp only [C_M, centeredMat, Matrix.mulVec, dotProduct, Matrix.sub_apply,
          Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mul_one, sub_mul,
          Finset.sum_sub_distrib, ← Finset.mul_sum]
      have hrhs_r :
          (M_re *ᵥ y) r = (∑ c, M_re r c * x c) - ((2 : ℝ) ^ t) * μ := by
        simp only [Matrix.mulVec, dotProduct, y, mul_sub, Finset.sum_sub_distrib,
          ← Finset.sum_mul, hM_row r]
      rw [hlhs_r, hrhs_r]
      dsimp only [μ, N]
      have h2t : (2 : ℝ) ^ t ≠ 0 := by positivity
      have hN_split : (2 : ℝ) ^ (2 * t) = (2 : ℝ) ^ t * (2 : ℝ) ^ t := by rw [two_mul, pow_add]
      rw [hN_split]
      field_simp [h2t]
    have hy_le_x : (l2Norm y) ^ 2 ≤ (l2Norm x) ^ 2 := by
      rw [sq_l2Norm, sq_l2Norm]
      have hdecomp : ∀ c, (x c) ^ 2 = (y c) ^ 2 + 2 * μ * y c + μ ^ 2 := by
        intro c; dsimp only [y]; ring
      simp_rw [hdecomp, Finset.sum_add_distrib, ← Finset.mul_sum, hsum_y, mul_zero, add_zero,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN_card]
      have hnn : 0 ≤ N * μ ^ 2 := mul_nonneg hN_pos.le (sq_nonneg μ)
      linarith
    have hMy_schur : (l2Norm (M_re *ᵥ y)) ^ 2 ≤ ((2 : ℝ) ^ t) ^ 2 * (l2Norm y) ^ 2 := by
      rw [sq_l2Norm, sq_l2Norm]
      have hrow_cs : ∀ r,
          ((M_re *ᵥ y) r) ^ 2 ≤ ((2 : ℝ) ^ t) * ∑ c, M_re r c * (y c) ^ 2 := by
        intro r
        simp only [Matrix.mulVec, dotProduct]
        have hrewrite :
            ∀ c, M_re r c * y c = Real.sqrt (M_re r c) * (Real.sqrt (M_re r c) * y c) := by
          intro c
          rw [← mul_assoc, Real.mul_self_sqrt (hM_nonneg r c)]
        simp_rw [hrewrite]
        have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
          (fun c => Real.sqrt (M_re r c)) (fun c => Real.sqrt (M_re r c) * y c)
        have hsq1 : (∑ c, (Real.sqrt (M_re r c)) ^ 2) = (2 : ℝ) ^ t := by
          rw [← hM_row r]
          exact Finset.sum_congr rfl fun c _ => Real.sq_sqrt (hM_nonneg r c)
        have hsq2 : (∑ c, (Real.sqrt (M_re r c) * y c) ^ 2) = ∑ c, M_re r c * (y c) ^ 2 := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [mul_pow, Real.sq_sqrt (hM_nonneg r c)]
        rw [hsq1, hsq2] at hcs
        exact hcs
      calc (∑ r, ((M_re *ᵥ y) r) ^ 2)
          ≤ ∑ r, (2 : ℝ) ^ t * ∑ c, M_re r c * (y c) ^ 2 := Finset.sum_le_sum fun r _ => hrow_cs r
        _ = (2 : ℝ) ^ t * ∑ c, (∑ r, M_re r c) * (y c) ^ 2 := by
            rw [← Finset.mul_sum, Finset.sum_comm]
            congr 1
            refine Finset.sum_congr rfl fun c _ => by rw [Finset.sum_mul]
        _ = ((2 : ℝ) ^ t) ^ 2 * ∑ c, (y c) ^ 2 := by
            simp_rw [hM_col]
            rw [← Finset.mul_sum]
            ring
    have htot : (l2Norm (C_M *ᵥ x)) ^ 2 ≤ ((2 : ℝ) ^ t * l2Norm x) ^ 2 := by
      rw [hCM_eq_My, mul_pow]
      exact hMy_schur.trans (mul_le_mul_of_nonneg_left hy_le_x (sq_nonneg _))
    nlinarith [l2Norm_nonneg (C_M *ᵥ x),
      mul_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ t) (l2Norm_nonneg x)]
  · right
    let x_anti : Fin 2 × (((Fin s → ZMod 2) × Fin (2 ^ s)) × Fin 2) → ℝ :=
      fun ⟨b, _⟩ => if b.val = 0 then 1 else -1
    have hx_sum0 : ∑ c, x_anti c = 0 := by
      rw [Fintype.sum_prod_type]
      have hb0 : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
      rw [hb0, Finset.sum_pair (by decide)]
      simp [x_anti]
    have hx_norm_sq : (l2Norm x_anti) ^ 2 = (2 : ℝ) ^ (2 * t) := by
      rw [sq_l2Norm]
      have h1 : ∀ c, (x_anti c) ^ 2 = 1 := by
        rintro ⟨b, _⟩; fin_cases b <;> simp [x_anti]
      simp_rw [h1]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hN_card]
    have hx_ne : l2Norm x_anti ≠ 0 := by
      intro h0; rw [h0, zero_pow (by decide)] at hx_norm_sq
      linarith [(by positivity : (0 : ℝ) < (2 : ℝ) ^ (2 * t))]
    refine ⟨x_anti, hx_ne, ?_⟩
    have hCx : C_M *ᵥ x_anti = ((2 : ℝ) ^ t) • x_anti := by
      ext ⟨b, u⟩
      have hlhs :
          (C_M *ᵥ x_anti) (b, u) =
            (∑ c, M_re (b, u) c * x_anti c) - ((2 : ℝ) ^ t)⁻¹ * (∑ c, x_anti c) := by
        simp only [C_M, centeredMat, Matrix.mulVec, dotProduct, Matrix.sub_apply,
          Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mul_one, sub_mul,
          Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [hlhs, hx_sum0, mul_zero, sub_zero, Pi.smul_apply, smul_eq_mul,
        Fintype.sum_prod_type, Finset.sum_eq_single b]
      · have hcell : ∀ x, M_re (b, u) (b, x) * x_anti (b, x) =
            B_core u x * (if b.val = 0 then (1 : ℝ) else -1) := by
          intro x
          simp [M_re, x_anti]
        simp_rw [hcell, ← Finset.sum_mul, hB_row u]
        simp [x_anti]
      · intro b' _ hb'
        simp [M_re, Matrix.kroneckerMap_apply, Ne.symm hb']
      · intro hm; exact absurd (Finset.mem_univ b) hm
    rw [hCx, l2Norm_smul, abs_of_pos (by positivity)]

/-! ### 5. Overlap-Safe Centered Spectral Cover Inequality & Exponential Separation (Remark 4.3) -/

/-- Number of edges `|E(R)|` of a finite binary relation `R : α → β → Prop`. -/
def relEdgeCount {α β : Type*} [Fintype α] [Fintype β]
    (R : α → β → Prop) [∀ r c, Decidable (R r c)] : ℕ :=
  ((Finset.univ : Finset (α × β)).filter fun rc => R rc.1 rc.2).card

/-- `{0, 1}`-biadjacency matrix `M_R ∈ {0, 1}^{α × β}` over `ℝ`. -/
def relBiadjMat {α β : Type*} (R : α → β → Prop) [∀ r c, Decidable (R r c)] :
    Matrix α β ℝ :=
  fun r c => if R r c then 1 else 0

lemma relEdgeCount_le_card_mul {α β : Type*} [Fintype α] [Fintype β]
    (R : α → β → Prop) [∀ r c, Decidable (R r c)] :
    relEdgeCount R ≤ Fintype.card α * Fintype.card β := by
  unfold relEdgeCount
  calc ((Finset.univ : Finset (α × β)).filter fun rc => R rc.1 rc.2).card
      ≤ (Finset.univ : Finset (α × β)).card := Finset.card_filter_le _ _
    _ = Fintype.card α * Fintype.card β := by simp

lemma relEdgeCount_le_sum_biclique_areas {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {R : α → β → Prop} [∀ r c, Decidable (R r c)]
    (C : ExactBicliqueCover R) :
    relEdgeCount R ≤ ∑ ℓ : C.L, (C.U ℓ).card * (C.V ℓ).card := by
  have hsub :
      ((Finset.univ : Finset (α × β)).filter fun rc => R rc.1 rc.2) ⊆
        Finset.univ.biUnion (fun ℓ : C.L => C.U ℓ ×ˢ C.V ℓ) := by
    rintro ⟨r, c⟩ hrc
    have hR : R r c := (Finset.mem_filter.mp hrc).2
    obtain ⟨ℓ, hr, hc⟩ := C.covers r c hR
    exact Finset.mem_biUnion.mpr ⟨ℓ, Finset.mem_univ ℓ, Finset.mem_product.mpr ⟨hr, hc⟩⟩
  calc relEdgeCount R
      ≤ (Finset.univ.biUnion fun ℓ : C.L => C.U ℓ ×ˢ C.V ℓ).card := Finset.card_le_card hsub
    _ ≤ ∑ ℓ : C.L, (C.U ℓ ×ˢ C.V ℓ).card := Finset.card_biUnion_le
    _ = ∑ ℓ : C.L, (C.U ℓ).card * (C.V ℓ).card := by simp [Finset.card_product]

/-- **Remark 4.3, Part 1 (Overlap-Safe Centered Spectral Cover Inequality)**:
For ANY `{0, 1}`-relation `R` on `α × β`, ANY `p ≤ 1` (in particular edge density
`p = |E| / (|α| |β|)`), ANY centered spectral bound `0 ≤ Λ` satisfying
`∀ x y, |⟨x, (M_R - p 1 1ᵀ) y⟩| ≤ Λ ‖x‖₂ ‖y‖₂`, and ANY (possibly overlapping) exact biclique
cover `C` of `R`,
`2 (1 - p) |E| ≤ Λ · C.labelWeight` (Paper 2, Remark 4.3). -/
theorem centered_spectral_biclique_cover_mul_le {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {R : α → β → Prop} [∀ r c, Decidable (R r c)]
    {p Λ : ℝ} (hp1 : p ≤ 1) (hΛ0 : 0 ≤ Λ)
    (hspec : ∀ (x : α → ℝ) (y : β → ℝ),
      |dotProduct x (centeredMat (relBiadjMat R) p *ᵥ y)| ≤ Λ * l2Norm x * l2Norm y)
    (C : ExactBicliqueCover R) :
    2 * (1 - p) * (relEdgeCount R : ℝ) ≤ Λ * (C.labelWeight : ℝ) := by
  have hrect :
      ∀ ℓ : C.L,
        2 * (1 - p) * (((C.U ℓ).card : ℝ) * ((C.V ℓ).card : ℝ)) ≤
          Λ * (((C.U ℓ).card : ℝ) + ((C.V ℓ).card : ℝ)) := by
    intro ℓ
    let u : α → ℝ := fun r => if r ∈ C.U ℓ then 1 else 0
    let v : β → ℝ := fun c => if c ∈ C.V ℓ then 1 else 0
    set a : ℝ := ((C.U ℓ).card : ℝ)
    set b : ℝ := ((C.V ℓ).card : ℝ)
    have ha0 : 0 ≤ a := Nat.cast_nonneg _
    have hb0 : 0 ≤ b := Nat.cast_nonneg _
    have hu_sum : ∑ r : α, u r = a := by
      simp [u, a]
    have hv_sum : ∑ c : β, v c = b := by
      simp [v, b]
    have hu_norm : l2Norm u = Real.sqrt a := by
      unfold l2Norm
      congr 1
      have hsq_u : ∀ r : α, (u r) ^ 2 = u r := by intro r; dsimp [u]; split_ifs <;> ring
      simp_rw [hsq_u, hu_sum]
    have hv_norm : l2Norm v = Real.sqrt b := by
      unfold l2Norm
      congr 1
      have hsq_v : ∀ c : β, (v c) ^ 2 = v c := by intro c; dsimp [v]; split_ifs <;> ring
      simp_rw [hsq_v, hv_sum]
    have hquad_M : dotProduct u (relBiadjMat R *ᵥ v) = a * b := by
      simp only [dotProduct, Matrix.mulVec]
      have hrow_u :
          ∀ r : α,
            u r * (∑ c : β, relBiadjMat R r c * v c) = if r ∈ C.U ℓ then b else 0 := by
        intro r
        by_cases hr : r ∈ C.U ℓ
        · simp only [u, hr, ↓reduceIte, one_mul]
          have hcol_v : ∀ c : β, relBiadjMat R r c * v c = v c := by
            intro c
            by_cases hc : c ∈ C.V ℓ
            · have hR : R r c := C.isBiclique ℓ r hr c hc
              simp [relBiadjMat, v, hc, hR]
            · simp [v, hc]
          simp_rw [hcol_v, hv_sum]
        · simp [u, hr]
      simp_rw [hrow_u]
      simp [a]
    have hquad_ones :
        dotProduct u ((p • Matrix.of (fun (_ : α) (_ : β) => (1 : ℝ))) *ᵥ v) = p * (a * b) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul,
        mul_one, ← Finset.mul_sum, hv_sum]
      have h1 : ∀ r : α, u r * (p * b) = (p * b) * u r := fun r => mul_comm _ _
      simp_rw [h1, ← Finset.mul_sum, hu_sum]
      ring
    have hquad_cent :
        dotProduct u (centeredMat (relBiadjMat R) p *ᵥ v) = (1 - p) * (a * b) := by
      unfold centeredMat
      rw [Matrix.sub_mulVec, dotProduct_sub, hquad_M, hquad_ones]
      ring
    have hcs_bound : (1 - p) * (a * b) ≤ Λ * Real.sqrt a * Real.sqrt b := by
      calc (1 - p) * (a * b)
          ≤ |(1 - p) * (a * b)| := le_abs_self _
        _ = |dotProduct u (centeredMat (relBiadjMat R) p *ᵥ v)| := by rw [hquad_cent]
        _ ≤ Λ * l2Norm u * l2Norm v := hspec u v
        _ = Λ * Real.sqrt a * Real.sqrt b := by rw [hu_norm, hv_norm]
    have ham_gm : 2 * (Real.sqrt a * Real.sqrt b) ≤ a + b := by
      have hsq : 0 ≤ (Real.sqrt a - Real.sqrt b) ^ 2 := sq_nonneg _
      have hexp : (Real.sqrt a - Real.sqrt b) ^ 2 = a + b - 2 * (Real.sqrt a * Real.sqrt b) := by
        calc (Real.sqrt a - Real.sqrt b) ^ 2
            = (Real.sqrt a) ^ 2 + (Real.sqrt b) ^ 2 - 2 * (Real.sqrt a * Real.sqrt b) := by ring
          _ = a + b - 2 * (Real.sqrt a * Real.sqrt b) := by
                rw [Real.sq_sqrt ha0, Real.sq_sqrt hb0]
      linarith
    calc 2 * (1 - p) * (a * b)
        = 2 * ((1 - p) * (a * b)) := by ring
      _ ≤ 2 * (Λ * Real.sqrt a * Real.sqrt b) := by linarith
      _ = Λ * (2 * (Real.sqrt a * Real.sqrt b)) := by ring
      _ ≤ Λ * (a + b) := mul_le_mul_of_nonneg_left ham_gm hΛ0
  have hcover_cast :
      (relEdgeCount R : ℝ) ≤ ∑ ℓ : C.L, ((C.U ℓ).card : ℝ) * ((C.V ℓ).card : ℝ) := by
    exact_mod_cast relEdgeCount_le_sum_biclique_areas C
  have h1p_nn : 0 ≤ 1 - p := by linarith
  calc 2 * (1 - p) * (relEdgeCount R : ℝ)
      ≤ 2 * (1 - p) * (∑ ℓ : C.L, ((C.U ℓ).card : ℝ) * ((C.V ℓ).card : ℝ)) :=
        mul_le_mul_of_nonneg_left hcover_cast (by positivity)
    _ = ∑ ℓ : C.L, 2 * (1 - p) * (((C.U ℓ).card : ℝ) * ((C.V ℓ).card : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ ℓ : C.L, Λ * (((C.U ℓ).card : ℝ) + ((C.V ℓ).card : ℝ)) :=
        Finset.sum_le_sum fun ℓ _ => hrect ℓ
    _ = Λ * (C.labelWeight : ℝ) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
        simp [ExactBicliqueCover.labelWeight, ExactBicliqueCover.totalRowLoad,
          ExactBicliqueCover.totalColLoad]

/-- Division form `W_label ≥ 2(1 - p)|E| / Λ(M)` with edge density `p = |E| / (|α| |β|)`
(Paper 2, Remark 4.3). -/
theorem centered_spectral_biclique_cover_div_le {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {R : α → β → Prop} [∀ r c, Decidable (R r c)]
    (C : ExactBicliqueCover R)
    (hΛ_pos :
      0 < spectralNorm2 (centeredMat (relBiadjMat R)
        ((relEdgeCount R : ℝ) / ((Fintype.card α : ℝ) * (Fintype.card β : ℝ))))) :
    let p := (relEdgeCount R : ℝ) / ((Fintype.card α : ℝ) * (Fintype.card β : ℝ))
    let Λ := spectralNorm2 (centeredMat (relBiadjMat R) p)
    2 * (1 - p) * (relEdgeCount R : ℝ) / Λ ≤ (C.labelWeight : ℝ) := by
  intro p Λ
  have hp1 : p ≤ 1 := by
    dsimp only [p]
    by_cases hcard0 : (Fintype.card α : ℝ) * (Fintype.card β : ℝ) = 0
    · rw [hcard0, div_zero]; norm_num
    · have hpos : 0 < (Fintype.card α : ℝ) * (Fintype.card β : ℝ) :=
        lt_of_le_of_ne (by positivity) (Ne.symm hcard0)
      rw [div_le_one hpos]
      exact_mod_cast relEdgeCount_le_card_mul R
  rw [div_le_iff₀ hΛ_pos, mul_comm (C.labelWeight : ℝ) Λ]
  exact centered_spectral_biclique_cover_mul_le hp1 hΛ_pos.le
    (abs_dotProduct_mulVec_le_spectralNorm2 (centeredMat (relBiadjMat R) p)) C

/-- Exact edge count `|E(K_{s+1})| = 2^{3s}`. -/
theorem relEdgeCount_K_coreRel (s : ℕ) :
    relEdgeCount (K_coreRel s) = 2 ^ (3 * s) := by
  unfold relEdgeCount
  let e : ((Fin s → ZMod 2) × Fin (2 ^ s)) × Fin (2 ^ s) ≃
      { rc : ((Fin s → ZMod 2) × Fin (2 ^ s)) × ((Fin s → ZMod 2) × Fin (2 ^ s)) //
          K_coreRel s rc.1 rc.2 } :=
    { toFun := fun ⟨⟨x', w'⟩, z'⟩ =>
        ⟨((x', w'), (x' + borrowVec s w' z', z')), by
          simp only [K_coreRel, ← add_assoc, f2_vec_add_self, zero_add]⟩
      invFun := fun ⟨⟨⟨x', w'⟩, ⟨_, z'⟩⟩, _⟩ => ((x', w'), z')
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := by
        rintro ⟨⟨⟨x', w'⟩, ⟨y', z'⟩⟩, hrel⟩
        have hy : y' = x' + borrowVec s w' z' := (f2_vec_add_eq_iff s x' y' _).mp hrel
        subst hy
        rfl }
  rw [← Fintype.card_subtype, ← Fintype.card_congr e]
  simp only [Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  ring_nf

/-- **Remark 4.3, Part 2 (Instantiation on `C_t` for `t = s + 1 ≥ 2`)**:
The centered spectral cover bound on `C_t` (`p = 2^{-s}`, `|E| = 2^{3s}`, `Λ = 2^{s - 1/2}`)
yields `W_label ≥ 2√2 (1 - 2^{-s}) 2^{2s}`! -/
theorem K_coreRel_spectral_cover_lower_bound {s : ℕ} (hs : 1 ≤ s)
    (C : ExactBicliqueCover (K_coreRel s)) :
    2 * Real.sqrt 2 * (1 - ((2 : ℝ) ^ s)⁻¹) * (2 : ℝ) ^ (2 * s) ≤ (C.labelWeight : ℝ) := by
  have hM_eq : relBiadjMat (K_coreRel s) = K_coreMat ℝ s := rfl
  have hp_le1 : ((2 : ℝ) ^ s)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hgap := centeredSpectralGap_K_core hs
  rw [← hM_eq] at hgap
  set Λ := (2 : ℝ) ^ ((s : ℝ) - 1 / 2)
  have hΛ_pos : 0 < Λ := by positivity
  have hmul := centered_spectral_biclique_cover_mul_le (p := ((2 : ℝ) ^ s)⁻¹) (Λ := Λ)
    hp_le1 hΛ_pos.le
    (fun x y => by rw [← hgap]; exact abs_dotProduct_mulVec_le_spectralNorm2 _ x y) C
  rw [relEdgeCount_K_coreRel] at hmul
  have hΛ_eq : Λ = (2 : ℝ) ^ s / Real.sqrt 2 := by
    dsimp only [Λ]
    have h2_pos : (0 : ℝ) < 2 := by positivity
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast 2 s, ← Real.rpow_sub h2_pos]
  have halg :
      2 * (1 - ((2 : ℝ) ^ s)⁻¹) * ((2 ^ (3 * s) : ℕ) : ℝ) / Λ =
        2 * Real.sqrt 2 * (1 - ((2 : ℝ) ^ s)⁻¹) * (2 : ℝ) ^ (2 * s) := by
    rw [hΛ_eq]
    push_cast
    have h2s_ne : (2 : ℝ) ^ s ≠ 0 := by positivity
    have hsq2_ne : Real.sqrt 2 ≠ 0 := by positivity
    have h3s : (2 : ℝ) ^ (3 * s) = (2 : ℝ) ^ s * (2 : ℝ) ^ (2 * s) := by
      rw [← pow_add]; congr 1; omega
    rw [h3s]
    field_simp [h2s_ne, hsq2_ne]
  rw [← halg, div_le_iff₀ hΛ_pos]
  linarith

/-- Normalized per-vertex spectral degree lower bound on `C_t`:
`E[|A| + |B|] = W_label / 2^{2s} ≥ 2√2 (1 - 2^{-s})` (Paper 2, Remark 4.3). -/
theorem K_coreRel_spectral_avg_degree_lower_bound {s : ℕ} (hs : 1 ≤ s)
    (C : ExactBicliqueCover (K_coreRel s)) :
    2 * Real.sqrt 2 * (1 - ((2 : ℝ) ^ s)⁻¹) ≤ (C.labelWeight : ℝ) / (2 : ℝ) ^ (2 * s) := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (2 * s) := by positivity
  rw [le_div_iff₀ hpos]
  exact K_coreRel_spectral_cover_lower_bound hs C

/-- **Remark 4.3, Exponential Separation (`O(1)` Spectral Bound vs `Θ(2^{s/2})` Cocycle Bound)**:
The centered spectral lower bound `2√2 (1 - 2^{-s})` is uniformly bounded above by `2√2 = O(1)`,
whereas the cocycle bound `2^{⌊s/2⌋} + 2^{⌈s/2⌉}` grows exponentially as `≥ (2^{s/2} / √2)` times
the spectral bound. -/
theorem spectral_vs_cocycle_exponential_separation (s : ℕ) :
    2 * Real.sqrt 2 * (1 - ((2 : ℝ) ^ s)⁻¹) < 2 * Real.sqrt 2 ∧
      (1 ≤ s →
        (2 : ℝ) ^ (s / 2) * (2 * Real.sqrt 2 * (1 - ((2 : ℝ) ^ s)⁻¹)) ≤
          Real.sqrt 2 * (((2 ^ (s / 2) + 2 ^ ((s + 1) / 2) : ℕ) : ℝ))) := by
  have hinv_pos : (0 : ℝ) < ((2 : ℝ) ^ s)⁻¹ := by positivity
  have hsq2_pos : (0 : ℝ) < Real.sqrt 2 := by positivity
  refine ⟨by nlinarith, fun _hs => ?_⟩
  push_cast
  have hceil_ge : (2 : ℝ) ^ (s / 2) ≤ (2 : ℝ) ^ ((s + 1) / 2) :=
    pow_le_pow_right₀ (by norm_num) (Nat.div_le_div_right (Nat.le_succ s))
  have h1 : 1 - ((2 : ℝ) ^ s)⁻¹ ≤ 1 := by linarith
  have h2pow_pos : (0 : ℝ) ≤ (2 : ℝ) ^ (s / 2) := by positivity
  calc (2 : ℝ) ^ (s / 2) * (2 * Real.sqrt 2 * (1 - ((2 : ℝ) ^ s)⁻¹))
      ≤ (2 : ℝ) ^ (s / 2) * (2 * Real.sqrt 2 * 1) :=
        mul_le_mul_of_nonneg_left (by nlinarith) h2pow_pos
    _ = Real.sqrt 2 * ((2 : ℝ) ^ (s / 2) + (2 : ℝ) ^ (s / 2)) := by ring
    _ ≤ Real.sqrt 2 * ((2 : ℝ) ^ (s / 2) + (2 : ℝ) ^ ((s + 1) / 2)) :=
        mul_le_mul_of_nonneg_left (by linarith) hsq2_pos.le

end CarryAutomaton


