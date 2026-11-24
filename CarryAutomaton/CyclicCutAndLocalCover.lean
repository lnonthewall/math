module

public import CarryAutomaton.Defs
public import CarryAutomaton.CoreBicliques
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.BitVec
import Mathlib.Tactic

@[expose] public section

/-!
# Optimal Cyclic Carry-Cut Partitions, Cover Invariants, and Local Cover Numbers

Formalization of Section 2 (Lemma 2.2, Definition 2.3, Theorem 2.4), Section 3 (Theorem 3.2,
Proposition 3.3), and Appendix A (Proposition A.1) of Paper 2 (where the borrow core `C_t` is
formalized as `K_coreRel s` with `s = t - 1`, and the cyclic carry-cut partition `𝒫_m` is named
`mechanismIICStar`):
1. Lemma 2.2: Modular-quotient carry identity (both `c_in = 0` and general `c_in ∈ {0, 1}`),
   bit-parallel borrow formula, and two's-complement trailing-zero wrap mask (`BitVec`).
2. Definition 2.3 & Theorem 2.4(a): Cyclic carry-cut partition family `𝒫_m` (`mechanismIICStar`)
   of exact zero-duplicate biclique partitions of `M_t` (and projected core partitions of `C_t`)
   with `2^(2t-1)` keys, constant row load `2^(t-1-m)`, constant column load `2^m`, and exact
   biclique sizes `|U_ℓ| = 2^(t-m)` and `|V_ℓ| = 2^(m+1)`.
3. Theorem 2.4(b): Exact optimality across ALL exact biclique covers of `M_t` (and `C_t`) for
   label count `bc = cp = 2^(2t-1)`, degree product `totalRowLoad * totalColLoad ≥ 2^(5t-1)`,
   and all weighted sums `α * totalRowLoad + β * totalColLoad ≥ min_m (α * 2^(t-1-m) + β * 2^m) * 2^(2t)`.
4. Theorem 3.2: Exact local biclique cover and partition numbers
   `lbc(C_t) = lbp(C_t) = lbc(M_t) = lbp(M_t) = ⌈(2^⌊s/2⌋ + 2^⌈s/2⌉)/2⌉` for all `t ≥ 1`,
   including the general non-equivariant lift-colored balanced 4-star blowup partition for all
   odd `s = 2r + 1` (`r ≥ 1`).
5. Proposition 3.3 & Appendix A Proposition A.1: Kernel-verified (`decide`) `s = 3` equivariant
   grid obstruction certifying `48` maximal `(2,4)/(4,2)` rectangles, exactly `50` disjoint
   tilings of `{0..7}²` (distribution `(5, 12, 16, 12, 5)`), and `0` tilings (hence `0`
   `𝔽₂³`-equivariant covers of `C_4`) with maximum vertex load `≤ 3`.
-/

namespace CarryAutomaton

open Finset BigOperators

/-! ### Lemma 2.2: Modular-Quotient Carry Identity, Bit-Parallel Borrow, and Wrap Mask -/

/-- `i`-bit borrow indicator with incoming carry `c_in ∈ {0, 1}`:
`c_i(w, z; c_in) = 1[(w mod 2^i) + c_in > (z mod 2^i)]` in `ZMod 2`. -/
def borrowBitCin (i w z c_in : ℕ) : ZMod 2 :=
  if z % 2 ^ i < w % 2 ^ i + c_in then 1 else 0

/-- Generalized Lemma 2.2 (Modular-Quotient Carry Identity with incoming carry `c_in ∈ {0, 1}`):
for `0 ≤ m ≤ s`, `h = s - m`, `1 ≤ j ≤ h`, `w, z < 2^s`, `c_in ≤ 1`,
splitting `w = w_lo + 2^m w_hi`, `z = z_lo + 2^m z_hi`, `c_m = 1[w_lo + c_in > z_lo]`,
and `q = (z_hi - c_m) mod 2^h`:
`c_{m+j}(w, z; c_in) = c_j(w_hi, q) ⊕ 1[c_m = 1 ∧ z_hi ≡ 0 (mod 2^j)]`. -/
theorem modular_quotient_carry_identity_cin {s m j w z c_in : ℕ}
    (hm : m ≤ s) (hj1 : 1 ≤ j) (hjh : j ≤ s - m)
    (hw : w < 2 ^ s) (hz : z < 2 ^ s) (hc : c_in ≤ 1) :
    let h := s - m
    let w_lo := w % 2 ^ m
    let w_hi := w / 2 ^ m
    let z_lo := z % 2 ^ m
    let z_hi := z / 2 ^ m
    let c_m : ℕ := if z_lo < w_lo + c_in then 1 else 0
    let q := (z_hi + 2 ^ h - c_m) % 2 ^ h
    borrowBitCin (m + j) w z c_in =
      borrowBit j w_hi q + if c_m = 1 ∧ z_hi % 2 ^ j = 0 then (1 : ZMod 2) else 0 := by
  dsimp only
  set h := s - m
  set w_lo := w % 2 ^ m
  set w_hi := w / 2 ^ m
  set z_lo := z % 2 ^ m
  set z_hi := z / 2 ^ m
  set c_m : ℕ := if z_lo < w_lo + c_in then 1 else 0
  set q := (z_hi + 2 ^ h - c_m) % 2 ^ h
  have hpow_m : 0 < 2 ^ m := by positivity
  have hpow_j : 0 < 2 ^ j := by positivity
  have hpow_h : 0 < 2 ^ h := by positivity
  have hw_lo_lt : w_lo < 2 ^ m := Nat.mod_lt _ hpow_m
  have hz_lo_lt : z_lo < 2 ^ m := Nat.mod_lt _ hpow_m
  have hpow_s : 2 ^ s = 2 ^ m * 2 ^ h := by rw [← pow_add, Nat.add_sub_of_le hm]
  have hw_hi_lt : w_hi < 2 ^ h := Nat.div_lt_of_lt_mul (by linarith)
  have hz_hi_lt : z_hi < 2 ^ h := Nat.div_lt_of_lt_mul (by linarith)
  have hdvd_jh : 2 ^ j ∣ 2 ^ h := Nat.pow_dvd_pow 2 hjh
  have hw_split : w % 2 ^ (m + j) = 2 ^ m * (w_hi % 2 ^ j) + w_lo := by
    have h1 : w % 2 ^ (m + j) / 2 ^ m = w_hi % 2 ^ j := by
      rw [pow_add, mul_comm (2 ^ m) (2 ^ j), Nat.mod_mul_left_div_self]
    have h2 : w % 2 ^ (m + j) % 2 ^ m = w_lo :=
      Nat.mod_mod_of_dvd w (Nat.pow_dvd_pow 2 (by omega))
    have h3 := Nat.div_add_mod (w % 2 ^ (m + j)) (2 ^ m)
    rw [h1, h2] at h3
    exact h3.symm
  have hz_split : z % 2 ^ (m + j) = 2 ^ m * (z_hi % 2 ^ j) + z_lo := by
    have h1 : z % 2 ^ (m + j) / 2 ^ m = z_hi % 2 ^ j := by
      rw [pow_add, mul_comm (2 ^ m) (2 ^ j), Nat.mod_mul_left_div_self]
    have h2 : z % 2 ^ (m + j) % 2 ^ m = z_lo :=
      Nat.mod_mod_of_dvd z (Nat.pow_dvd_pow 2 (by omega))
    have h3 := Nat.div_add_mod (z % 2 ^ (m + j)) (2 ^ m)
    rw [h1, h2] at h3
    exact h3.symm
  unfold borrowBitCin borrowBit
  rw [hw_split, hz_split]
  set a := w_hi % 2 ^ j
  set b := z_hi % 2 ^ j
  have ha_lt : a < 2 ^ j := Nat.mod_lt _ hpow_j
  have hb_lt : b < 2 ^ j := Nat.mod_lt _ hpow_j
  by_cases hcm : z_lo < w_lo + c_in
  · have hcm1 : c_m = 1 := by simp [c_m, hcm]
    by_cases hb0 : b = 0
    · -- Case 3: c_m = 1 and b = 0
      have hq_mod : q % 2 ^ j = 2 ^ j - 1 := by
        have h1 : q % 2 ^ j = (z_hi + 2 ^ h - 1) % 2 ^ j := by
          simp only [q, hcm1]
          exact Nat.mod_mod_of_dvd _ hdvd_jh
        rw [h1]
        rcases hdvd_jh with ⟨r, hr⟩
        have hz_dvd : 2 ^ j ∣ z_hi := Nat.dvd_of_mod_eq_zero hb0
        rcases hz_dvd with ⟨u, hu⟩
        have hr1 : 1 ≤ r := by rw [hr] at hpow_h; nlinarith
        have heq : z_hi + 2 ^ h - 1 = (2 ^ j - 1) + (u + r - 1) * 2 ^ j := by
          have hsum : z_hi + 2 ^ h = (u + r) * 2 ^ j := by
            rw [hu, hr]; ring
          have hsplit : (u + r) * 2 ^ j = 2 ^ j + (u + r - 1) * 2 ^ j := by
            calc (u + r) * 2 ^ j = (1 + (u + r - 1)) * 2 ^ j := by congr 1; omega
              _ = 2 ^ j + (u + r - 1) * 2 ^ j := by ring
          omega
        rw [heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      have hlhs : z_lo < 2 ^ m * a + w_lo + c_in := by
        have : 0 ≤ 2 ^ m * a := Nat.zero_le _
        omega
      have hrhs : ¬ (q % 2 ^ j < a) := by rw [hq_mod]; omega
      simp [hlhs, hrhs, hcm1, hb0]
    · -- Case 2: c_m = 1 and b ≥ 1
      have hb_pos : 1 ≤ b := by omega
      have hzhi_pos : 1 ≤ z_hi := by
        have := Nat.mod_le z_hi (2 ^ j); omega
      have hq_eq : q = z_hi - 1 := by
        simp only [q, hcm1]
        have hsub : z_hi + 2 ^ h - 1 = (z_hi - 1) + 2 ^ h := by omega
        rw [hsub, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have hq_mod : q % 2 ^ j = b - 1 := by
        rw [hq_eq]
        have hdiv := Nat.div_add_mod z_hi (2 ^ j)
        have heq : z_hi - 1 = (b - 1) + (z_hi / 2 ^ j) * 2 ^ j := by
          have : 2 ^ j * (z_hi / 2 ^ j) = (z_hi / 2 ^ j) * 2 ^ j := mul_comm _ _
          omega
        rw [heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      have hiff : 2 ^ m * b + z_lo < 2 ^ m * a + w_lo + c_in ↔ b - 1 < a := by
        constructor
        · intro hlt
          by_contra hnot
          have hab : a + 1 ≤ b := by omega
          have hmul : 2 ^ m * (a + 1) ≤ 2 ^ m * b := Nat.mul_le_mul_left _ hab
          have : 2 ^ m * (a + 1) = 2 ^ m * a + 2 ^ m := by ring
          omega
        · intro hba
          have hmul : 2 ^ m * b ≤ 2 ^ m * a := Nat.mul_le_mul_left _ (by omega)
          omega
      rw [hq_mod]
      simp only [hcm1, hb0, and_false, ↓reduceIte, add_zero]
      by_cases hba : b - 1 < a
      · simp [hba, hiff.mpr hba]
      · have hn : ¬ (2 ^ m * b + z_lo < 2 ^ m * a + w_lo + c_in) := fun h => hba (hiff.mp h)
        simp [hba, hn]
  · -- Case 1: c_m = 0
    have hcm0 : c_m = 0 := by simp [c_m, hcm]
    have hq_eq : q = z_hi := by
      simp only [q, hcm0, Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt hz_hi_lt]
    have hiff : 2 ^ m * b + z_lo < 2 ^ m * a + w_lo + c_in ↔ b < a := by
      constructor
      · intro hlt
        by_contra hnot
        have hmul : 2 ^ m * a ≤ 2 ^ m * b := Nat.mul_le_mul_left _ (by omega)
        omega
      · intro hba
        have hmul : 2 ^ m * (b + 1) ≤ 2 ^ m * a := Nat.mul_le_mul_left _ (by omega)
        have : 2 ^ m * (b + 1) = 2 ^ m * b + 2 ^ m := by ring
        omega
    rw [hq_eq]
    simp only [hcm0, zero_ne_one, false_and, ↓reduceIte, add_zero]
    change (if 2 ^ m * b + z_lo < 2 ^ m * a + w_lo + c_in then (1 : ZMod 2) else 0) =
      if b < a then 1 else 0
    by_cases hba : b < a
    · simp only [hba, hiff.mpr hba, ↓reduceIte]
    · have hn : ¬ (2 ^ m * b + z_lo < 2 ^ m * a + w_lo + c_in) := fun h => hba (hiff.mp h)
      simp only [hba, hn, ↓reduceIte]

/-- Lemma 2.2 (Modular-Quotient Carry Identity, `c_in = 0` specialization, Equation (2.7) of Paper 2). -/
theorem modular_quotient_carry_identity {s m j w z : ℕ}
    (hm : m ≤ s) (hj1 : 1 ≤ j) (hjh : j ≤ s - m)
    (hw : w < 2 ^ s) (hz : z < 2 ^ s) :
    let h := s - m
    let w_lo := w % 2 ^ m
    let w_hi := w / 2 ^ m
    let z_lo := z % 2 ^ m
    let z_hi := z / 2 ^ m
    let c_m : ℕ := if z_lo < w_lo then 1 else 0
    let q := (z_hi + 2 ^ h - c_m) % 2 ^ h
    borrowBit (m + j) w z =
      borrowBit j w_hi q + if c_m = 1 ∧ z_hi % 2 ^ j = 0 then (1 : ZMod 2) else 0 := by
  simpa [borrowBitCin, borrowBit] using
    modular_quotient_carry_identity_cin hm hj1 hjh hw hz (by omega : 0 ≤ 1)

/-- Bit-parallel `(k + 1)`-bit carry/borrow word:
`C_{[0..k]}(a, b) = (a ⊕ b ⊕ ((b - a) mod 2^(k+1))) mod 2^(k+1)`. -/
def bitParallelBorrow (k a b : ℕ) : ℕ :=
  (a ^^^ b ^^^ ((b + 2 ^ (k + 1) - a) % 2 ^ (k + 1))) % 2 ^ (k + 1)

lemma bitParallelBorrow_lt (k a b : ℕ) : bitParallelBorrow k a b < 2 ^ (k + 1) :=
  Nat.mod_lt _ (by positivity)

/-- Exact bitwise characterization of `bitParallelBorrow k a b` for all `k ≥ 0`, `a, b < 2^k`,
and `0 ≤ j ≤ k` (including `k = 0` and `j = 0`):
bit `j` equals `1[(a mod 2^j) > (b mod 2^j)]`. -/
theorem bitParallelBorrow_testBit {k a b j : ℕ}
    (ha : a < 2 ^ k) (hb : b < 2 ^ k) (hj : j ≤ k) :
    (bitParallelBorrow k a b).testBit j = decide (b % 2 ^ j < a % 2 ^ j) := by
  have ha1 : a < 2 ^ (k + 1) := lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (by omega))
  have hb1 : b < 2 ^ (k + 1) := lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) (by omega))
  set d := (b + 2 ^ (k + 1) - a) % 2 ^ (k + 1)
  have hd : d < 2 ^ (k + 1) := Nat.mod_lt _ (by positivity)
  have hadd : (d + a) % 2 ^ (k + 1) = b := by
    have h1 : (d + a) % 2 ^ (k + 1) = (b + 2 ^ (k + 1) - a + a) % 2 ^ (k + 1) := by
      simp only [d]; exact Nat.mod_add_mod _ _ _
    rw [h1]
    have h2 : b + 2 ^ (k + 1) - a + a = b + 2 ^ (k + 1) := by omega
    rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hb1]
  have htb := testBit_add_mod_two_pow hadd (by omega : j < k + 1)
  have hxor_lt : a ^^^ b ^^^ d < 2 ^ (k + 1) :=
    Nat.xor_lt_two_pow (Nat.xor_lt_two_pow ha1 hb1) hd
  unfold bitParallelBorrow
  change ((a ^^^ b ^^^ d) % 2 ^ (k + 1)).testBit j = decide (b % 2 ^ j < a % 2 ^ j)
  rw [Nat.mod_eq_of_lt hxor_lt, Nat.testBit_xor, Nat.testBit_xor]
  revert htb
  generalize a.testBit j = ba
  generalize b.testBit j = bb
  generalize d.testBit j = bd
  generalize decide (b % 2 ^ j < a % 2 ^ j) = bc
  cases ba <;> cases bb <;> cases bd <;> cases bc <;> decide

/-- Bit-parallel shifted `h`-bit borrow word `γ = (C_{[0..h]}(w_hi, q) >> 1) mod 2^h`
from Definition 2.3 (Equation (2.8)). -/
def aliceBorrowMask (h w_hi q : ℕ) : ℕ :=
  (bitParallelBorrow h w_hi q / 2) % 2 ^ h

lemma aliceBorrowMask_lt (h w_hi q : ℕ) : aliceBorrowMask h w_hi q < 2 ^ h :=
  Nat.mod_lt _ (by positivity)

theorem aliceBorrowMask_testBit {h w_hi q j : ℕ}
    (hw : w_hi < 2 ^ h) (hq : q < 2 ^ h) (hj : j < h) :
    (aliceBorrowMask h w_hi q).testBit j = decide (q % 2 ^ (j + 1) < w_hi % 2 ^ (j + 1)) := by
  unfold aliceBorrowMask
  have hdiv_lt : bitParallelBorrow h w_hi q / 2 < 2 ^ h := by
    have hlt := bitParallelBorrow_lt h w_hi q
    have hpow : 2 ^ (h + 1) = 2 * 2 ^ h := by ring
    omega
  rw [Nat.mod_eq_of_lt hdiv_lt, ← Nat.testBit_succ]
  exact bitParallelBorrow_testBit hw hq (by omega)

/-- Two's-complement trailing-zero wrap mask `ω(z_hi) = ((z_hi & (-z_hi)) - 1) mod 2^h`
in exact `BitVec h` arithmetic (Definition 2.3, including `z_hi = 0` and `h = 0`). -/
def omegaMaskBV (h : ℕ) (z : BitVec h) : BitVec h :=
  (z &&& (-z)) - BitVec.ofNat h 1

/-- Natural-number value of `omegaMaskBV h (BitVec.ofNat h z)`. -/
def omegaMaskNat (h z : ℕ) : ℕ :=
  (omegaMaskBV h (BitVec.ofNat h z)).toNat

lemma omegaMaskNat_lt (h z : ℕ) : omegaMaskNat h z < 2 ^ h :=
  (omegaMaskBV h (BitVec.ofNat h z)).isLt

theorem omegaMaskBV_zero (h : ℕ) : omegaMaskBV h (BitVec.ofNat h 0) = BitVec.allOnes h := by
  apply BitVec.eq_of_toNat_eq
  simp only [omegaMaskBV, BitVec.toNat_sub, BitVec.toNat_and, BitVec.toNat_neg,
    BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero, Nat.mod_self, Nat.and_zero,
    BitVec.toNat_allOnes]
  cases h with
  | zero => simp
  | succ h' =>
    have hpow : 2 ≤ 2 ^ (h' + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (h' + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.mod_eq_of_lt (by omega : 1 < 2 ^ (h' + 1)), Nat.add_zero]
    exact Nat.mod_eq_of_lt (by omega)

theorem omegaMaskBV_height_zero (z : BitVec 0) : omegaMaskBV 0 z = 0#0 := by
  apply BitVec.eq_of_toNat_eq
  have h1 := (omegaMaskBV 0 z).isLt
  simp only [BitVec.toNat_ofNat, Nat.pow_zero, Nat.zero_mod] at h1 ⊢
  omega

/-- Helper: if `z > 0` has `2^v ∣ z` and `¬ (2^(v+1) ∣ z)` with `z < 2^h`,
then `z &&& (2^h - z) = 2^v`. -/
lemma nat_and_two_pow_sub_eq {h z v : ℕ} (hz_lt : z < 2 ^ h) (hv : v < h)
    (hdvd : 2 ^ v ∣ z) (hndvd : ¬ 2 ^ (v + 1) ∣ z) :
    z &&& (2 ^ h - z) = 2 ^ v := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  have hz_pos : 0 < z := by
    by_contra h0
    have : z = 0 := by omega
    subst this; exact hndvd (dvd_zero _)
  have hneg_lt : 2 ^ h - z < 2 ^ h := by omega
  by_cases hi_lt : i < v
  · have hdiv_z : 2 ^ (i + 1) ∣ z := (Nat.pow_dvd_pow 2 (by omega)).trans hdvd
    have htb_z : z.testBit i = false := by
      rcases hdiv_z with ⟨q, rfl⟩
      rw [Nat.testBit_eq_decide_div_mod_eq, show 2 ^ (i + 1) * q = (2 * q) * 2 ^ i by
        rw [pow_succ']; ring, Nat.mul_div_cancel _ (by positivity)]
      simp
    simp [htb_z, show v ≠ i by omega]
  · by_cases hi_eq : i = v
    · subst i
      rcases hdvd with ⟨q, hq⟩
      have hq_odd : q % 2 = 1 := by
        by_contra hev
        have h2q : 2 ∣ q := Nat.dvd_of_mod_eq_zero (by omega)
        rcases h2q with ⟨r, rfl⟩
        apply hndvd
        exact ⟨r, by rw [hq, pow_succ']; ring⟩
      have htb_z : z.testBit v = true := by
        rw [hq, Nat.testBit_eq_decide_div_mod_eq, mul_comm,
            Nat.mul_div_cancel _ (by positivity), hq_odd]
        rfl
      have h2hv : 2 ^ v ∣ 2 ^ h := Nat.pow_dvd_pow 2 (by omega)
      have hneg_eq : 2 ^ h - z = 2 ^ v * (2 ^ (h - v) - q) := by
        have hsplit : 2 ^ h = 2 ^ v * 2 ^ (h - v) := by rw [← pow_add, Nat.add_sub_of_le (by omega)]
        rw [hsplit, hq, ← Nat.mul_sub_left_distrib]
      have hhv_even : 2 ^ (h - v) % 2 = 0 :=
        Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega : h - v ≠ 0))
      have hq_le : q < 2 ^ (h - v) := by
        have hsplit : 2 ^ h = 2 ^ v * 2 ^ (h - v) := by rw [← pow_add, Nat.add_sub_of_le (by omega)]
        rw [hq, hsplit] at hz_lt
        exact Nat.lt_of_mul_lt_mul_left hz_lt
      have htb_neg : (2 ^ h - z).testBit v = true := by
        rw [hneg_eq, Nat.testBit_eq_decide_div_mod_eq, mul_comm,
            Nat.mul_div_cancel _ (by positivity)]
        have : (2 ^ (h - v) - q) % 2 = 1 := by omega
        rw [this]; rfl
      simp [htb_z, htb_neg]
    · -- i > v
      by_cases hi_h : i < h
      · have hmod_pos : 0 < z % 2 ^ i := by
          by_contra h0
          have hm0 : z % 2 ^ i = 0 := by omega
          have hd : 2 ^ i ∣ z := Nat.dvd_of_mod_eq_zero hm0
          exact hndvd ((Nat.pow_dvd_pow 2 (by omega : v + 1 ≤ i)).trans hd)
        have hadd_zero : ((2 ^ h - z) + z) % 2 ^ h = 0 := by
          rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
        have htb := testBit_add_mod_two_pow hadd_zero hi_h
        simp only [Nat.zero_testBit, Nat.zero_mod, hmod_pos, decide_true] at htb
        simp only [show v ≠ i by omega, decide_false]
        revert htb
        generalize z.testBit i = bz
        generalize (2 ^ h - z).testBit i = bn
        cases bz <;> cases bn <;> decide
      · have hge : h ≤ i := by omega
        have htb_z : z.testBit i = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hz_lt (Nat.pow_le_pow_right (by omega) hge))
        simp [htb_z, show v ≠ i by omega]

/-- Exact characterization of the two's-complement wrap mask `ω(z_hi)` for ALL `h ≥ 0`,
ALL `z : BitVec h` (including `z = 0`), and ALL `1 ≤ j ≤ h`:
bit `j - 1` of `ω(z)` equals `1[z ≡ 0 (mod 2^j)]`. -/
theorem omegaMaskBV_getLsbD (h : ℕ) (z : BitVec h) {j : ℕ} (hj1 : 1 ≤ j) (hjh : j ≤ h) :
    (omegaMaskBV h z).getLsbD (j - 1) = decide (z.toNat % 2 ^ j = 0) := by
  by_cases hz0 : z.toNat = 0
  · have hzeq : z = BitVec.ofNat h 0 := BitVec.eq_of_toNat_eq (by simp [hz0])
    rw [hzeq, omegaMaskBV_zero]
    simp [show j - 1 < h by omega]
  · have hz_pos : 0 < z.toNat := by omega
    have hz_lt : z.toNat < 2 ^ h := z.isLt
    have hex : ∃ v, ¬ 2 ^ (v + 1) ∣ z.toNat := by
      refine ⟨h, fun hd => ?_⟩
      have hle := Nat.le_of_dvd hz_pos hd
      have : 2 ^ h < 2 ^ (h + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
      omega
    classical
    let v := Nat.find hex
    have hv_ndvd : ¬ 2 ^ (v + 1) ∣ z.toNat := Nat.find_spec hex
    have hv_dvd : 2 ^ v ∣ z.toNat := by
      cases hv0 : v with
      | zero => simp
      | succ v' =>
        have hlt : v' < v := by omega
        have hnn := Nat.find_min hex hlt
        push Not at hnn
        exact hnn
    have hv_lt : v < h := by
      by_contra hge
      have hd : 2 ^ h ∣ z.toNat := (Nat.pow_dvd_pow 2 (by omega)).trans hv_dvd
      have hle := Nat.le_of_dvd hz_pos hd
      omega
    have hpow_v_lt : 2 ^ v < 2 ^ h := Nat.pow_lt_pow_right (by omega) hv_lt
    have hand : (z &&& (-z)).toNat = 2 ^ v := by
      rw [BitVec.toNat_and, BitVec.toNat_neg, Nat.mod_eq_of_lt (by omega : 2 ^ h - z.toNat < 2 ^ h)]
      exact nat_and_two_pow_sub_eq hz_lt hv_lt hv_dvd hv_ndvd
    have hmask_toNat : (omegaMaskBV h z).toNat = 2 ^ v - 1 := by
      unfold omegaMaskBV
      rw [BitVec.toNat_sub, hand, BitVec.toNat_ofNat]
      have h1lt : 1 < 2 ^ h := by
        calc 1 < 2 ^ 1 := by norm_num
          _ ≤ 2 ^ h := Nat.pow_le_pow_right (by omega) (by omega)
      rw [Nat.mod_eq_of_lt h1lt]
      have h1le : 1 ≤ 2 ^ v := Nat.one_le_two_pow
      have hsub : 2 ^ h - 1 + 2 ^ v = (2 ^ v - 1) + 2 ^ h := by omega
      rw [hsub, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have htb_sub : (2 ^ v - 1).testBit (j - 1) = decide (j - 1 < v) := by
      rw [Nat.testBit_two_pow_sub_one]
    have hmod_iff : z.toNat % 2 ^ j = 0 ↔ j - 1 < v := by
      constructor
      · intro hm0
        have hd : 2 ^ j ∣ z.toNat := Nat.dvd_of_mod_eq_zero hm0
        by_contra hge
        have : v + 1 ≤ j := by omega
        exact hv_ndvd ((Nat.pow_dvd_pow 2 this).trans hd)
      · intro hlt
        exact Nat.mod_eq_zero_of_dvd ((Nat.pow_dvd_pow 2 (by omega)).trans hv_dvd)
    change (omegaMaskBV h z).toNat.testBit (j - 1) = _
    rw [hmask_toNat, htb_sub]
    by_cases hlt : j - 1 < v
    · simp only [hlt, hmod_iff.mpr hlt, decide_true]
    · have hn : z.toNat % 2 ^ j ≠ 0 := fun h0 => hlt (hmod_iff.mp h0)
      simp only [hlt, hn, decide_false]

theorem omegaMaskNat_testBit (h z : ℕ) (hz : z < 2 ^ h) {j : ℕ} (hj1 : 1 ≤ j) (hjh : j ≤ h) :
    (omegaMaskNat h z).testBit (j - 1) = decide (z % 2 ^ j = 0) := by
  have h1 := omegaMaskBV_getLsbD h (BitVec.ofNat h z) hj1 hjh
  change (omegaMaskBV h (BitVec.ofNat h z)).toNat.testBit (j - 1) = _ at h1
  simpa [omegaMaskNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hz] using h1

/-! ### Definition 2.3 & Theorem 2.4(a): Cyclic Carry-Cut Partition Family `𝒫_m` (`mechanismIICStar`) -/

/-- Label universe for the cyclic carry-cut partition `𝒫_m` (`mechanismIICStar`) at width `t ≥ 1`
and cut `0 ≤ m ≤ t - 1`: `{0,1}^m × {0,1}^{m+1} × {0,1}^h × {0,1}^h` with `h = t - 1 - m`
(`2^(2t - 1)` keys). -/
abbrev IICStarLabel (t m : ℕ) : Type :=
  Fin (2 ^ m) × Fin (2 ^ (m + 1)) × Fin (2 ^ (t - 1 - m)) × Fin (2 ^ (t - 1 - m))

/-- Alice's branchless cyclic carry-cut label generator (Definition 2.3, Equation (2.8)). -/
def iicStarAliceKey (t m : ℕ) (r : Fin (2 ^ t) × Fin (2 ^ t))
    (q : Fin (2 ^ (t - 1 - m))) : IICStarLabel t m :=
  let h := t - 1 - m
  let x := r.1.val ^^^ r.2.val
  let w_lo : Fin (2 ^ m) := ⟨r.2.val % 2 ^ m, Nat.mod_lt _ (by positivity)⟩
  let w_hi := (r.2.val / 2 ^ m) % 2 ^ h
  let x_lo_m : Fin (2 ^ (m + 1)) := ⟨x % 2 ^ (m + 1), Nat.mod_lt _ (by positivity)⟩
  let x_hi := (x / 2 ^ (m + 1)) % 2 ^ h
  let gamma := aliceBorrowMask h w_hi q.val
  let y_tilde : Fin (2 ^ h) :=
    ⟨x_hi ^^^ gamma, Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) (aliceBorrowMask_lt _ _ _)⟩
  (w_lo, x_lo_m, q, y_tilde)

/-- Bob's branchless cyclic carry-cut label generator (Definition 2.3, Equation (2.9)). -/
def iicStarBobKey (t m : ℕ) (c : Fin (2 ^ t) × Fin (2 ^ t))
    (w_lo : Fin (2 ^ m)) : IICStarLabel t m :=
  let h := t - 1 - m
  let y := c.1.val ^^^ c.2.val
  let z_lo := c.2.val % 2 ^ m
  let z_hi := (c.2.val / 2 ^ m) % 2 ^ h
  let y_lo_m := y % 2 ^ (m + 1)
  let y_hi := (y / 2 ^ (m + 1)) % 2 ^ h
  let C_lo := bitParallelBorrow m w_lo.val z_lo
  let c_m := (C_lo / 2 ^ m) % 2
  let x_lo_m : Fin (2 ^ (m + 1)) :=
    ⟨y_lo_m ^^^ C_lo, Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) (bitParallelBorrow_lt _ _ _)⟩
  let q : Fin (2 ^ h) := ⟨(z_hi + 2 ^ h - c_m) % 2 ^ h, Nat.mod_lt _ (by positivity)⟩
  let beta := c_m * omegaMaskNat h z_hi
  have hbeta : beta < 2 ^ h := by
    have hcm_le : c_m ≤ 1 := by have := Nat.mod_lt (C_lo / 2 ^ m) (by omega : 0 < 2); omega
    have hom := omegaMaskNat_lt h z_hi
    have h1 : c_m * omegaMaskNat h z_hi ≤ 1 * omegaMaskNat h z_hi := Nat.mul_le_mul_right _ hcm_le
    omega
  let y_tilde : Fin (2 ^ h) :=
    ⟨y_hi ^^^ beta, Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) hbeta⟩
  (w_lo, x_lo_m, q, y_tilde)

lemma bool_xor_bridge_mp {bx by_ : Bool} {p1 p2 p3 : Prop}
    [Decidable p1] [Decidable p2] [Decidable p3]
    (htb : (bx ^^ decide p2) = (by_ ^^ decide p3))
    (hmq : (if p1 then (1 : ZMod 2) else 0) =
      (if p2 then 1 else 0) + (if p3 then 1 else 0)) :
    (bx ^^ decide (by_ = decide p1)) = true := by
  by_cases h1 : p1 <;> by_cases h2 : p2 <;> by_cases h3 : p3 <;>
    simp only [h1, h2, h3, ↓reduceIte, decide_true, decide_false] at htb hmq ⊢ <;>
    revert htb hmq <;> cases bx <;> cases by_ <;> decide

lemma bool_xor_bridge_mpr {bx by_ : Bool} {p1 p2 p3 : Prop}
    [Decidable p1] [Decidable p2] [Decidable p3]
    (hb : (bx ^^ decide (by_ = decide p1)) = true)
    (hmq : (if p1 then (1 : ZMod 2) else 0) =
      (if p2 then 1 else 0) + (if p3 then 1 else 0)) :
    (bx ^^ decide p2) = (by_ ^^ decide p3) := by
  by_cases h1 : p1 <;> by_cases h2 : p2 <;> by_cases h3 : p3 <;>
    simp only [h1, h2, h3, ↓reduceIte, decide_true, decide_false] at hb hmq ⊢ <;>
    revert hb hmq <;> cases bx <;> cases by_ <;> decide

/-- Fundamental key-matching equivalence for Mechanism `II-C*`:
for any `t ≥ 1`, `0 ≤ m ≤ t - 1`, row `r`, column `c`, `q`, `w_lo`:
`iicStarAliceKey t m r q = iicStarBobKey t m c w_lo` holds if and only if
`M_rel t r c` holds AND `w_lo`, `q` are the unique canonical values determined by `(r, c)`. -/
lemma iicStar_key_eq_iff {t m : ℕ} (ht : 1 ≤ t) (hm : m ≤ t - 1)
    (r c : Fin (2 ^ t) × Fin (2 ^ t))
    (q : Fin (2 ^ (t - 1 - m))) (w_lo : Fin (2 ^ m)) :
    iicStarAliceKey t m r q = iicStarBobKey t m c w_lo ↔
      M_rel t r c ∧
      w_lo.val = r.2.val % 2 ^ m ∧
      q.val = ((c.2.val / 2 ^ m) % 2 ^ (t - 1 - m) + 2 ^ (t - 1 - m) -
        (if c.2.val % 2 ^ m < r.2.val % 2 ^ m then 1 else 0)) % 2 ^ (t - 1 - m) := by
  let h := t - 1 - m
  have hmh : m + h = t - 1 := by omega
  have hcm_eval : ∀ w0 : Fin (2 ^ m),
      (bitParallelBorrow m w0.val (c.2.val % 2 ^ m) / 2 ^ m) % 2 =
        if c.2.val % 2 ^ m < w0.val then 1 else 0 := by
    intro w0
    have htb := bitParallelBorrow_testBit (k := m) (a := w0.val) (b := c.2.val % 2 ^ m) (j := m)
      w0.isLt (Nat.mod_lt c.2.val (by positivity)) le_rfl
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.mod_eq_of_lt w0.isLt,
        Nat.mod_eq_of_lt (Nat.mod_lt c.2.val (by positivity))] at htb
    have hmod2 : (bitParallelBorrow m w0.val (c.2.val % 2 ^ m) / 2 ^ m) % 2 < 2 :=
      Nat.mod_lt _ (by omega)
    by_cases hlt : c.2.val % 2 ^ m < w0.val
    · simp only [hlt, decide_true, ↓reduceIte] at htb ⊢
      exact of_decide_eq_true htb
    · simp only [hlt, decide_false, ↓reduceIte] at htb ⊢
      have hne : (bitParallelBorrow m w0.val (c.2.val % 2 ^ m) / 2 ^ m) % 2 ≠ 1 :=
        of_decide_eq_false htb
      omega
  have hpow_t_div : ∀ a : ℕ, (a % 2 ^ (t - 1)) / 2 ^ m = (a / 2 ^ m) % 2 ^ h := by
    intro a
    rw [show 2 ^ (t - 1) = 2 ^ h * 2 ^ m by rw [← pow_add, add_comm, hmh]]
    exact Nat.mod_mul_left_div_self a (2 ^ m) (2 ^ h)
  have hpow_t_mod : ∀ a : ℕ, (a % 2 ^ (t - 1)) % 2 ^ m = a % 2 ^ m := fun a =>
    Nat.mod_mod_of_dvd a (Nat.pow_dvd_pow 2 hm)
  rw [M_rel_iff_testBit]
  simp only [iicStarAliceKey, iicStarBobKey, Prod.mk.injEq, Fin.ext_iff]
  constructor
  · rintro ⟨hwlo_eq, hxlo_eq, hq_eq, hyt_eq⟩
    have hwlo_val : w_lo.val = r.2.val % 2 ^ m := hwlo_eq.symm
    have hcm_eq : (bitParallelBorrow m w_lo.val (c.2.val % 2 ^ m) / 2 ^ m) % 2 =
        if c.2.val % 2 ^ m < r.2.val % 2 ^ m then 1 else 0 := by
      rw [hcm_eval w_lo, hwlo_val]
    have hq_val : q.val = ((c.2.val / 2 ^ m) % 2 ^ h + 2 ^ h -
        (if c.2.val % 2 ^ m < r.2.val % 2 ^ m then 1 else 0)) % 2 ^ h := by
      rw [hq_eq, hcm_eq]
    refine ⟨?_, hwlo_val, hq_val⟩
    intro i hi
    by_cases him : i < m + 1
    · have htb := congrArg (fun n => n.testBit i) hxlo_eq
      rw [Nat.testBit_mod_two_pow, Nat.testBit_xor (x := (c.1.val ^^^ c.2.val) % 2 ^ (m + 1)),
          Nat.testBit_mod_two_pow,
          bitParallelBorrow_testBit w_lo.isLt (Nat.mod_lt c.2.val (by positivity)) (by omega)] at htb
      simp only [him, decide_true, Bool.true_and] at htb
      have hmod_w : w_lo.val % 2 ^ i = r.2.val % 2 ^ i := by
        rw [hwlo_val]
        exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))
      have hmod_z : c.2.val % 2 ^ m % 2 ^ i = c.2.val % 2 ^ i :=
        Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))
      rw [hmod_w, hmod_z] at htb
      revert htb
      generalize (r.1.val ^^^ r.2.val).testBit i = bx
      generalize (c.1.val ^^^ c.2.val).testBit i = by_
      generalize decide (c.2.val % 2 ^ i < r.2.val % 2 ^ i) = bc
      cases bx <;> cases by_ <;> cases bc <;> decide
    · -- m + 1 ≤ i < t, write i = m + j with 1 ≤ j ≤ h
      set j := i - m
      have hj1 : 1 ≤ j := by omega
      have hjh : j ≤ h := by omega
      have hij : m + j = i := by omega
      have hjm1 : j - 1 < h := by omega
      have htb := congrArg (fun n => n.testBit (j - 1)) hyt_eq
      rw [Nat.testBit_xor (x := (r.1.val ^^^ r.2.val) / 2 ^ (m + 1) % 2 ^ h),
          Nat.testBit_xor (x := (c.1.val ^^^ c.2.val) / 2 ^ (m + 1) % 2 ^ h),
          Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
          Nat.testBit_div_two_pow, Nat.testBit_div_two_pow,
          aliceBorrowMask_testBit (Nat.mod_lt _ (by positivity)) q.isLt hjm1] at htb
      simp only [hjm1, decide_true, Bool.true_and,
        show j - 1 + (m + 1) = i by omega, show j - 1 + 1 = j by omega] at htb
      have hmq := modular_quotient_carry_identity (s := t - 1) (m := m) (j := j)
        (w := r.2.val % 2 ^ (t - 1)) (z := c.2.val % 2 ^ (t - 1))
        hm hj1 hjh (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ (by positivity))
      dsimp only at hmq
      rw [hpow_t_mod, hpow_t_mod, hpow_t_div, hpow_t_div, hij] at hmq
      have hdvd_is : 2 ^ i ∣ 2 ^ (t - 1) := Nat.pow_dvd_pow 2 (by omega)
      have hm1 : borrowBit i (r.2.val % 2 ^ (t - 1)) (c.2.val % 2 ^ (t - 1)) =
          borrowBit i r.2.val c.2.val := by
        simp only [borrowBit, Nat.mod_mod_of_dvd _ hdvd_is]
      rw [hm1, ← hq_val] at hmq
      have hbeta_tb : ((bitParallelBorrow m w_lo.val (c.2.val % 2 ^ m) / 2 ^ m % 2) *
          omegaMaskNat h (c.2.val / 2 ^ m % 2 ^ h)).testBit (j - 1) =
          decide ((if c.2.val % 2 ^ m < r.2.val % 2 ^ m then 1 else 0) = 1 ∧
            (c.2.val / 2 ^ m % 2 ^ h) % 2 ^ j = 0) := by
        rw [hcm_eq]
        by_cases hlt : c.2.val % 2 ^ m < r.2.val % 2 ^ m
        · simp only [hlt, ↓reduceIte, one_mul, true_and]
          exact omegaMaskNat_testBit h _ (Nat.mod_lt _ (by positivity)) hj1 hjh
        · simp [hlt]
      rw [hbeta_tb] at htb
      unfold borrowBit at hmq
      exact bool_xor_bridge_mp htb hmq
  · rintro ⟨hbits, hwlo_val, hq_val⟩
    have hcm_eq : (bitParallelBorrow m w_lo.val (c.2.val % 2 ^ m) / 2 ^ m) % 2 =
        if c.2.val % 2 ^ m < r.2.val % 2 ^ m then 1 else 0 := by
      rw [hcm_eval w_lo, hwlo_val]
    refine ⟨hwlo_val.symm, ?_, ?_, ?_⟩
    · apply Nat.eq_of_testBit_eq
      intro i
      by_cases him : i < m + 1
      · rw [Nat.testBit_mod_two_pow, Nat.testBit_xor (x := (c.1.val ^^^ c.2.val) % 2 ^ (m + 1)),
            Nat.testBit_mod_two_pow,
            bitParallelBorrow_testBit w_lo.isLt (Nat.mod_lt c.2.val (by positivity)) (by omega)]
        simp only [him, decide_true, Bool.true_and]
        have hmod_w : w_lo.val % 2 ^ i = r.2.val % 2 ^ i := by
          rw [hwlo_val]; exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))
        have hmod_z : c.2.val % 2 ^ m % 2 ^ i = c.2.val % 2 ^ i :=
          Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))
        rw [hmod_w, hmod_z]
        have hb := hbits i (by omega)
        revert hb
        generalize (r.1.val ^^^ r.2.val).testBit i = bx
        generalize (c.1.val ^^^ c.2.val).testBit i = by_
        generalize decide (c.2.val % 2 ^ i < r.2.val % 2 ^ i) = bc
        cases bx <;> cases by_ <;> cases bc <;> decide
      · have hge : m + 1 ≤ i := by omega
        have h1 : (r.1.val ^^^ r.2.val) % 2 ^ (m + 1) < 2 ^ (m + 1) := Nat.mod_lt _ (by positivity)
        have h2 : (c.1.val ^^^ c.2.val) % 2 ^ (m + 1) ^^^
            bitParallelBorrow m w_lo.val (c.2.val % 2 ^ m) < 2 ^ (m + 1) :=
          Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) (bitParallelBorrow_lt _ _ _)
        rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) hge)),
            Nat.testBit_lt_two_pow (lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by omega) hge))]
    · rw [hq_val, hcm_eq]
    · apply Nat.eq_of_testBit_eq
      intro k
      by_cases hk : k < h
      · set j := k + 1
        have hj1 : 1 ≤ j := by omega
        have hjh : j ≤ h := by omega
        have hjm1 : j - 1 = k := by omega
        rw [Nat.testBit_xor (x := (r.1.val ^^^ r.2.val) / 2 ^ (m + 1) % 2 ^ h),
            Nat.testBit_xor (x := (c.1.val ^^^ c.2.val) / 2 ^ (m + 1) % 2 ^ h),
            Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
            Nat.testBit_div_two_pow, Nat.testBit_div_two_pow,
            aliceBorrowMask_testBit (Nat.mod_lt _ (by positivity)) q.isLt hk]
        simp only [hk, decide_true, Bool.true_and]
        have hbeta_tb : ((bitParallelBorrow m w_lo.val (c.2.val % 2 ^ m) / 2 ^ m % 2) *
            omegaMaskNat h (c.2.val / 2 ^ m % 2 ^ h)).testBit k =
            decide ((if c.2.val % 2 ^ m < r.2.val % 2 ^ m then 1 else 0) = 1 ∧
              (c.2.val / 2 ^ m % 2 ^ h) % 2 ^ j = 0) := by
          rw [hcm_eq]
          by_cases hlt : c.2.val % 2 ^ m < r.2.val % 2 ^ m
          · simp only [hlt, ↓reduceIte, one_mul, true_and]
            rw [← hjm1]
            exact omegaMaskNat_testBit h _ (Nat.mod_lt _ (by positivity)) hj1 hjh
          · simp [hlt]
        rw [hbeta_tb]
        have hmq := modular_quotient_carry_identity (s := t - 1) (m := m) (j := j)
          (w := r.2.val % 2 ^ (t - 1)) (z := c.2.val % 2 ^ (t - 1))
          hm hj1 hjh (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ (by positivity))
        dsimp only at hmq
        rw [hpow_t_mod, hpow_t_mod, hpow_t_div, hpow_t_div] at hmq
        have hdvd_is : 2 ^ (m + j) ∣ 2 ^ (t - 1) := Nat.pow_dvd_pow 2 (by omega)
        have hm1 : borrowBit (m + j) (r.2.val % 2 ^ (t - 1)) (c.2.val % 2 ^ (t - 1)) =
            borrowBit (m + j) r.2.val c.2.val := by
          simp only [borrowBit, Nat.mod_mod_of_dvd _ hdvd_is]
        rw [hm1, ← hq_val] at hmq
        have hb := hbits (m + j) (by omega)
        rw [show k + (m + 1) = m + j by omega]
        unfold borrowBit at hmq
        exact bool_xor_bridge_mpr hb hmq
      · have hge : h ≤ k := by omega
        have h1 : (r.1.val ^^^ r.2.val) / 2 ^ (m + 1) % 2 ^ h ^^^
            aliceBorrowMask h (r.2.val / 2 ^ m % 2 ^ h) q.val < 2 ^ h :=
          Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) (aliceBorrowMask_lt _ _ _)
        have hbeta : (bitParallelBorrow m w_lo.val (c.2.val % 2 ^ m) / 2 ^ m % 2) *
            omegaMaskNat h (c.2.val / 2 ^ m % 2 ^ h) < 2 ^ h := by
          have hcm_le : bitParallelBorrow m w_lo.val (c.2.val % 2 ^ m) / 2 ^ m % 2 ≤ 1 := by
            have := Nat.mod_lt (bitParallelBorrow m w_lo.val (c.2.val % 2 ^ m) / 2 ^ m) (by omega : 0 < 2)
            omega
          have hom := omegaMaskNat_lt h (c.2.val / 2 ^ m % 2 ^ h)
          have := Nat.mul_le_mul_right (omegaMaskNat h (c.2.val / 2 ^ m % 2 ^ h)) hcm_le
          omega
        have h2 : (c.1.val ^^^ c.2.val) / 2 ^ (m + 1) % 2 ^ h ^^^
            (bitParallelBorrow m w_lo.val (c.2.val % 2 ^ m) / 2 ^ m % 2) *
            omegaMaskNat h (c.2.val / 2 ^ m % 2 ^ h) < 2 ^ h :=
          Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) hbeta
        rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) hge)),
            Nat.testBit_lt_two_pow (lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by omega) hge))]

/-- Definition 2.3 & Theorem 2.4(a): Cyclic carry-cut partition `𝒫_m` (`mechanismIICStar`) as an
`ExactBicliqueCover (M_rel t)` for every `t ≥ 1` and cut `0 ≤ m ≤ t - 1`. -/
def mechanismIICStar (t m : ℕ) (ht : 1 ≤ t) (hm : m ≤ t - 1) :
    ExactBicliqueCover (M_rel t) where
  L := IICStarLabel t m
  U ℓ := Finset.univ.filter fun r => ∃ q : Fin (2 ^ (t - 1 - m)), iicStarAliceKey t m r q = ℓ
  V ℓ := Finset.univ.filter fun c => ∃ w_lo : Fin (2 ^ m), iicStarBobKey t m c w_lo = ℓ
  isBiclique ℓ r hr c hc := by
    rw [Finset.mem_filter] at hr hc
    rcases hr.2 with ⟨q, hq⟩
    rcases hc.2 with ⟨w_lo, hw⟩
    exact ((iicStar_key_eq_iff ht hm r c q w_lo).mp (hq.trans hw.symm)).1
  covers r c hrc := by
    let w_lo : Fin (2 ^ m) := ⟨r.2.val % 2 ^ m, Nat.mod_lt _ (by positivity)⟩
    let c_m : ℕ := if c.2.val % 2 ^ m < r.2.val % 2 ^ m then 1 else 0
    let q : Fin (2 ^ (t - 1 - m)) :=
      ⟨((c.2.val / 2 ^ m) % 2 ^ (t - 1 - m) + 2 ^ (t - 1 - m) - c_m) % 2 ^ (t - 1 - m),
       Nat.mod_lt _ (by positivity)⟩
    have heq := (iicStar_key_eq_iff ht hm r c q w_lo).mpr ⟨hrc, rfl, rfl⟩
    refine ⟨iicStarAliceKey t m r q, ?_, ?_⟩
    · rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, q, rfl⟩
    · rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, w_lo, heq.symm⟩

/-- Theorem 2.4(a): `𝒫_m` (`mechanismIICStar`) has exact label count `|L| = 2^(2t - 1)`. -/
theorem mechanismIICStar_card_L (t m : ℕ) (ht : 1 ≤ t) (hm : m ≤ t - 1) :
    Fintype.card (mechanismIICStar t m ht hm).L = 2 ^ (2 * t - 1) := by
  change Fintype.card (IICStarLabel t m) = 2 ^ (2 * t - 1)
  simp only [IICStarLabel, Fintype.card_prod, Fintype.card_fin]
  rw [← pow_add, ← pow_add, ← pow_add]
  congr 1; omega

/-- Theorem 2.4(a): `𝒫_m` (`mechanismIICStar`) is a zero-duplicate biclique partition (`IsPartition`). -/
theorem mechanismIICStar_isPartition (t m : ℕ) (ht : 1 ≤ t) (hm : m ≤ t - 1) :
    (mechanismIICStar t m ht hm).IsPartition := by
  intro r c hrc
  let w_lo0 : Fin (2 ^ m) := ⟨r.2.val % 2 ^ m, Nat.mod_lt _ (by positivity)⟩
  let c_m : ℕ := if c.2.val % 2 ^ m < r.2.val % 2 ^ m then 1 else 0
  let q0 : Fin (2 ^ (t - 1 - m)) :=
    ⟨((c.2.val / 2 ^ m) % 2 ^ (t - 1 - m) + 2 ^ (t - 1 - m) - c_m) % 2 ^ (t - 1 - m),
     Nat.mod_lt _ (by positivity)⟩
  have heq0 := (iicStar_key_eq_iff ht hm r c q0 w_lo0).mpr ⟨hrc, rfl, rfl⟩
  refine ⟨iicStarAliceKey t m r q0, ?_, ?_⟩
  · constructor
    · simp only [mechanismIICStar, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨q0, rfl⟩
    · simp only [mechanismIICStar, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨w_lo0, heq0.symm⟩
  · rintro ℓ ⟨hU, hV⟩
    simp only [mechanismIICStar, Finset.mem_filter, Finset.mem_univ, true_and] at hU hV
    rcases hU with ⟨q, hq⟩
    rcases hV with ⟨w_lo, hw⟩
    have hmatch := (iicStar_key_eq_iff ht hm r c q w_lo).mp (hq.trans hw.symm)
    have hq_eq : q = q0 := Fin.ext hmatch.2.2
    rw [← hq, hq_eq]

/-- Theorem 2.4(a): Constant row load `|A(u, w)| = 2^(t - 1 - m)` for every row. -/
theorem mechanismIICStar_rowLoad (t m : ℕ) (ht : 1 ≤ t) (hm : m ≤ t - 1)
    (r : Fin (2 ^ t) × Fin (2 ^ t)) :
    (mechanismIICStar t m ht hm).rowLoad r = 2 ^ (t - 1 - m) := by
  unfold ExactBicliqueCover.rowLoad mechanismIICStar
  dsimp only
  have hbij : (Finset.univ.filter fun ℓ : IICStarLabel t m =>
      r ∈ Finset.univ.filter fun r' => ∃ q, iicStarAliceKey t m r' q = ℓ).card =
      (Finset.univ : Finset (Fin (2 ^ (t - 1 - m)))).card := by
    refine Finset.card_bij
      (fun ℓ _ => ℓ.2.2.1)
      (fun _ _ => Finset.mem_univ _)
      (fun ℓ1 h1 ℓ2 h2 h => ?_)
      (fun q _ => ?_)
    · rw [Finset.mem_filter] at h1 h2
      have h1' := (Finset.mem_filter.mp h1.2).2
      have h2' := (Finset.mem_filter.mp h2.2).2
      rcases h1' with ⟨q1, hq1⟩
      rcases h2' with ⟨q2, hq2⟩
      have eq1 : ℓ1.2.2.1 = q1 := by rw [← hq1]; rfl
      have eq2 : ℓ2.2.2.1 = q2 := by rw [← hq2]; rfl
      have hq12 : q1 = q2 := eq1.symm.trans (h.trans eq2)
      rw [← hq1, ← hq2, hq12]
    · refine ⟨iicStarAliceKey t m r q, ?_, rfl⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, q, rfl⟩⟩
  simpa using hbij

/-- Theorem 2.4(a): Constant column load `|B(v, z)| = 2^m` for every column. -/
theorem mechanismIICStar_colLoad (t m : ℕ) (ht : 1 ≤ t) (hm : m ≤ t - 1)
    (c : Fin (2 ^ t) × Fin (2 ^ t)) :
    (mechanismIICStar t m ht hm).colLoad c = 2 ^ m := by
  unfold ExactBicliqueCover.colLoad mechanismIICStar
  dsimp only
  have hbij : (Finset.univ.filter fun ℓ : IICStarLabel t m =>
      c ∈ Finset.univ.filter fun c' => ∃ w_lo, iicStarBobKey t m c' w_lo = ℓ).card =
      (Finset.univ : Finset (Fin (2 ^ m))).card := by
    refine Finset.card_bij
      (fun ℓ _ => ℓ.1)
      (fun _ _ => Finset.mem_univ _)
      (fun ℓ1 h1 ℓ2 h2 h => ?_)
      (fun w_lo _ => ?_)
    · rw [Finset.mem_filter] at h1 h2
      have h1' := (Finset.mem_filter.mp h1.2).2
      have h2' := (Finset.mem_filter.mp h2.2).2
      rcases h1' with ⟨w1, hw1⟩
      rcases h2' with ⟨w2, hw2⟩
      have eq1 : ℓ1.1 = w1 := by rw [← hw1]; rfl
      have eq2 : ℓ2.1 = w2 := by rw [← hw2]; rfl
      have hw12 : w1 = w2 := eq1.symm.trans (h.trans eq2)
      rw [← hw1, ← hw2, hw12]
    · refine ⟨iicStarBobKey t m c w_lo, ?_, rfl⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, w_lo, rfl⟩⟩
  simpa using hbij

theorem mechanismIICStar_totalRowLoad (t m : ℕ) (ht : 1 ≤ t) (hm : m ≤ t - 1) :
    (mechanismIICStar t m ht hm).totalRowLoad = 2 ^ (2 * t) * 2 ^ (t - 1 - m) := by
  rw [← ExactBicliqueCover.sum_rowLoad]
  simp only [mechanismIICStar_rowLoad, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, smul_eq_mul, ← pow_add, show t + t = 2 * t by omega]

theorem mechanismIICStar_totalColLoad (t m : ℕ) (ht : 1 ≤ t) (hm : m ≤ t - 1) :
    (mechanismIICStar t m ht hm).totalColLoad = 2 ^ (2 * t) * 2 ^ m := by
  rw [← ExactBicliqueCover.sum_colLoad]
  simp only [mechanismIICStar_colLoad, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, smul_eq_mul, ← pow_add, show t + t = 2 * t by omega]

/-- Exact biclique row size `|U_ℓ| = 2^(t - m)` and column size `|V_ℓ| = 2^(m + 1)`
for every label `ℓ` of Mechanism `II-C*`. -/
theorem mechanismIICStar_biclique_cards (t m : ℕ) (ht : 1 ≤ t) (hm : m ≤ t - 1)
    (ℓ : (mechanismIICStar t m ht hm).L) :
    ((mechanismIICStar t m ht hm).U ℓ).card = 2 ^ (t - m) ∧
    ((mechanismIICStar t m ht hm).V ℓ).card = 2 ^ (m + 1) := by
  let h := t - 1 - m
  have hdecomp : ∀ a : ℕ, a = a % 2 ^ m + 2 ^ m * ((a / 2 ^ m) % 2 ^ h) +
      2 ^ (t - 1) * (a / 2 ^ (t - 1)) := by
    intro a
    have h1 := Nat.div_add_mod a (2 ^ m)
    have h2 := Nat.div_add_mod (a / 2 ^ m) (2 ^ h)
    have h3 : (a / 2 ^ m) / 2 ^ h = a / 2 ^ (t - 1) := by
      rw [Nat.div_div_eq_div_mul, ← pow_add, show m + h = t - 1 by omega]
    have h4 : 2 ^ m * (2 ^ h * ((a / 2 ^ m) / 2 ^ h)) =
        2 ^ (t - 1) * (a / 2 ^ (t - 1)) := by
      rw [← mul_assoc, ← pow_add, show m + h = t - 1 by omega, h3]
    calc a = 2 ^ m * (a / 2 ^ m) + a % 2 ^ m := h1.symm
      _ = 2 ^ m * (2 ^ h * ((a / 2 ^ m) / 2 ^ h) + (a / 2 ^ m) % 2 ^ h) + a % 2 ^ m := by
          rw [h2]
      _ = 2 ^ m * (2 ^ h * ((a / 2 ^ m) / 2 ^ h)) + 2 ^ m * ((a / 2 ^ m) % 2 ^ h) +
          a % 2 ^ m := by ring
      _ = a % 2 ^ m + 2 ^ m * ((a / 2 ^ m) % 2 ^ h) + 2 ^ (t - 1) * (a / 2 ^ (t - 1)) := by
          rw [h4]; ring
  have hU_le : ∀ ℓ' : IICStarLabel t m, ((mechanismIICStar t m ht hm).U ℓ').card ≤ 2 ^ (t - m) := by
    intro ℓ'
    have hinj : ((mechanismIICStar t m ht hm).U ℓ').card ≤
        (Finset.univ : Finset (Fin (2 ^ h) × Fin 2)).card := by
      refine Finset.card_le_card_of_injOn
        (fun r => (⟨(r.2.val / 2 ^ m) % 2 ^ h, Nat.mod_lt _ (by positivity)⟩,
                   ⟨r.2.val / 2 ^ (t - 1), by
                     have hr := r.2.isLt
                     have hpow : 2 ^ t = 2 ^ (t - 1) * 2 := by
                       rw [← pow_succ, show t - 1 + 1 = t by omega]
                     exact Nat.div_lt_of_lt_mul (by linarith)⟩))
        (fun _ _ => Finset.mem_univ _)
        (fun r1 hr1 r2 hr2 hpair => ?_)
      simp only [Finset.mem_coe, mechanismIICStar, Finset.mem_filter, Finset.mem_univ, true_and] at hr1 hr2
      rcases hr1 with ⟨q1, hq1⟩
      rcases hr2 with ⟨q2, hq2⟩
      have h12 : iicStarAliceKey t m r1 q1 = iicStarAliceKey t m r2 q2 := hq1.trans hq2.symm
      simp only [iicStarAliceKey, Prod.mk.injEq, Fin.ext_iff] at h12
      have hwhi : (r1.2.val / 2 ^ m) % 2 ^ h = (r2.2.val / 2 ^ m) % 2 ^ h :=
        congrArg (fun p => p.1.val) hpair
      have hwtop : r1.2.val / 2 ^ (t - 1) = r2.2.val / 2 ^ (t - 1) :=
        congrArg (fun p => p.2.val) hpair
      have hw_eq : r1.2 = r2.2 := by
        apply Fin.ext
        rw [hdecomp r1.2.val, hdecomp r2.2.val, h12.1, hwhi, hwtop]
      have hx_hi_eq : ((r1.1.val ^^^ r1.2.val) / 2 ^ (m + 1)) % 2 ^ h =
          ((r2.1.val ^^^ r2.2.val) / 2 ^ (m + 1)) % 2 ^ h := by
        have hyt := h12.2.2.2
        rw [hwhi, h12.2.2.1] at hyt
        have := congrArg (· ^^^ aliceBorrowMask h (r2.2.val / 2 ^ m % 2 ^ h) q2.val) hyt
        simpa [h, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] using this
      have hx_eq : r1.1.val ^^^ r1.2.val = r2.1.val ^^^ r2.2.val := by
        have hlt1 : r1.1.val ^^^ r1.2.val < 2 ^ t := Nat.xor_lt_two_pow r1.1.isLt r1.2.isLt
        have hlt2 : r2.1.val ^^^ r2.2.val < 2 ^ t := Nat.xor_lt_two_pow r2.1.isLt r2.2.isLt
        have hdiv1 : (r1.1.val ^^^ r1.2.val) / 2 ^ (m + 1) < 2 ^ h := by
          have : 2 ^ t = 2 ^ (m + 1) * 2 ^ h := by rw [← pow_add]; congr 1; omega
          exact Nat.div_lt_of_lt_mul (by linarith)
        have hdiv2 : (r2.1.val ^^^ r2.2.val) / 2 ^ (m + 1) < 2 ^ h := by
          have : 2 ^ t = 2 ^ (m + 1) * 2 ^ h := by rw [← pow_add]; congr 1; omega
          exact Nat.div_lt_of_lt_mul (by linarith)
        rw [Nat.mod_eq_of_lt hdiv1, Nat.mod_eq_of_lt hdiv2] at hx_hi_eq
        have d1 := Nat.div_add_mod (r1.1.val ^^^ r1.2.val) (2 ^ (m + 1))
        have d2 := Nat.div_add_mod (r2.1.val ^^^ r2.2.val) (2 ^ (m + 1))
        rw [hx_hi_eq, h12.2.1] at d1
        omega
      apply Prod.ext _ hw_eq
      apply Fin.ext
      rw [hw_eq] at hx_eq
      have := congrArg (· ^^^ r2.2.val) hx_eq
      simpa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] using this
    simpa [Fintype.card_prod, Fintype.card_fin, ← pow_succ, show h + 1 = t - m by omega] using hinj
  have hV_le : ∀ ℓ' : IICStarLabel t m, ((mechanismIICStar t m ht hm).V ℓ').card ≤ 2 ^ (m + 1) := by
    intro ℓ'
    have hinj : ((mechanismIICStar t m ht hm).V ℓ').card ≤
        (Finset.univ : Finset (Fin (2 ^ m) × Fin 2)).card := by
      refine Finset.card_le_card_of_injOn
        (fun c => (⟨c.2.val % 2 ^ m, Nat.mod_lt _ (by positivity)⟩,
                   ⟨c.2.val / 2 ^ (t - 1), by
                     have hc := c.2.isLt
                     have hpow : 2 ^ t = 2 ^ (t - 1) * 2 := by
                       rw [← pow_succ, show t - 1 + 1 = t by omega]
                     exact Nat.div_lt_of_lt_mul (by linarith)⟩))
        (fun _ _ => Finset.mem_univ _)
        (fun c1 hc1 c2 hc2 hpair => ?_)
      simp only [Finset.mem_coe, mechanismIICStar, Finset.mem_filter, Finset.mem_univ, true_and] at hc1 hc2
      rcases hc1 with ⟨w1, hw1⟩
      rcases hc2 with ⟨w2, hw2⟩
      have h12 : iicStarBobKey t m c1 w1 = iicStarBobKey t m c2 w2 := hw1.trans hw2.symm
      simp only [iicStarBobKey, Prod.mk.injEq, Fin.ext_iff] at h12
      have hzlo : c1.2.val % 2 ^ m = c2.2.val % 2 ^ m := congrArg (fun p => p.1.val) hpair
      have hztop : c1.2.val / 2 ^ (t - 1) = c2.2.val / 2 ^ (t - 1) := congrArg (fun p => p.2.val) hpair
      have hw12 : w1.val = w2.val := h12.1
      have hcm12 : bitParallelBorrow m w1.val (c1.2.val % 2 ^ m) =
          bitParallelBorrow m w2.val (c2.2.val % 2 ^ m) := by rw [hw12, hzlo]
      have hzhi : (c1.2.val / 2 ^ m) % 2 ^ h = (c2.2.val / 2 ^ m) % 2 ^ h := by
        have hq := h12.2.2.1
        rw [hcm12] at hq
        set cm := bitParallelBorrow m w2.val (c2.2.val % 2 ^ m) / 2 ^ m % 2
        have hcm_le : cm ≤ 1 := by have := Nat.mod_lt (bitParallelBorrow m w2.val (c2.2.val % 2 ^ m) / 2 ^ m) (by omega : 0 < 2); omega
        have h1lt : (c1.2.val / 2 ^ m) % 2 ^ h < 2 ^ h := Nat.mod_lt _ (by positivity)
        have h2lt : (c2.2.val / 2 ^ m) % 2 ^ h < 2 ^ h := Nat.mod_lt _ (by positivity)
        have hadd : ∀ a : ℕ, a < 2 ^ h → ((a + 2 ^ h - cm) % 2 ^ h + cm) % 2 ^ h = a := by
          intro a ha
          rw [Nat.mod_add_mod]
          have : a + 2 ^ h - cm + cm = a + 2 ^ h := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt ha]
        rw [← hadd _ h1lt, ← hadd _ h2lt, hq]
      have hz_eq : c1.2 = c2.2 := by
        apply Fin.ext
        rw [hdecomp c1.2.val, hdecomp c2.2.val, hzlo, hzhi, hztop]
      have hylo_eq : (c1.1.val ^^^ c1.2.val) % 2 ^ (m + 1) = (c2.1.val ^^^ c2.2.val) % 2 ^ (m + 1) := by
        have hx := h12.2.1
        rw [hcm12] at hx
        have := congrArg (· ^^^ bitParallelBorrow m w2.val (c2.2.val % 2 ^ m)) hx
        simpa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] using this
      have hyhi_eq : ((c1.1.val ^^^ c1.2.val) / 2 ^ (m + 1)) % 2 ^ h =
          ((c2.1.val ^^^ c2.2.val) / 2 ^ (m + 1)) % 2 ^ h := by
        have hyt := h12.2.2.2
        rw [hcm12, hzhi] at hyt
        have := congrArg (· ^^^ ((bitParallelBorrow m w2.val (c2.2.val % 2 ^ m) / 2 ^ m % 2) *
            omegaMaskNat h (c2.2.val / 2 ^ m % 2 ^ h))) hyt
        simpa [h, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] using this
      have hy_eq : c1.1.val ^^^ c1.2.val = c2.1.val ^^^ c2.2.val := by
        have hlt1 : c1.1.val ^^^ c1.2.val < 2 ^ t := Nat.xor_lt_two_pow c1.1.isLt c1.2.isLt
        have hlt2 : c2.1.val ^^^ c2.2.val < 2 ^ t := Nat.xor_lt_two_pow c2.1.isLt c2.2.isLt
        have hdiv1 : (c1.1.val ^^^ c1.2.val) / 2 ^ (m + 1) < 2 ^ h := by
          have : 2 ^ t = 2 ^ (m + 1) * 2 ^ h := by rw [← pow_add]; congr 1; omega
          exact Nat.div_lt_of_lt_mul (by linarith)
        have hdiv2 : (c2.1.val ^^^ c2.2.val) / 2 ^ (m + 1) < 2 ^ h := by
          have : 2 ^ t = 2 ^ (m + 1) * 2 ^ h := by rw [← pow_add]; congr 1; omega
          exact Nat.div_lt_of_lt_mul (by linarith)
        rw [Nat.mod_eq_of_lt hdiv1, Nat.mod_eq_of_lt hdiv2] at hyhi_eq
        have d1 := Nat.div_add_mod (c1.1.val ^^^ c1.2.val) (2 ^ (m + 1))
        have d2 := Nat.div_add_mod (c2.1.val ^^^ c2.2.val) (2 ^ (m + 1))
        rw [hyhi_eq, hylo_eq] at d1
        omega
      apply Prod.ext _ hz_eq
      apply Fin.ext
      rw [hz_eq] at hy_eq
      have := congrArg (· ^^^ c2.2.val) hy_eq
      simpa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] using this
    simpa [Fintype.card_prod, Fintype.card_fin, ← pow_succ] using hinj
  have hsumU : ∑ ℓ' : (mechanismIICStar t m ht hm).L, ((mechanismIICStar t m ht hm).U ℓ').card =
      ∑ _ℓ' : (mechanismIICStar t m ht hm).L, 2 ^ (t - m) := by
    change (mechanismIICStar t m ht hm).totalRowLoad = _
    rw [mechanismIICStar_totalRowLoad, Finset.sum_const, Finset.card_univ,
        mechanismIICStar_card_L, smul_eq_mul, ← pow_add, ← pow_add]
    congr 1; omega
  have hsumV : ∑ ℓ' : (mechanismIICStar t m ht hm).L, ((mechanismIICStar t m ht hm).V ℓ').card =
      ∑ _ℓ' : (mechanismIICStar t m ht hm).L, 2 ^ (m + 1) := by
    change (mechanismIICStar t m ht hm).totalColLoad = _
    rw [mechanismIICStar_totalColLoad, Finset.sum_const, Finset.card_univ,
        mechanismIICStar_card_L, smul_eq_mul, ← pow_add, ← pow_add]
    congr 1; omega
  have hUeq : ∀ ℓ' ∈ (Finset.univ : Finset (mechanismIICStar t m ht hm).L),
      ((mechanismIICStar t m ht hm).U ℓ').card = 2 ^ (t - m) :=
    (Finset.sum_eq_sum_iff_of_le (fun ℓ' _ => hU_le ℓ')).mp hsumU
  have hVeq : ∀ ℓ' ∈ (Finset.univ : Finset (mechanismIICStar t m ht hm).L),
      ((mechanismIICStar t m ht hm).V ℓ').card = 2 ^ (m + 1) :=
    (Finset.sum_eq_sum_iff_of_le (fun ℓ' _ => hV_le ℓ')).mp hsumV
  exact ⟨hUeq ℓ (Finset.mem_univ _), hVeq ℓ (Finset.mem_univ _)⟩

/-! ### Theorem 2.4(b): Exact Cover Optimality across ALL Exact Covers -/

/-- Any exact biclique cover of a finite relation `R` satisfies `|E(R)| ≤ ∑_ℓ |U_ℓ| * |V_ℓ|`. -/
lemma exactBicliqueCover_edge_sum_ge {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] {R : α → β → Prop} [∀ r c, Decidable (R r c)]
    (C : ExactBicliqueCover R) :
    (Finset.univ.filter fun p : α × β => R p.1 p.2).card ≤
      ∑ ℓ : C.L, (C.U ℓ).card * (C.V ℓ).card := by
  have hsub : (Finset.univ.filter fun p : α × β => R p.1 p.2) ⊆
      Finset.univ.biUnion fun ℓ : C.L => C.U ℓ ×ˢ C.V ℓ := by
    intro ⟨r, c⟩ hp
    rw [Finset.mem_filter] at hp
    rcases C.covers r c hp.2 with ⟨ℓ, hr, hc⟩
    exact Finset.mem_biUnion.mpr ⟨ℓ, Finset.mem_univ _, Finset.mem_product.mpr ⟨hr, hc⟩⟩
  calc (Finset.univ.filter fun p : α × β => R p.1 p.2).card
      ≤ (Finset.univ.biUnion fun ℓ : C.L => C.U ℓ ×ˢ C.V ℓ).card := Finset.card_le_card hsub
    _ ≤ ∑ ℓ : C.L, (C.U ℓ ×ˢ C.V ℓ).card := Finset.card_biUnion_le
    _ = ∑ ℓ : C.L, (C.U ℓ).card * (C.V ℓ).card := by
        refine Finset.sum_congr rfl fun ℓ _ => Finset.card_product _ _

/-- Pure `ℕ` Cauchy–Schwarz + maximum-area inequality:
if `u_i * v_i ≤ A` for every `i`, then `(∑_i u_i * v_i)^2 ≤ A * (∑_i u_i) * (∑_i v_i)`. -/
lemma cauchy_schwarz_area_bound {ι : Type*} [Fintype ι] (u v : ι → ℕ) (A : ℕ)
    (hA : ∀ i, u i * v i ≤ A) :
    (∑ i : ι, u i * v i) ^ 2 ≤ A * (∑ i : ι, u i) * (∑ i : ι, v i) := by
  have hpair : ∀ i j : ι, 2 * ((u i * v i) * (u j * v j)) ≤ A * (u i * v j + u j * v i) := by
    intro i j
    have hsq : (2 * ((u i * v i) * (u j * v j))) ^ 2 ≤ (A * (u i * v j + u j * v i)) ^ 2 := by
      have h1 : (u i * v i) * (u j * v j) ≤ A * A := Nat.mul_le_mul (hA i) (hA j)
      have h2 : 4 * (u i * v j * (u j * v i)) ≤ (u i * v j + u j * v i) ^ 2 := by
        zify
        nlinarith [sq_nonneg ((u i : ℤ) * v j - (u j : ℤ) * v i)]
      have h3 : (u i * v i) * (u j * v j) = u i * v j * (u j * v i) := by ring
      calc (2 * ((u i * v i) * (u j * v j))) ^ 2
          = 4 * ((u i * v i) * (u j * v j)) * ((u i * v i) * (u j * v j)) := by ring
        _ ≤ 4 * (A * A) * ((u i * v i) * (u j * v j)) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 h1)
        _ = A ^ 2 * (4 * (u i * v j * (u j * v i))) := by rw [h3]; ring
        _ ≤ A ^ 2 * (u i * v j + u j * v i) ^ 2 := Nat.mul_le_mul_left _ h2
        _ = (A * (u i * v j + u j * v i)) ^ 2 := by ring
    by_contra hlt
    push Not at hlt
    have hpow := Nat.pow_lt_pow_left hlt (by omega : 2 ≠ 0)
    omega
  have hsum : ∑ i : ι, ∑ j : ι, 2 * ((u i * v i) * (u j * v j)) ≤
      ∑ i : ι, ∑ j : ι, A * (u i * v j + u j * v i) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j
  have hlhs : ∑ i : ι, ∑ j : ι, 2 * ((u i * v i) * (u j * v j)) =
      2 * (∑ i : ι, u i * v i) ^ 2 := by
    rw [sq, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  have hrhs : ∑ i : ι, ∑ j : ι, A * (u i * v j + u j * v i) =
      2 * (A * (∑ i : ι, u i) * (∑ j : ι, v j)) := by
    have h1 : ∑ i : ι, ∑ j : ι, u i * v j = (∑ i : ι, u i) * (∑ j : ι, v j) := by
      rw [Finset.sum_mul]; simp_rw [Finset.mul_sum]
    have h2 : ∑ i : ι, ∑ j : ι, u j * v i = (∑ i : ι, u i) * (∑ j : ι, v j) := by
      rw [Finset.sum_comm, Finset.sum_mul]; simp_rw [Finset.mul_sum]
    calc ∑ i : ι, ∑ j : ι, A * (u i * v j + u j * v i)
        = A * ∑ i : ι, ∑ j : ι, (u i * v j + u j * v i) := by
          simp_rw [← Finset.mul_sum]
      _ = A * ((∑ i : ι, ∑ j : ι, u i * v j) + (∑ i : ι, ∑ j : ι, u j * v i)) := by
          simp_rw [Finset.sum_add_distrib]
      _ = A * ((∑ i : ι, u i) * (∑ j : ι, v j) + (∑ i : ι, u i) * (∑ j : ι, v j)) := by
          rw [h1, h2]
      _ = 2 * (A * (∑ i : ι, u i) * (∑ j : ι, v j)) := by ring
  rw [hlhs, hrhs] at hsum
  omega

/-- Theorem 2.4(b) (Equation (2.10)): Biclique cover lower bound `bc(M_t) ≥ 2^(2t - 1)` for EVERY
exact cover (matched by the partition `mechanismIICStar`, so `bc(M_t) = cp(M_t) = 2^(2t - 1)`). -/
theorem bc_M_lower {t : ℕ} (ht : 1 ≤ t) (C : ExactBicliqueCover (M_rel t)) :
    2 ^ (2 * t - 1) ≤ Fintype.card C.L := by
  cases t with
  | zero => omega
  | succ s =>
    have hedges : 2 ^ (3 * (s + 1)) ≤ ∑ ℓ : C.L, (C.U ℓ).card * (C.V ℓ).card := by
      rw [← M_rel_edge_card (s + 1)]
      exact exactBicliqueCover_edge_sum_ge C
    have hsum_le : ∑ ℓ : C.L, (C.U ℓ).card * (C.V ℓ).card ≤ Fintype.card C.L * 2 ^ (s + 2) := by
      calc ∑ ℓ : C.L, (C.U ℓ).card * (C.V ℓ).card
          ≤ ∑ _ℓ : C.L, 2 ^ (s + 2) := Finset.sum_le_sum fun ℓ _ => M_rel_biclique_area_le s (C.isBiclique ℓ)
        _ = Fintype.card C.L * 2 ^ (s + 2) := by simp
    have hmul : 2 ^ (2 * (s + 1) - 1) * 2 ^ (s + 2) ≤ Fintype.card C.L * 2 ^ (s + 2) := by
      calc 2 ^ (2 * (s + 1) - 1) * 2 ^ (s + 2)
          = 2 ^ (3 * (s + 1)) := by rw [← pow_add]; congr 1; omega
        _ ≤ ∑ ℓ : C.L, (C.U ℓ).card * (C.V ℓ).card := hedges
        _ ≤ Fintype.card C.L * 2 ^ (s + 2) := hsum_le
    exact Nat.le_of_mul_le_mul_right hmul (by positivity)

/-- Theorem 2.4(b) (Equation (2.10)): Core biclique cover lower bound `bc(C_{s+1}) ≥ 2^(2s)` for EVERY exact cover. -/
theorem bc_K_lower (s : ℕ) (C : ExactBicliqueCover (K_coreRel s)) :
    2 ^ (2 * s) ≤ Fintype.card C.L := by
  have hedges : 2 ^ (3 * s) ≤ ∑ ℓ : C.L, (C.U ℓ).card * (C.V ℓ).card := by
    rw [← K_coreRel_edge_card s]
    exact exactBicliqueCover_edge_sum_ge C
  have hsum_le : ∑ ℓ : C.L, (C.U ℓ).card * (C.V ℓ).card ≤ Fintype.card C.L * 2 ^ s := by
    calc ∑ ℓ : C.L, (C.U ℓ).card * (C.V ℓ).card
        ≤ ∑ _ℓ : C.L, 2 ^ s := Finset.sum_le_sum fun ℓ _ => K_coreRel_biclique_area_le s (C.isBiclique ℓ)
      _ = Fintype.card C.L * 2 ^ s := by simp
  have hmul : 2 ^ (2 * s) * 2 ^ s ≤ Fintype.card C.L * 2 ^ s := by
    calc 2 ^ (2 * s) * 2 ^ s = 2 ^ (3 * s) := by rw [← pow_add]; congr 1; omega
      _ ≤ ∑ ℓ : C.L, (C.U ℓ).card * (C.V ℓ).card := hedges
      _ ≤ Fintype.card C.L * 2 ^ s := hsum_le
  exact Nat.le_of_mul_le_mul_right hmul (by positivity)

/-- Theorem 2.4(b) (Equation (2.11)): Universal product bound `totalRowLoad * totalColLoad ≥ 2^(5t - 1)`
(equivalently `E|A| * E|B| ≥ 2^(t - 1)`) across ALL exact covers of `M_t`. -/
theorem prod_load_M_lower {t : ℕ} (ht : 1 ≤ t) (C : ExactBicliqueCover (M_rel t)) :
    2 ^ (5 * t - 1) ≤ C.totalRowLoad * C.totalColLoad := by
  cases t with
  | zero => omega
  | succ s =>
    have hedges : 2 ^ (3 * (s + 1)) ≤ ∑ ℓ : C.L, (C.U ℓ).card * (C.V ℓ).card := by
      rw [← M_rel_edge_card (s + 1)]
      exact exactBicliqueCover_edge_sum_ge C
    have hcs := cauchy_schwarz_area_bound (fun ℓ => (C.U ℓ).card) (fun ℓ => (C.V ℓ).card)
      (2 ^ (s + 2)) (fun ℓ => M_rel_biclique_area_le s (C.isBiclique ℓ))
    have hmul : 2 ^ (s + 2) * 2 ^ (5 * (s + 1) - 1) ≤
        2 ^ (s + 2) * (C.totalRowLoad * C.totalColLoad) := by
      calc 2 ^ (s + 2) * 2 ^ (5 * (s + 1) - 1)
          = (2 ^ (3 * (s + 1))) ^ 2 := by rw [← pow_add, ← pow_mul]; congr 1; omega
        _ ≤ (∑ ℓ : C.L, (C.U ℓ).card * (C.V ℓ).card) ^ 2 := Nat.pow_le_pow_left hedges 2
        _ ≤ 2 ^ (s + 2) * C.totalRowLoad * C.totalColLoad := hcs
        _ = 2 ^ (s + 2) * (C.totalRowLoad * C.totalColLoad) := mul_assoc _ _ _
    exact Nat.le_of_mul_le_mul_left hmul (by positivity)

/-- Every cut `0 ≤ m ≤ t - 1` of Mechanism `II-C*` attains the exact product bound `2^(5t - 1)`. -/
theorem mechanismIICStar_prod_load_eq (t m : ℕ) (ht : 1 ≤ t) (hm : m ≤ t - 1) :
    (mechanismIICStar t m ht hm).totalRowLoad * (mechanismIICStar t m ht hm).totalColLoad =
      2 ^ (5 * t - 1) := by
  rw [mechanismIICStar_totalRowLoad, mechanismIICStar_totalColLoad]
  calc 2 ^ (2 * t) * 2 ^ (t - 1 - m) * (2 ^ (2 * t) * 2 ^ m)
      = 2 ^ (2 * t) * 2 ^ (2 * t) * (2 ^ (t - 1 - m) * 2 ^ m) := by ring
    _ = 2 ^ (2 * t + 2 * t) * 2 ^ (t - 1 - m + m) := by rw [← pow_add, ← pow_add]
    _ = 2 ^ (5 * t - 1) := by rw [← pow_add]; congr 1; omega

/-- Theorem 2.4(b) (Equation (2.11)): Core universal product bound `totalRowLoad * totalColLoad ≥ 2^(5s)`. -/
theorem prod_load_K_lower (s : ℕ) (C : ExactBicliqueCover (K_coreRel s)) :
    2 ^ (5 * s) ≤ C.totalRowLoad * C.totalColLoad := by
  have hedges : 2 ^ (3 * s) ≤ ∑ ℓ : C.L, (C.U ℓ).card * (C.V ℓ).card := by
    rw [← K_coreRel_edge_card s]
    exact exactBicliqueCover_edge_sum_ge C
  have hcs := cauchy_schwarz_area_bound (fun ℓ => (C.U ℓ).card) (fun ℓ => (C.V ℓ).card)
    (2 ^ s) (fun ℓ => K_coreRel_biclique_area_le s (C.isBiclique ℓ))
  have hmul : 2 ^ s * 2 ^ (5 * s) ≤ 2 ^ s * (C.totalRowLoad * C.totalColLoad) := by
    calc 2 ^ s * 2 ^ (5 * s)
        = (2 ^ (3 * s)) ^ 2 := by rw [← pow_add, ← pow_mul]; congr 1; omega
      _ ≤ (∑ ℓ : C.L, (C.U ℓ).card * (C.V ℓ).card) ^ 2 := Nat.pow_le_pow_left hedges 2
      _ ≤ 2 ^ s * C.totalRowLoad * C.totalColLoad := hcs
      _ = 2 ^ s * (C.totalRowLoad * C.totalColLoad) := mul_assoc _ _ _
  exact Nat.le_of_mul_le_mul_left hmul (by positivity)

/-- The discrete dyadic envelope `min_{0 ≤ m ≤ s} (α * 2^(s - m) + β * 2^m)`. -/
def minWeightedCut (s α β : ℕ) : ℕ :=
  (Finset.range (s + 1)).inf' Finset.nonempty_range_add_one fun m => α * 2 ^ (s - m) + β * 2 ^ m

lemma minWeightedCut_le (s α β m : ℕ) (hm : m ≤ s) :
    minWeightedCut s α β ≤ α * 2 ^ (s - m) + β * 2 ^ m :=
  Finset.inf'_le _ (Finset.mem_range.mpr (by omega))

lemma exists_minWeightedCut_attained (s α β : ℕ) :
    ∃ m ≤ s, α * 2 ^ (s - m) + β * 2 ^ m = minWeightedCut s α β := by
  rcases Finset.exists_mem_eq_inf' Finset.nonempty_range_add_one
      (fun m => α * 2 ^ (s - m) + β * 2 ^ m) with ⟨m, hm, heq⟩
  exact ⟨m, by have := Finset.mem_range.mp hm; omega, heq.symm⟩

/-- Theorem 2.4(b) (Equation (2.12)): Unconditional weighted-sum lower bound across ALL exact covers of `M_t`:
`min_{0 ≤ m ≤ t - 1} (α * 2^(t - 1 - m) + β * 2^m) * 2^(2t) ≤ α * totalRowLoad + β * totalColLoad`. -/
theorem weighted_sum_M_lower {t : ℕ} (ht : 1 ≤ t) (α β : ℕ)
    (C : ExactBicliqueCover (M_rel t)) :
    minWeightedCut (t - 1) α β * 2 ^ (2 * t) ≤ α * C.totalRowLoad + β * C.totalColLoad := by
  cases t with
  | zero => omega
  | succ s =>
    simp only [Nat.add_sub_cancel]
    have hterm : ∀ ℓ : C.L,
        minWeightedCut s α β * ((C.U ℓ).card * (C.V ℓ).card) ≤
          2 ^ (s + 1) * (α * (C.U ℓ).card + β * (C.V ℓ).card) := by
      intro ℓ
      by_cases hU : (C.U ℓ).Nonempty
      · by_cases hV : (C.V ℓ).Nonempty
        · rcases M_rel_nonempty_biclique_dyadic_bound s hU hV (C.isBiclique ℓ) with
            ⟨m, hm, hUm, hVm⟩
          have hmin := minWeightedCut_le s α β m hm
          have hVmul : 2 ^ (s - m) * (C.V ℓ).card ≤ 2 ^ (s + 1) := by
            calc 2 ^ (s - m) * (C.V ℓ).card
                ≤ 2 ^ (s - m) * 2 ^ (m + 1) := Nat.mul_le_mul_left _ hVm
              _ = 2 ^ (s + 1) := by rw [← pow_add]; congr 1; omega
          have hUmul : 2 ^ m * (C.U ℓ).card ≤ 2 ^ (s + 1) := by
            calc 2 ^ m * (C.U ℓ).card
                ≤ 2 ^ m * 2 ^ (s - m + 1) := Nat.mul_le_mul_left _ hUm
              _ = 2 ^ (s + 1) := by rw [← pow_add]; congr 1; omega
          calc minWeightedCut s α β * ((C.U ℓ).card * (C.V ℓ).card)
              ≤ (α * 2 ^ (s - m) + β * 2 ^ m) * ((C.U ℓ).card * (C.V ℓ).card) :=
                Nat.mul_le_mul_right _ hmin
            _ = α * (C.U ℓ).card * (2 ^ (s - m) * (C.V ℓ).card) +
                β * (C.V ℓ).card * (2 ^ m * (C.U ℓ).card) := by ring
            _ ≤ α * (C.U ℓ).card * 2 ^ (s + 1) + β * (C.V ℓ).card * 2 ^ (s + 1) :=
                Nat.add_le_add (Nat.mul_le_mul_left _ hVmul) (Nat.mul_le_mul_left _ hUmul)
            _ = 2 ^ (s + 1) * (α * (C.U ℓ).card + β * (C.V ℓ).card) := by ring
        · rw [Finset.not_nonempty_iff_eq_empty] at hV; simp [hV]
      · rw [Finset.not_nonempty_iff_eq_empty] at hU; simp [hU]
    have hedges : 2 ^ (3 * (s + 1)) ≤ ∑ ℓ : C.L, (C.U ℓ).card * (C.V ℓ).card := by
      rw [← M_rel_edge_card (s + 1)]
      exact exactBicliqueCover_edge_sum_ge C
    have hsum : minWeightedCut s α β * (2 ^ (2 * (s + 1)) * 2 ^ (s + 1)) ≤
        2 ^ (s + 1) * (α * C.totalRowLoad + β * C.totalColLoad) := by
      calc minWeightedCut s α β * (2 ^ (2 * (s + 1)) * 2 ^ (s + 1))
          = minWeightedCut s α β * 2 ^ (3 * (s + 1)) := by rw [← pow_add]; congr 2; omega
        _ ≤ minWeightedCut s α β * ∑ ℓ : C.L, (C.U ℓ).card * (C.V ℓ).card :=
            Nat.mul_le_mul_left _ hedges
        _ = ∑ ℓ : C.L, minWeightedCut s α β * ((C.U ℓ).card * (C.V ℓ).card) :=
            Finset.mul_sum _ _ _
        _ ≤ ∑ ℓ : C.L, 2 ^ (s + 1) * (α * (C.U ℓ).card + β * (C.V ℓ).card) :=
            Finset.sum_le_sum fun ℓ _ => hterm ℓ
        _ = 2 ^ (s + 1) * (α * C.totalRowLoad + β * C.totalColLoad) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
            rfl
    have hre : 2 ^ (s + 1) * (minWeightedCut s α β * 2 ^ (2 * (s + 1))) ≤
        2 ^ (s + 1) * (α * C.totalRowLoad + β * C.totalColLoad) := by
      calc 2 ^ (s + 1) * (minWeightedCut s α β * 2 ^ (2 * (s + 1)))
          = minWeightedCut s α β * (2 ^ (2 * (s + 1)) * 2 ^ (s + 1)) := by ring
        _ ≤ 2 ^ (s + 1) * (α * C.totalRowLoad + β * C.totalColLoad) := hsum
    exact Nat.le_of_mul_le_mul_left hre (by positivity)

/-- Theorem 2.4(b) (Equation (2.12)): `𝒫_m` (`mechanismIICStar`) attains equality for EVERY `(α, β)`. -/
theorem weighted_sum_M_attained {t : ℕ} (ht : 1 ≤ t) (α β : ℕ) :
    ∃ (m : ℕ) (hm : m ≤ t - 1),
      α * (mechanismIICStar t m ht hm).totalRowLoad +
        β * (mechanismIICStar t m ht hm).totalColLoad =
      minWeightedCut (t - 1) α β * 2 ^ (2 * t) := by
  rcases exists_minWeightedCut_attained (t - 1) α β with ⟨m, hm, heq⟩
  refine ⟨m, hm, ?_⟩
  rw [mechanismIICStar_totalRowLoad, mechanismIICStar_totalColLoad, ← heq]
  ring

/-- Theorem 2.4(b) (Equation (2.12)): Unconditional weighted-sum lower bound across ALL exact covers of `K_coreRel s`. -/
theorem weighted_sum_K_lower (s α β : ℕ) (C : ExactBicliqueCover (K_coreRel s)) :
    minWeightedCut s α β * 2 ^ (2 * s) ≤ α * C.totalRowLoad + β * C.totalColLoad := by
  have hterm : ∀ ℓ : C.L,
      minWeightedCut s α β * ((C.U ℓ).card * (C.V ℓ).card) ≤
        2 ^ s * (α * (C.U ℓ).card + β * (C.V ℓ).card) := by
    intro ℓ
    by_cases hU : (C.U ℓ).Nonempty
    · by_cases hV : (C.V ℓ).Nonempty
      · rcases K_coreRel_nonempty_biclique_dyadic_bound s hU hV (C.isBiclique ℓ) with
          ⟨a, ha, hUa, hVa⟩
        let m := s - a
        have hm : m ≤ s := Nat.sub_le s a
        have hmin := minWeightedCut_le s α β m hm
        have hsm : s - m = a := Nat.sub_sub_self ha
        have hVmul : 2 ^ (s - m) * (C.V ℓ).card ≤ 2 ^ s := by
          calc 2 ^ (s - m) * (C.V ℓ).card
              ≤ 2 ^ a * 2 ^ (s - a) := by rw [hsm]; exact Nat.mul_le_mul_left _ hVa
            _ = 2 ^ s := by rw [← pow_add, Nat.add_sub_cancel' ha]
        have hUmul : 2 ^ m * (C.U ℓ).card ≤ 2 ^ s := by
          calc 2 ^ m * (C.U ℓ).card
              ≤ 2 ^ (s - a) * 2 ^ a := Nat.mul_le_mul_left _ hUa
            _ = 2 ^ s := by rw [← pow_add, Nat.sub_add_cancel ha]
        calc minWeightedCut s α β * ((C.U ℓ).card * (C.V ℓ).card)
            ≤ (α * 2 ^ (s - m) + β * 2 ^ m) * ((C.U ℓ).card * (C.V ℓ).card) :=
              Nat.mul_le_mul_right _ hmin
          _ = α * (C.U ℓ).card * (2 ^ (s - m) * (C.V ℓ).card) +
              β * (C.V ℓ).card * (2 ^ m * (C.U ℓ).card) := by ring
          _ ≤ α * (C.U ℓ).card * 2 ^ s + β * (C.V ℓ).card * 2 ^ s :=
              Nat.add_le_add (Nat.mul_le_mul_left _ hVmul) (Nat.mul_le_mul_left _ hUmul)
          _ = 2 ^ s * (α * (C.U ℓ).card + β * (C.V ℓ).card) := by ring
      · rw [Finset.not_nonempty_iff_eq_empty] at hV; simp [hV]
    · rw [Finset.not_nonempty_iff_eq_empty] at hU; simp [hU]
  have hedges : 2 ^ (3 * s) ≤ ∑ ℓ : C.L, (C.U ℓ).card * (C.V ℓ).card := by
    rw [← K_coreRel_edge_card s]
    exact exactBicliqueCover_edge_sum_ge C
  have hsum : 2 ^ s * (minWeightedCut s α β * 2 ^ (2 * s)) ≤
      2 ^ s * (α * C.totalRowLoad + β * C.totalColLoad) := by
    calc 2 ^ s * (minWeightedCut s α β * 2 ^ (2 * s))
        = minWeightedCut s α β * 2 ^ (3 * s) := by
          rw [mul_left_comm, ← pow_add]; congr 2; omega
      _ ≤ minWeightedCut s α β * ∑ ℓ : C.L, (C.U ℓ).card * (C.V ℓ).card :=
          Nat.mul_le_mul_left _ hedges
      _ = ∑ ℓ : C.L, minWeightedCut s α β * ((C.U ℓ).card * (C.V ℓ).card) :=
          Finset.mul_sum _ _ _
      _ ≤ ∑ ℓ : C.L, 2 ^ s * (α * (C.U ℓ).card + β * (C.V ℓ).card) :=
          Finset.sum_le_sum fun ℓ _ => hterm ℓ
      _ = 2 ^ s * (α * C.totalRowLoad + β * C.totalColLoad) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          rfl
  exact Nat.le_of_mul_le_mul_left hsum (by positivity)

/-- Convexity of `m ↦ 2^(s - m) + 2^m`: the unweighted minimum occurs at `m = ⌊s/2⌋`. -/
theorem minWeightedCut_one_one (s : ℕ) :
    minWeightedCut s 1 1 = 2 ^ (s / 2) + 2 ^ ((s + 1) / 2) := by
  have hge : 2 ^ (s / 2) + 2 ^ ((s + 1) / 2) ≤ minWeightedCut s 1 1 := by
    unfold minWeightedCut
    rw [Finset.le_inf'_iff]
    intro m hm
    have hms : m ≤ s := by have := Finset.mem_range.mp hm; omega
    simp only [one_mul]
    by_cases hle : m ≤ s / 2
    · set d := s / 2 - m
      have h1 : 2 ^ (s / 2) = 2 ^ m * 2 ^ d := by rw [← pow_add]; congr 1; omega
      have h2 : 2 ^ (s - m) = 2 ^ ((s + 1) / 2) * 2 ^ d := by rw [← pow_add]; congr 1; omega
      have hpow_le : 2 ^ m ≤ 2 ^ ((s + 1) / 2) := Nat.pow_le_pow_right (by omega) (by omega)
      have h1le : 1 ≤ 2 ^ d := Nat.one_le_two_pow
      rw [h1, h2]
      nlinarith
    · set d := m - (s + 1) / 2
      have hm_ge : (s + 1) / 2 ≤ m := by omega
      have h1 : 2 ^ m = 2 ^ ((s + 1) / 2) * 2 ^ d := by rw [← pow_add]; congr 1; omega
      have h2 : 2 ^ (s / 2) = 2 ^ (s - m) * 2 ^ d := by rw [← pow_add]; congr 1; omega
      have hpow_le : 2 ^ (s - m) ≤ 2 ^ ((s + 1) / 2) := Nat.pow_le_pow_right (by omega) (by omega)
      have h1le : 1 ≤ 2 ^ d := Nat.one_le_two_pow
      rw [h1, h2]
      nlinarith
  have hle : minWeightedCut s 1 1 ≤ 2 ^ (s / 2) + 2 ^ ((s + 1) / 2) := by
    have h := minWeightedCut_le s 1 1 (s / 2) (Nat.div_le_self s 2)
    have hsub : s - s / 2 = (s + 1) / 2 := by omega
    simpa [hsub, add_comm] using h
  exact le_antisymm hle hge

/-- Theorem 2.4(b) (Equation (2.13)): Exact unweighted label-weight lower bound on `K_coreRel s`:
`W_label(C) ≥ (2^⌊s/2⌋ + 2^⌈s/2⌉) * 2^(2s)`. -/
theorem unweighted_labelWeight_K_lower (s : ℕ) (C : ExactBicliqueCover (K_coreRel s)) :
    (2 ^ (s / 2) + 2 ^ ((s + 1) / 2)) * 2 ^ (2 * s) ≤ C.labelWeight := by
  have h := weighted_sum_K_lower s 1 1 C
  rw [minWeightedCut_one_one, one_mul, one_mul] at h
  exact h

/-- Theorem 2.4(b) (Equation (2.13)): Exact unweighted label-weight lower bound on `M_rel t`:
`W_label(C) ≥ (2^⌊(t-1)/2⌋ + 2^⌈(t-1)/2⌉) * 2^(2t)`. -/
theorem unweighted_labelWeight_M_lower {t : ℕ} (ht : 1 ≤ t) (C : ExactBicliqueCover (M_rel t)) :
    (2 ^ ((t - 1) / 2) + 2 ^ (t / 2)) * 2 ^ (2 * t) ≤ C.labelWeight := by
  have h := weighted_sum_M_lower ht 1 1 C
  rw [minWeightedCut_one_one, one_mul, one_mul, show (t - 1 + 1) / 2 = t / 2 by omega] at h
  exact h

/-! ### Theorem 3.2: Exact Local Biclique Cover & Partition Numbers `lbc = lbp` for ALL `t ≥ 1` -/

/-- Theorem 3.2 (lower bound on `C_t`, Equation (3.1)): every exact cover of `K_coreRel s` with max load `≤ k`
satisfies `⌈(2^⌊s/2⌋ + 2^⌈s/2⌉) / 2⌉ ≤ k`. -/
theorem local_load_lower_K (s k : ℕ) (C : ExactBicliqueCover (K_coreRel s))
    (hk : C.HasMaxLoadLe k) :
    (2 ^ (s / 2) + 2 ^ ((s + 1) / 2) + 1) / 2 ≤ k := by
  have hrow : C.totalRowLoad ≤ 2 ^ (2 * s) * k := by
    rw [← ExactBicliqueCover.sum_rowLoad]
    calc ∑ r : (Fin s → ZMod 2) × Fin (2 ^ s), C.rowLoad r
        ≤ ∑ _r : (Fin s → ZMod 2) × Fin (2 ^ s), k := Finset.sum_le_sum fun r _ => hk.1 r
      _ = 2 ^ (2 * s) * k := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_pi,
            Fintype.card_fin, ZMod.card, Finset.prod_const, smul_eq_mul, ← pow_add,
            show s + s = 2 * s by omega]
  have hcol : C.totalColLoad ≤ 2 ^ (2 * s) * k := by
    rw [← ExactBicliqueCover.sum_colLoad]
    calc ∑ c : (Fin s → ZMod 2) × Fin (2 ^ s), C.colLoad c
        ≤ ∑ _c : (Fin s → ZMod 2) × Fin (2 ^ s), k := Finset.sum_le_sum fun c _ => hk.2 c
      _ = 2 ^ (2 * s) * k := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_pi,
            Fintype.card_fin, ZMod.card, Finset.prod_const, smul_eq_mul, ← pow_add,
            show s + s = 2 * s by omega]
  have hlb := unweighted_labelWeight_K_lower s C
  have h2k : (2 ^ (s / 2) + 2 ^ ((s + 1) / 2)) * 2 ^ (2 * s) ≤ (2 * k) * 2 ^ (2 * s) := by
    calc (2 ^ (s / 2) + 2 ^ ((s + 1) / 2)) * 2 ^ (2 * s)
        ≤ C.totalRowLoad + C.totalColLoad := hlb
      _ ≤ 2 ^ (2 * s) * k + 2 ^ (2 * s) * k := Nat.add_le_add hrow hcol
      _ = (2 * k) * 2 ^ (2 * s) := by ring
  have hle : 2 ^ (s / 2) + 2 ^ ((s + 1) / 2) ≤ 2 * k :=
    Nat.le_of_mul_le_mul_right h2k (by positivity)
  omega

/-- Theorem 3.2 (lower bound on `M_t`, Equation (3.1)): every exact cover of `M_rel t` (`t ≥ 1`) with
max load `≤ k` satisfies `⌈(2^⌊(t-1)/2⌋ + 2^⌈(t-1)/2⌉) / 2⌉ ≤ k`. -/
theorem local_load_lower_M {t : ℕ} (ht : 1 ≤ t) (k : ℕ) (C : ExactBicliqueCover (M_rel t))
    (hk : C.HasMaxLoadLe k) :
    (2 ^ ((t - 1) / 2) + 2 ^ (t / 2) + 1) / 2 ≤ k := by
  have hrow : C.totalRowLoad ≤ 2 ^ (2 * t) * k := by
    rw [← ExactBicliqueCover.sum_rowLoad]
    calc ∑ r : Fin (2 ^ t) × Fin (2 ^ t), C.rowLoad r
        ≤ ∑ _r : Fin (2 ^ t) × Fin (2 ^ t), k := Finset.sum_le_sum fun r _ => hk.1 r
      _ = 2 ^ (2 * t) * k := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            smul_eq_mul, ← pow_add, show t + t = 2 * t by omega]
  have hcol : C.totalColLoad ≤ 2 ^ (2 * t) * k := by
    rw [← ExactBicliqueCover.sum_colLoad]
    calc ∑ c : Fin (2 ^ t) × Fin (2 ^ t), C.colLoad c
        ≤ ∑ _c : Fin (2 ^ t) × Fin (2 ^ t), k := Finset.sum_le_sum fun c _ => hk.2 c
      _ = 2 ^ (2 * t) * k := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            smul_eq_mul, ← pow_add, show t + t = 2 * t by omega]
  have hlb := unweighted_labelWeight_M_lower ht C
  have h2k : (2 ^ ((t - 1) / 2) + 2 ^ (t / 2)) * 2 ^ (2 * t) ≤ (2 * k) * 2 ^ (2 * t) := by
    calc (2 ^ ((t - 1) / 2) + 2 ^ (t / 2)) * 2 ^ (2 * t)
        ≤ C.totalRowLoad + C.totalColLoad := hlb
      _ ≤ 2 ^ (2 * t) * k + 2 ^ (2 * t) * k := Nat.add_le_add hrow hcol
      _ = (2 * k) * 2 ^ (2 * t) := by ring
  have hle : 2 ^ ((t - 1) / 2) + 2 ^ (t / 2) ≤ 2 * k :=
    Nat.le_of_mul_le_mul_right h2k (by positivity)
  omega

/-- Lift ANY exact biclique cover (or partition) of `K_coreRel s` to `M_rel (s + 1)`
via `M_{s+1} ≅ I_2 ⊗ K_{s+1} ⊗ J_2`, preserving `IsPartition` and every vertex load. -/
def liftCoverKToM (s : ℕ) (C : ExactBicliqueCover (K_coreRel s)) :
    ExactBicliqueCover (M_rel (s + 1)) where
  L := Fin 2 × C.L
  U bl := liftM_U s bl.1 (C.U bl.2)
  V bl := liftM_V s bl.1 (C.V bl.2)
  isBiclique bl r hr c hc := by
    rw [liftM_U, Finset.mem_filter] at hr
    rw [liftM_V, Finset.mem_filter] at hc
    exact (M_rel_core_factorization s r c).mpr
      ⟨hr.2.1.trans hc.2.1.symm, C.isBiclique bl.2 _ hr.2.2 _ hc.2.2⟩
  covers r c hrc := by
    have ⟨hb, hcore⟩ := (M_rel_core_factorization s r c).mp hrc
    rcases C.covers _ _ hcore with ⟨ℓ, hr, hc⟩
    refine ⟨((phi_row s r).1, ℓ), ?_, ?_⟩
    · rw [liftM_U, Finset.mem_filter]; exact ⟨Finset.mem_univ _, rfl, hr⟩
    · rw [liftM_V, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hb.symm, hc⟩

theorem liftCoverKToM_isPartition (s : ℕ) (C : ExactBicliqueCover (K_coreRel s))
    (hp : C.IsPartition) : (liftCoverKToM s C).IsPartition := by
  intro r c hrc
  have ⟨hb, hcore⟩ := (M_rel_core_factorization s r c).mp hrc
  rcases hp _ _ hcore with ⟨ℓ0, ⟨hr0, hc0⟩, huniq⟩
  refine ⟨((phi_row s r).1, ℓ0), ?_, ?_⟩
  · constructor
    · simp [liftCoverKToM, liftM_U, hr0]
    · simp [liftCoverKToM, liftM_V, hb, hc0]
  · rintro ⟨b, ℓ⟩ ⟨hr, hc⟩
    simp only [liftCoverKToM, liftM_U, liftM_V, Finset.mem_filter, Finset.mem_univ, true_and] at hr hc
    exact Prod.ext hr.1.symm (huniq ℓ ⟨hr.2, hc.2⟩)

theorem liftCoverKToM_rowLoad (s : ℕ) (C : ExactBicliqueCover (K_coreRel s))
    (r : Fin (2 ^ (s + 1)) × Fin (2 ^ (s + 1))) :
    (liftCoverKToM s C).rowLoad r = C.rowLoad (phi_row s r).2.1 := by
  unfold ExactBicliqueCover.rowLoad liftCoverKToM
  dsimp only
  refine Finset.card_bij
    (fun bl _ => bl.2)
    (fun bl hbl => ?_)
    (fun bl1 h1 bl2 h2 h => ?_)
    (fun ℓ hℓ => ?_)
  · rw [Finset.mem_filter] at hbl ⊢
    rw [liftM_U, Finset.mem_filter] at hbl
    exact ⟨Finset.mem_univ _, hbl.2.2.2⟩
  · rw [Finset.mem_filter] at h1 h2
    rw [liftM_U, Finset.mem_filter] at h1 h2
    exact Prod.ext (h1.2.2.1.symm.trans h2.2.2.1) h
  · rw [Finset.mem_filter] at hℓ
    refine ⟨((phi_row s r).1, ℓ), ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [liftM_U, Finset.mem_filter]; exact ⟨Finset.mem_univ _, rfl, hℓ.2⟩⟩

theorem liftCoverKToM_colLoad (s : ℕ) (C : ExactBicliqueCover (K_coreRel s))
    (c : Fin (2 ^ (s + 1)) × Fin (2 ^ (s + 1))) :
    (liftCoverKToM s C).colLoad c = C.colLoad (phi_col s c).2.1 := by
  unfold ExactBicliqueCover.colLoad liftCoverKToM
  dsimp only
  refine Finset.card_bij
    (fun bl _ => bl.2)
    (fun bl hbl => ?_)
    (fun bl1 h1 bl2 h2 h => ?_)
    (fun ℓ hℓ => ?_)
  · rw [Finset.mem_filter] at hbl ⊢
    rw [liftM_V, Finset.mem_filter] at hbl
    exact ⟨Finset.mem_univ _, hbl.2.2.2⟩
  · rw [Finset.mem_filter] at h1 h2
    rw [liftM_V, Finset.mem_filter] at h1 h2
    exact Prod.ext (h1.2.2.1.symm.trans h2.2.2.1) h
  · rw [Finset.mem_filter] at hℓ
    refine ⟨((phi_col s c).1, ℓ), ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [liftM_V, Finset.mem_filter]; exact ⟨Finset.mem_univ _, rfl, hℓ.2⟩⟩

theorem liftCoverKToM_hasMaxLoadLe (s k : ℕ) (C : ExactBicliqueCover (K_coreRel s))
    (hk : C.HasMaxLoadLe k) : (liftCoverKToM s C).HasMaxLoadLe k :=
  ⟨fun r => by rw [liftCoverKToM_rowLoad]; exact hk.1 _,
   fun c => by rw [liftCoverKToM_colLoad]; exact hk.2 _⟩

/-! #### Projected Core Mechanism `II-C*` on `K_coreRel s` -/

/-- Label universe for core Mechanism `II-C*` at borrow width `s` and cut `0 ≤ m ≤ s`:
`{0..2^m - 1} × 𝔽₂^m × {0..2^(s-m) - 1} × 𝔽₂^(s-m)` (`2^(2s)` keys). -/
abbrev IICStarCoreLabel (s m : ℕ) : Type :=
  Fin (2 ^ m) × (Fin m → ZMod 2) × Fin (2 ^ (s - m)) × (Fin (s - m) → ZMod 2)

/-- Core Alice key map for `K_coreRel s` at cut `m ≤ s`. -/
def coreAliceKey (s m : ℕ) (hm : m ≤ s)
    (r : (Fin s → ZMod 2) × Fin (2 ^ s)) (q : Fin (2 ^ (s - m))) :
    IICStarCoreLabel s m :=
  let w_lo : Fin (2 ^ m) := ⟨r.2.val % 2 ^ m, Nat.mod_lt _ (by positivity)⟩
  let w_hi : Fin (2 ^ (s - m)) := ⟨r.2.val / 2 ^ m, by
    have hpow : 2 ^ s = 2 ^ m * 2 ^ (s - m) := by rw [← pow_add, Nat.add_sub_of_le hm]
    have hr := r.2.isLt
    exact Nat.div_lt_of_lt_mul (by linarith)⟩
  let x_lo : Fin m → ZMod 2 := fun i => r.1 ⟨i.val, by omega⟩
  let y_tilde : Fin (s - m) → ZMod 2 := fun j =>
    r.1 ⟨m + j.val, by omega⟩ + borrowVec (s - m) w_hi q j
  (w_lo, x_lo, q, y_tilde)

/-- Core Bob key map for `K_coreRel s` at cut `m ≤ s`. -/
def coreBobKey (s m : ℕ) (hm : m ≤ s)
    (c : (Fin s → ZMod 2) × Fin (2 ^ s)) (w_lo : Fin (2 ^ m)) :
    IICStarCoreLabel s m :=
  let z_lo : Fin (2 ^ m) := ⟨c.2.val % 2 ^ m, Nat.mod_lt _ (by positivity)⟩
  let z_hi : Fin (2 ^ (s - m)) := ⟨c.2.val / 2 ^ m, by
    have hpow : 2 ^ s = 2 ^ m * 2 ^ (s - m) := by rw [← pow_add, Nat.add_sub_of_le hm]
    have hc := c.2.isLt
    exact Nat.div_lt_of_lt_mul (by linarith)⟩
  let x_lo : Fin m → ZMod 2 := fun i =>
    c.1 ⟨i.val, by omega⟩ + borrowVec m w_lo z_lo i
  let c_m : ℕ := if z_lo.val < w_lo.val then 1 else 0
  let q : Fin (2 ^ (s - m)) := ⟨(z_hi.val + 2 ^ (s - m) - c_m) % 2 ^ (s - m), Nat.mod_lt _ (by positivity)⟩
  let y_tilde : Fin (s - m) → ZMod 2 := fun j =>
    c.1 ⟨m + j.val, by omega⟩ +
      if c_m = 1 ∧ z_hi.val % 2 ^ (j.val + 1) = 0 then (1 : ZMod 2) else 0
  (w_lo, x_lo, q, y_tilde)

lemma coreKey_eq_iff {s m : ℕ} (hm : m ≤ s)
    (r c : (Fin s → ZMod 2) × Fin (2 ^ s))
    (q : Fin (2 ^ (s - m))) (w_lo : Fin (2 ^ m)) :
    coreAliceKey s m hm r q = coreBobKey s m hm c w_lo ↔
      K_coreRel s r c ∧
      w_lo.val = r.2.val % 2 ^ m ∧
      q.val = (c.2.val / 2 ^ m + 2 ^ (s - m) -
        (if c.2.val % 2 ^ m < r.2.val % 2 ^ m then 1 else 0)) % 2 ^ (s - m) := by
  simp only [coreAliceKey, coreBobKey, Prod.mk.injEq, Fin.ext_iff]
  constructor
  · rintro ⟨hwlo, hxlo, hq, hyt⟩
    have hwlo' : w_lo.val = r.2.val % 2 ^ m := hwlo.symm
    have hq' : q.val = (c.2.val / 2 ^ m + 2 ^ (s - m) -
        (if c.2.val % 2 ^ m < r.2.val % 2 ^ m then 1 else 0)) % 2 ^ (s - m) := by
      rw [hq, hwlo']
    refine ⟨?_, hwlo', hq'⟩
    unfold K_coreRel
    funext i
    simp only [Pi.add_apply]
    by_cases him : i.val < m
    · have hi := congrFun hxlo ⟨i.val, him⟩
      simp only [borrowVec, borrowBit, hwlo',
        Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : i.val + 1 ≤ m))] at hi
      have h1 : r.1 i = c.1 i + borrowVec s r.2 c.2 i := hi
      rw [h1, add_assoc, add_comm (borrowVec s r.2 c.2 i), ← add_assoc,
          zmod2_add_self, zero_add]
    · set j := i.val - m
      have hj : j < s - m := by omega
      have hmj : m + j = i.val := by omega
      have hij := congrFun hyt ⟨j, hj⟩
      have hmq := modular_quotient_carry_identity (s := s) (m := m) (j := j + 1)
        hm (by omega) (by omega) r.2.isLt c.2.isLt
      dsimp only at hmq
      rw [show m + (j + 1) = i.val + 1 by omega, ← hq'] at hmq
      have hj_eq : (⟨m + j, by omega⟩ : Fin s) = i := Fin.ext hmj
      rw [hj_eq] at hij
      simp only [borrowVec, hwlo'] at hij ⊢
      have hsum : r.1 i + c.1 i =
          borrowBit (j + 1) (r.2.val / 2 ^ m) q.val +
          if (if c.2.val % 2 ^ m < r.2.val % 2 ^ m then 1 else 0) = 1 ∧
              c.2.val / 2 ^ m % 2 ^ (j + 1) = 0 then 1 else 0 := by
        calc r.1 i + c.1 i
            = (r.1 i + borrowBit (j + 1) (r.2.val / 2 ^ m) q.val) +
              (borrowBit (j + 1) (r.2.val / 2 ^ m) q.val + c.1 i) := by
              rw [← add_assoc, add_assoc (r.1 i), zmod2_add_self, add_zero]
          _ = (c.1 i + if (if c.2.val % 2 ^ m < r.2.val % 2 ^ m then 1 else 0) = 1 ∧
                  c.2.val / 2 ^ m % 2 ^ (j + 1) = 0 then 1 else 0) +
              (borrowBit (j + 1) (r.2.val / 2 ^ m) q.val + c.1 i) := by rw [hij]
          _ = (c.1 i + c.1 i) + (borrowBit (j + 1) (r.2.val / 2 ^ m) q.val +
              if (if c.2.val % 2 ^ m < r.2.val % 2 ^ m then 1 else 0) = 1 ∧
                  c.2.val / 2 ^ m % 2 ^ (j + 1) = 0 then 1 else 0) := by abel
          _ = _ := by rw [zmod2_add_self, zero_add]
      rw [hsum, ← hmq]
  · rintro ⟨hcore, hwlo', hq'⟩
    refine ⟨hwlo'.symm, ?_, ?_, ?_⟩
    · funext i
      have hi := congrFun hcore ⟨i.val, by omega⟩
      simp only [Pi.add_apply, borrowVec, borrowBit] at hi ⊢
      rw [hwlo', Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : i.val + 1 ≤ m)),
          Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : i.val + 1 ≤ m))]
      calc r.1 ⟨i.val, by omega⟩
          = r.1 ⟨i.val, by omega⟩ + (c.1 ⟨i.val, by omega⟩ + c.1 ⟨i.val, by omega⟩) := by
            rw [zmod2_add_self, add_zero]
        _ = c.1 ⟨i.val, by omega⟩ + (r.1 ⟨i.val, by omega⟩ + c.1 ⟨i.val, by omega⟩) := by abel
        _ = _ := by rw [hi]
    · rw [hq', hwlo']
    · funext j
      have hj := congrFun hcore ⟨m + j.val, by omega⟩
      simp only [Pi.add_apply, borrowVec] at hj ⊢
      have hmq := modular_quotient_carry_identity (s := s) (m := m) (j := j.val + 1)
        hm (by omega) (by omega) r.2.isLt c.2.isLt
      dsimp only at hmq
      rw [show m + (j.val + 1) = m + j.val + 1 by omega, ← hq'] at hmq
      rw [hwlo']
      calc r.1 ⟨m + j.val, by omega⟩ + borrowBit (j.val + 1) (r.2.val / 2 ^ m) q.val
          = (r.1 ⟨m + j.val, by omega⟩ + (c.1 ⟨m + j.val, by omega⟩ + c.1 ⟨m + j.val, by omega⟩)) +
            borrowBit (j.val + 1) (r.2.val / 2 ^ m) q.val := by rw [zmod2_add_self, add_zero]
        _ = c.1 ⟨m + j.val, by omega⟩ +
            ((r.1 ⟨m + j.val, by omega⟩ + c.1 ⟨m + j.val, by omega⟩) +
              borrowBit (j.val + 1) (r.2.val / 2 ^ m) q.val) := by abel
        _ = c.1 ⟨m + j.val, by omega⟩ +
            ((borrowBit (j.val + 1) (r.2.val / 2 ^ m) q.val +
              borrowBit (j.val + 1) (r.2.val / 2 ^ m) q.val) +
              if (if c.2.val % 2 ^ m < r.2.val % 2 ^ m then 1 else 0) = 1 ∧
                  c.2.val / 2 ^ m % 2 ^ (j.val + 1) = 0 then 1 else 0) := by
            rw [hj, hmq]; abel
        _ = _ := by rw [zmod2_add_self, zero_add]

/-- Projected Mechanism `II-C*` biclique partition on `K_coreRel s` for any `m ≤ s`. -/
def mechanismIICStarCore (s m : ℕ) (hm : m ≤ s) : ExactBicliqueCover (K_coreRel s) where
  L := IICStarCoreLabel s m
  U ℓ := Finset.univ.filter fun r => ∃ q : Fin (2 ^ (s - m)), coreAliceKey s m hm r q = ℓ
  V ℓ := Finset.univ.filter fun c => ∃ w_lo : Fin (2 ^ m), coreBobKey s m hm c w_lo = ℓ
  isBiclique ℓ r hr c hc := by
    rw [Finset.mem_filter] at hr hc
    rcases hr.2 with ⟨q, hq⟩
    rcases hc.2 with ⟨w_lo, hw⟩
    exact ((coreKey_eq_iff hm r c q w_lo).mp (hq.trans hw.symm)).1
  covers r c hrc := by
    let w_lo : Fin (2 ^ m) := ⟨r.2.val % 2 ^ m, Nat.mod_lt _ (by positivity)⟩
    let c_m : ℕ := if c.2.val % 2 ^ m < r.2.val % 2 ^ m then 1 else 0
    let q : Fin (2 ^ (s - m)) := ⟨(c.2.val / 2 ^ m + 2 ^ (s - m) - c_m) % 2 ^ (s - m),
      Nat.mod_lt _ (by positivity)⟩
    have heq := (coreKey_eq_iff hm r c q w_lo).mpr ⟨hrc, rfl, rfl⟩
    refine ⟨coreAliceKey s m hm r q, ?_, ?_⟩
    · rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, q, rfl⟩
    · rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, w_lo, heq.symm⟩

theorem mechanismIICStarCore_isPartition (s m : ℕ) (hm : m ≤ s) :
    (mechanismIICStarCore s m hm).IsPartition := by
  intro r c hrc
  let w_lo0 : Fin (2 ^ m) := ⟨r.2.val % 2 ^ m, Nat.mod_lt _ (by positivity)⟩
  let c_m : ℕ := if c.2.val % 2 ^ m < r.2.val % 2 ^ m then 1 else 0
  let q0 : Fin (2 ^ (s - m)) := ⟨(c.2.val / 2 ^ m + 2 ^ (s - m) - c_m) % 2 ^ (s - m),
    Nat.mod_lt _ (by positivity)⟩
  have heq0 := (coreKey_eq_iff hm r c q0 w_lo0).mpr ⟨hrc, rfl, rfl⟩
  refine ⟨coreAliceKey s m hm r q0, ?_, ?_⟩
  · constructor
    · simp only [mechanismIICStarCore, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨q0, rfl⟩
    · simp only [mechanismIICStarCore, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨w_lo0, heq0.symm⟩
  · rintro ℓ ⟨hU, hV⟩
    simp only [mechanismIICStarCore, Finset.mem_filter, Finset.mem_univ, true_and] at hU hV
    rcases hU with ⟨q, hq⟩
    rcases hV with ⟨w_lo, hw⟩
    have hmatch := (coreKey_eq_iff hm r c q w_lo).mp (hq.trans hw.symm)
    have hq_eq : q = q0 := Fin.ext hmatch.2.2
    rw [← hq, hq_eq]

theorem mechanismIICStarCore_rowLoad (s m : ℕ) (hm : m ≤ s)
    (r : (Fin s → ZMod 2) × Fin (2 ^ s)) :
    (mechanismIICStarCore s m hm).rowLoad r = 2 ^ (s - m) := by
  unfold ExactBicliqueCover.rowLoad mechanismIICStarCore
  dsimp only
  have hbij : (Finset.univ.filter fun ℓ : IICStarCoreLabel s m =>
      r ∈ Finset.univ.filter fun r' => ∃ q, coreAliceKey s m hm r' q = ℓ).card =
      (Finset.univ : Finset (Fin (2 ^ (s - m)))).card := by
    refine Finset.card_bij
      (fun ℓ _ => ℓ.2.2.1)
      (fun _ _ => Finset.mem_univ _)
      (fun ℓ1 h1 ℓ2 h2 h => ?_)
      (fun q _ => ?_)
    · rw [Finset.mem_filter] at h1 h2
      rcases (Finset.mem_filter.mp h1.2).2 with ⟨q1, hq1⟩
      rcases (Finset.mem_filter.mp h2.2).2 with ⟨q2, hq2⟩
      have eq1 : ℓ1.2.2.1 = q1 := by rw [← hq1]; rfl
      have eq2 : ℓ2.2.2.1 = q2 := by rw [← hq2]; rfl
      rw [← hq1, ← hq2, eq1.symm.trans (h.trans eq2)]
    · refine ⟨coreAliceKey s m hm r q, ?_, rfl⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, q, rfl⟩⟩
  simpa using hbij

theorem mechanismIICStarCore_colLoad (s m : ℕ) (hm : m ≤ s)
    (c : (Fin s → ZMod 2) × Fin (2 ^ s)) :
    (mechanismIICStarCore s m hm).colLoad c = 2 ^ m := by
  unfold ExactBicliqueCover.colLoad mechanismIICStarCore
  dsimp only
  have hbij : (Finset.univ.filter fun ℓ : IICStarCoreLabel s m =>
      c ∈ Finset.univ.filter fun c' => ∃ w_lo, coreBobKey s m hm c' w_lo = ℓ).card =
      (Finset.univ : Finset (Fin (2 ^ m))).card := by
    refine Finset.card_bij
      (fun ℓ _ => ℓ.1)
      (fun _ _ => Finset.mem_univ _)
      (fun ℓ1 h1 ℓ2 h2 h => ?_)
      (fun w_lo _ => ?_)
    · rw [Finset.mem_filter] at h1 h2
      rcases (Finset.mem_filter.mp h1.2).2 with ⟨w1, hw1⟩
      rcases (Finset.mem_filter.mp h2.2).2 with ⟨w2, hw2⟩
      have eq1 : ℓ1.1 = w1 := by rw [← hw1]; rfl
      have eq2 : ℓ2.1 = w2 := by rw [← hw2]; rfl
      rw [← hw1, ← hw2, eq1.symm.trans (h.trans eq2)]
    · refine ⟨coreBobKey s m hm c w_lo, ?_, rfl⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, w_lo, rfl⟩⟩
  simpa using hbij

/-! #### General Odd-`s` Non-Equivariant Lift-Colored Balanced Star-Blowup Partition -/

/-- Split a `(2r + 1)`-bit core vertex `(x_full, w_full)` into lower `2r`-bit vertex `u0`. -/
def oddCoreLow (r : ℕ) (p : (Fin (2 * r + 1) → ZMod 2) × Fin (2 ^ (2 * r + 1))) :
    (Fin (2 * r) → ZMod 2) × Fin (2 ^ (2 * r)) :=
  (fun i => p.1 i.castSucc, ⟨p.2.val % 2 ^ (2 * r), Nat.mod_lt _ (by positivity)⟩)

/-- Top coordinate bit `a = w_{2r}` (or `b = z_{2r}`) in `ZMod 2`. -/
def oddCoreTopBit (r : ℕ) (p : (Fin (2 * r + 1) → ZMod 2) × Fin (2 ^ (2 * r + 1))) : ZMod 2 :=
  if p.2.val / 2 ^ (2 * r) = 1 then 1 else 0

/-- Top XOR bit `X = x_{2r+1}` (or `Y = y_{2r+1}`) in `ZMod 2`. -/
def oddCoreTopXor (r : ℕ) (p : (Fin (2 * r + 1) → ZMod 2) × Fin (2 ^ (2 * r + 1))) : ZMod 2 :=
  p.1 (Fin.last (2 * r))

/-- Top carry equation (Equation (3.2) of Paper 2) decomposing `K_coreRel (2r + 1)` over `K_coreRel (2r)`. -/
lemma K_coreRel_odd_split (r : ℕ)
    (u v : (Fin (2 * r + 1) → ZMod 2) × Fin (2 ^ (2 * r + 1))) :
    K_coreRel (2 * r + 1) u v ↔
      K_coreRel (2 * r) (oddCoreLow r u) (oddCoreLow r v) ∧
      oddCoreTopXor r u + oddCoreTopXor r v =
        oddCoreTopBit r u * (1 + oddCoreTopBit r v) +
        (1 + oddCoreTopBit r u + oddCoreTopBit r v) *
          borrowBit (2 * r) (oddCoreLow r u).2.val (oddCoreLow r v).2.val := by
  have hpow : 2 ^ (2 * r + 1) = 2 * 2 ^ (2 * r) := by rw [pow_succ']
  have hdiv_u : u.2.val / 2 ^ (2 * r) < 2 := Nat.div_lt_of_lt_mul (by have := u.2.isLt; linarith)
  have hdiv_v : v.2.val / 2 ^ (2 * r) < 2 := Nat.div_lt_of_lt_mul (by have := v.2.isLt; linarith)
  have hu_eq : u.2.val = u.2.val % 2 ^ (2 * r) + (u.2.val / 2 ^ (2 * r)) * 2 ^ (2 * r) := by
    have := Nat.div_add_mod u.2.val (2 ^ (2 * r)); linarith
  have hv_eq : v.2.val = v.2.val % 2 ^ (2 * r) + (v.2.val / 2 ^ (2 * r)) * 2 ^ (2 * r) := by
    have := Nat.div_add_mod v.2.val (2 ^ (2 * r)); linarith
  have htop_borrow : borrowBit (2 * r + 1) u.2.val v.2.val =
      oddCoreTopBit r u * (1 + oddCoreTopBit r v) +
      (1 + oddCoreTopBit r u + oddCoreTopBit r v) *
        borrowBit (2 * r) (oddCoreLow r u).2.val (oddCoreLow r v).2.val := by
    unfold borrowBit oddCoreTopBit oddCoreLow
    rw [Nat.mod_eq_of_lt u.2.isLt, Nat.mod_eq_of_lt v.2.isLt,
        Nat.mod_mod_of_dvd _ dvd_rfl, Nat.mod_mod_of_dvd _ dvd_rfl]
    have hlt_u : u.2.val % 2 ^ (2 * r) < 2 ^ (2 * r) := Nat.mod_lt _ (by positivity)
    have hlt_v : v.2.val % 2 ^ (2 * r) < 2 ^ (2 * r) := Nat.mod_lt _ (by positivity)
    have hcases_u : u.2.val / 2 ^ (2 * r) = 0 ∨ u.2.val / 2 ^ (2 * r) = 1 := by
      rcases h : u.2.val / 2 ^ (2 * r) with _ | _ | _
      · exact Or.inl rfl
      · exact Or.inr rfl
      · omega
    have hcases_v : v.2.val / 2 ^ (2 * r) = 0 ∨ v.2.val / 2 ^ (2 * r) = 1 := by
      rcases h : v.2.val / 2 ^ (2 * r) with _ | _ | _
      · exact Or.inl rfl
      · exact Or.inr rfl
      · omega
    rcases hcases_u with hu0 | hu1 <;> rcases hcases_v with hv0 | hv1
    · have hu' : u.2.val = u.2.val % 2 ^ (2 * r) := by
        calc u.2.val = u.2.val % 2 ^ (2 * r) + (u.2.val / 2 ^ (2 * r)) * 2 ^ (2 * r) := hu_eq
          _ = u.2.val % 2 ^ (2 * r) + 0 * 2 ^ (2 * r) := by rw [hu0]
          _ = u.2.val % 2 ^ (2 * r) := by simp
      have hv' : v.2.val = v.2.val % 2 ^ (2 * r) := by
        calc v.2.val = v.2.val % 2 ^ (2 * r) + (v.2.val / 2 ^ (2 * r)) * 2 ^ (2 * r) := hv_eq
          _ = v.2.val % 2 ^ (2 * r) + 0 * 2 ^ (2 * r) := by rw [hv0]
          _ = v.2.val % 2 ^ (2 * r) := by simp
      simp only [hu0, hv0, zero_ne_one, ↓reduceIte, zero_mul, zero_add, add_zero, one_mul]
      rw [← hu', ← hv']
    · have hu' : u.2.val = u.2.val % 2 ^ (2 * r) := by
        calc u.2.val = u.2.val % 2 ^ (2 * r) + (u.2.val / 2 ^ (2 * r)) * 2 ^ (2 * r) := hu_eq
          _ = u.2.val % 2 ^ (2 * r) + 0 * 2 ^ (2 * r) := by rw [hu0]
          _ = u.2.val % 2 ^ (2 * r) := by simp
      have hv' : v.2.val = v.2.val % 2 ^ (2 * r) + 2 ^ (2 * r) := by
        calc v.2.val = v.2.val % 2 ^ (2 * r) + (v.2.val / 2 ^ (2 * r)) * 2 ^ (2 * r) := hv_eq
          _ = v.2.val % 2 ^ (2 * r) + 1 * 2 ^ (2 * r) := by rw [hv1]
          _ = v.2.val % 2 ^ (2 * r) + 2 ^ (2 * r) := by rw [one_mul]
      have hnot : ¬ (v.2.val < u.2.val) := by omega
      simp only [hu0, hv1, zero_ne_one, ↓reduceIte, hnot, zero_mul, add_zero, zmod2_add_self]
    · have hu' : u.2.val = u.2.val % 2 ^ (2 * r) + 2 ^ (2 * r) := by
        calc u.2.val = u.2.val % 2 ^ (2 * r) + (u.2.val / 2 ^ (2 * r)) * 2 ^ (2 * r) := hu_eq
          _ = u.2.val % 2 ^ (2 * r) + 1 * 2 ^ (2 * r) := by rw [hu1]
          _ = u.2.val % 2 ^ (2 * r) + 2 ^ (2 * r) := by rw [one_mul]
      have hv' : v.2.val = v.2.val % 2 ^ (2 * r) := by
        calc v.2.val = v.2.val % 2 ^ (2 * r) + (v.2.val / 2 ^ (2 * r)) * 2 ^ (2 * r) := hv_eq
          _ = v.2.val % 2 ^ (2 * r) + 0 * 2 ^ (2 * r) := by rw [hv0]
          _ = v.2.val % 2 ^ (2 * r) := by simp
      have hlt : v.2.val < u.2.val := by omega
      simp only [hu1, hv0, zero_ne_one, ↓reduceIte, hlt, add_zero, mul_one, zmod2_add_self,
        zero_mul]
    · have hu' : u.2.val = u.2.val % 2 ^ (2 * r) + 2 ^ (2 * r) := by
        calc u.2.val = u.2.val % 2 ^ (2 * r) + (u.2.val / 2 ^ (2 * r)) * 2 ^ (2 * r) := hu_eq
          _ = u.2.val % 2 ^ (2 * r) + 1 * 2 ^ (2 * r) := by rw [hu1]
          _ = u.2.val % 2 ^ (2 * r) + 2 ^ (2 * r) := by rw [one_mul]
      have hv' : v.2.val = v.2.val % 2 ^ (2 * r) + 2 ^ (2 * r) := by
        calc v.2.val = v.2.val % 2 ^ (2 * r) + (v.2.val / 2 ^ (2 * r)) * 2 ^ (2 * r) := hv_eq
          _ = v.2.val % 2 ^ (2 * r) + 1 * 2 ^ (2 * r) := by rw [hv1]
          _ = v.2.val % 2 ^ (2 * r) + 2 ^ (2 * r) := by rw [one_mul]
      have hiff : v.2.val < u.2.val ↔ v.2.val % 2 ^ (2 * r) < u.2.val % 2 ^ (2 * r) := by omega
      simp only [hu1, hv1, ↓reduceIte, zmod2_add_self, mul_zero, zero_add, one_mul, hiff]
  constructor
  · intro h
    constructor
    · unfold K_coreRel oddCoreLow
      funext i
      have hi := congrFun h i.castSucc
      simp only [Pi.add_apply, borrowVec, borrowBit, Fin.val_castSucc] at hi ⊢
      have hdvd : 2 ^ (i.val + 1) ∣ 2 ^ (2 * r) := Nat.pow_dvd_pow 2 (by omega)
      simp only [Nat.mod_mod_of_dvd _ hdvd]
      exact hi
    · have hlast := congrFun h (Fin.last (2 * r))
      simp only [Pi.add_apply, borrowVec, Fin.val_last] at hlast
      rw [← htop_borrow]
      exact hlast
  · rintro ⟨hlow, htop⟩
    unfold K_coreRel
    funext i
    refine Fin.lastCases ?_ ?_ i
    · simp only [Pi.add_apply, borrowVec, Fin.val_last]
      rw [htop_borrow]
      exact htop
    · intro j
      have hj := congrFun hlow j
      simp only [Pi.add_apply, borrowVec, borrowBit, oddCoreLow, Fin.val_castSucc] at hj ⊢
      have hdvd : 2 ^ (j.val + 1) ∣ 2 ^ (2 * r) := Nat.pow_dvd_pow 2 (by omega)
      simp only [Nat.mod_mod_of_dvd _ hdvd] at hj
      exact hj

/-- Step 1 (Non-equivariant balanced coloring): `f(ℓ_0) = q_0 ⊕ x_r ⊕ w_0 ∈ 𝔽₂` (Theorem 3.2, Step 1). -/
def starColor (r : ℕ) (hr : 1 ≤ r) (ℓ0 : IICStarCoreLabel (2 * r) r) : ZMod 2 :=
  ((ℓ0.2.2.1.val % 2 : ℕ) : ZMod 2) + ℓ0.2.1 ⟨r - 1, by omega⟩ + ((ℓ0.1.val % 2 : ℕ) : ZMod 2)

/-- Counting parity in `Fin (2^r)` for `r ≥ 1`: exactly `2^(r - 1)` elements have each parity. -/
lemma card_fin_two_pow_parity {r : ℕ} (hr : 1 ≤ r) (b : ZMod 2) :
    (Finset.univ.filter fun x : Fin (2 ^ r) => ((x.val % 2 : ℕ) : ZMod 2) = b).card =
      2 ^ (r - 1) := by
  have hpow : 2 ^ r = 2 * 2 ^ (r - 1) := by
    rw [← pow_succ', show r - 1 + 1 = r by omega]
  have hbij : (Finset.univ.filter fun x : Fin (2 ^ r) => ((x.val % 2 : ℕ) : ZMod 2) = b).card =
      (Finset.univ : Finset (Fin (2 ^ (r - 1)))).card := by
    refine Finset.card_bij
      (fun x _ => ⟨x.val / 2, by have := x.isLt; omega⟩)
      (fun _ _ => Finset.mem_univ _)
      (fun x1 hx1 x2 hx2 h => ?_)
      (fun k _ => ?_)
    · rw [Finset.mem_filter] at hx1 hx2
      have hdiv : x1.val / 2 = x2.val / 2 := congrArg Fin.val h
      have hmod : x1.val % 2 = x2.val % 2 := by
        have heq : ((x1.val % 2 : ℕ) : ZMod 2) = ((x2.val % 2 : ℕ) : ZMod 2) :=
          hx1.2.trans hx2.2.symm
        have h1 : x1.val % 2 < 2 := Nat.mod_lt _ (by omega)
        have h2 : x2.val % 2 < 2 := Nat.mod_lt _ (by omega)
        interval_cases (x1.val % 2) <;> interval_cases (x2.val % 2) <;> first | rfl | exact absurd heq (by decide)
      apply Fin.ext; omega
    · refine ⟨⟨2 * k.val + b.val, by have := k.isLt; have := b.val_lt; omega⟩, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have hb := b.val_lt
        have hm : (2 * k.val + b.val) % 2 = b.val := by omega
        rw [hm]; exact ZMod.natCast_zmod_val b
      · apply Fin.ext
        have hb := b.val_lt
        dsimp only; omega
  simpa using hbij

/-- Step 2 (Local bijective coordinates on Alice's side): unilateral row borrow when `q < 2^r - 1`. -/
def starAliceLoc (r : ℕ)
    (u : (Fin (2 * r + 1) → ZMod 2) × Fin (2 ^ (2 * r + 1)))
    (q : Fin (2 ^ (2 * r - r))) : ZMod 2 × ZMod 2 :=
  let a := oddCoreTopBit r u
  let x := oddCoreTopXor r u
  if q.val < 2 ^ r - 1 then
    let cRow : ZMod 2 := if q.val < (oddCoreLow r u).2.val / 2 ^ r then 1 else 0
    (a + cRow, x + a + cRow + a * cRow)
  else (a, x)

/-- Step 2 (Local bijective coordinates on Bob's side): unilateral column borrow when `q = 2^r - 1`. -/
def starBobLoc (r : ℕ)
    (v : (Fin (2 * r + 1) → ZMod 2) × Fin (2 ^ (2 * r + 1)))
    (w_lo : Fin (2 ^ r)) (q : Fin (2 ^ (2 * r - r))) : ZMod 2 × ZMod 2 :=
  let b := oddCoreTopBit r v
  let y := oddCoreTopXor r v
  if q.val < 2 ^ r - 1 then
    (1 + b, y)
  else
    let dCol : ZMod 2 :=
      if (oddCoreLow r v).2.val % 2 ^ r < w_lo.val ∧ (oddCoreLow r v).2.val / 2 ^ r = 0
      then 1 else 0
    (b + dCol, y + dCol * (1 + b))

/-- Step 2 algebraic equivalence: on every matched base block `(u0, v0) ∈ U_{ℓ_0} × V_{ℓ_0}`,
the local coordinates `(A, X')` and `(B, Y')` transform Equation (3.2) into `X' + Y' = A * (1 + B)`. -/
lemma starBlowup_local_iff {r : ℕ} (hr : 1 ≤ r)
    (u v : (Fin (2 * r + 1) → ZMod 2) × Fin (2 ^ (2 * r + 1)))
    (q : Fin (2 ^ (2 * r - r))) (w_lo : Fin (2 ^ r))
    (hmatch : coreAliceKey (2 * r) r (by omega) (oddCoreLow r u) q =
              coreBobKey (2 * r) r (by omega) (oddCoreLow r v) w_lo) :
    (starAliceLoc r u q).2 + (starBobLoc r v w_lo q).2 =
      (starAliceLoc r u q).1 * (1 + (starBobLoc r v w_lo q).1) ↔
    oddCoreTopXor r u + oddCoreTopXor r v =
      oddCoreTopBit r u * (1 + oddCoreTopBit r v) +
      (1 + oddCoreTopBit r u + oddCoreTopBit r v) *
        borrowBit (2 * r) (oddCoreLow r u).2.val (oddCoreLow r v).2.val := by
  have hm := (coreKey_eq_iff (by omega : r ≤ 2 * r) (oddCoreLow r u) (oddCoreLow r v) q w_lo).mp hmatch
  have hwlo_val : w_lo.val = (oddCoreLow r u).2.val % 2 ^ r := hm.2.1
  have hsub_r : 2 * r - r = r := by omega
  have hq_val : q.val = ((oddCoreLow r v).2.val / 2 ^ r + 2 ^ r -
      (if (oddCoreLow r v).2.val % 2 ^ r < (oddCoreLow r u).2.val % 2 ^ r then 1 else 0)) % 2 ^ r := by
    simpa [hsub_r] using hm.2.2
  have hmq := modular_quotient_carry_identity (s := 2 * r) (m := r) (j := r)
    (by omega) hr (by omega) (oddCoreLow r u).2.isLt (oddCoreLow r v).2.isLt
  dsimp only at hmq
  have h2r : r + r = 2 * r := by omega
  rw [h2r, hsub_r, ← hq_val] at hmq
  have hw_hi_lt : (oddCoreLow r u).2.val / 2 ^ r < 2 ^ r := by
    have hpow : 2 ^ (2 * r) = 2 ^ r * 2 ^ r := by rw [← pow_add, h2r]
    exact Nat.div_lt_of_lt_mul (by have := (oddCoreLow r u).2.isLt; linarith)
  have hz_hi_lt : (oddCoreLow r v).2.val / 2 ^ r < 2 ^ r := by
    have hpow : 2 ^ (2 * r) = 2 ^ r * 2 ^ r := by rw [← pow_add, h2r]
    exact Nat.div_lt_of_lt_mul (by have := (oddCoreLow r v).2.isLt; linarith)
  have hq_lt : q.val < 2 ^ r := by simpa [hsub_r] using q.isLt
  have hbr_eq : borrowBit r ((oddCoreLow r u).2.val / 2 ^ r) q.val =
      if q.val < (oddCoreLow r u).2.val / 2 ^ r then 1 else 0 := by
    unfold borrowBit
    rw [Nat.mod_eq_of_lt hw_hi_lt, Nat.mod_eq_of_lt hq_lt]
  have hmodz : ((oddCoreLow r v).2.val / 2 ^ r) % 2 ^ r = (oddCoreLow r v).2.val / 2 ^ r :=
    Nat.mod_eq_of_lt hz_hi_lt
  rw [hbr_eq, hmodz] at hmq
  unfold starAliceLoc starBobLoc
  by_cases hq_small : q.val < 2 ^ r - 1
  · -- Case 1: q < 2^r - 1 (row-borrow case)
    have hno_wrap : ¬ ((if (oddCoreLow r v).2.val % 2 ^ r < (oddCoreLow r u).2.val % 2 ^ r then 1 else 0) = 1 ∧
        (oddCoreLow r v).2.val / 2 ^ r = 0) := by
      rintro ⟨hcm1, hz0⟩
      rw [hcm1, hz0, zero_add, Nat.mod_eq_of_lt (by have : 1 ≤ 2 ^ r := Nat.one_le_two_pow; omega)] at hq_val
      omega
    have heta : borrowBit (2 * r) (oddCoreLow r u).2.val (oddCoreLow r v).2.val =
        if q.val < (oddCoreLow r u).2.val / 2 ^ r then 1 else 0 := by
      rw [hmq]; simp only [hno_wrap, ↓reduceIte, add_zero]
    simp only [hq_small, ↓reduceIte, heta]
    generalize oddCoreTopBit r u = a
    generalize oddCoreTopBit r v = b
    generalize oddCoreTopXor r u = x
    generalize oddCoreTopXor r v = y
    generalize (if q.val < (oddCoreLow r u).2.val / 2 ^ r then (1 : ZMod 2) else 0) = C
    fin_cases a <;> fin_cases b <;> fin_cases x <;> fin_cases y <;> fin_cases C <;> decide
  · -- Case 2: q = 2^r - 1 (column-borrow case)
    have hq_max : q.val = 2 ^ r - 1 := by omega
    have hno_row : ¬ (q.val < (oddCoreLow r u).2.val / 2 ^ r) := by omega
    have heta : borrowBit (2 * r) (oddCoreLow r u).2.val (oddCoreLow r v).2.val =
        if (oddCoreLow r v).2.val % 2 ^ r < w_lo.val ∧ (oddCoreLow r v).2.val / 2 ^ r = 0
        then 1 else 0 := by
      rw [hmq, hwlo_val]
      simp only [hno_row, ↓reduceIte, zero_add]
      by_cases hlt : (oddCoreLow r v).2.val % 2 ^ r < (oddCoreLow r u).2.val % 2 ^ r
      · simp [hlt]
      · simp [hlt]
    simp only [hq_small, ↓reduceIte, heta]
    generalize oddCoreTopBit r u = a
    generalize oddCoreTopBit r v = b
    generalize oddCoreTopXor r u = x
    generalize oddCoreTopXor r v = y
    generalize (if (oddCoreLow r v).2.val % 2 ^ r < w_lo.val ∧
        (oddCoreLow r v).2.val / 2 ^ r = 0 then (1 : ZMod 2) else 0) = D
    fin_cases a <;> fin_cases b <;> fin_cases x <;> fin_cases y <;> fin_cases D <;> decide

/-- Theorem 3.2: General non-equivariant lift-colored balanced 4-star blowup
partition of `K_coreRel (2r + 1)` for EVERY `r ≥ 1`, with exact vertex load `3 * 2^(r - 1)`
at every row and every column! -/
def starBlowupPartition (r : ℕ) (hr : 1 ≤ r) : ExactBicliqueCover (K_coreRel (2 * r + 1)) where
  L := IICStarCoreLabel (2 * r) r × ZMod 2 × ZMod 2
  decEqL :=
    letI : DecidableEq (IICStarCoreLabel (2 * r) r) := inferInstance
    inferInstance
  U ℓ := Finset.univ.filter fun u =>
    ∃ q : Fin (2 ^ (2 * r - r)),
      coreAliceKey (2 * r) r (by omega) (oddCoreLow r u) q = ℓ.1 ∧
      if starColor r hr ℓ.1 = 0 then
        starAliceLoc r u q = (ℓ.2.1, ℓ.2.2)
      else
        (starAliceLoc r u q).2 = ℓ.2.2 + (starAliceLoc r u q).1 * (1 + ℓ.2.1)
  V ℓ := Finset.univ.filter fun v =>
    ∃ w_lo : Fin (2 ^ r),
      coreBobKey (2 * r) r (by omega) (oddCoreLow r v) w_lo = ℓ.1 ∧
      if starColor r hr ℓ.1 = 0 then
        (starBobLoc r v w_lo ℓ.1.2.2.1).2 = ℓ.2.2 + ℓ.2.1 * (1 + (starBobLoc r v w_lo ℓ.1.2.2.1).1)
      else
        starBobLoc r v w_lo ℓ.1.2.2.1 = (ℓ.2.1, ℓ.2.2)
  isBiclique ℓ u hu v hv := by
    rw [Finset.mem_filter] at hu hv
    rcases hu.2 with ⟨q, hq, hlocU⟩
    rcases hv.2 with ⟨w_lo, hw, hlocV⟩
    have hmatch : coreAliceKey (2 * r) r (by omega) (oddCoreLow r u) q =
        coreBobKey (2 * r) r (by omega) (oddCoreLow r v) w_lo := hq.trans hw.symm
    have hq_eq : ℓ.1.2.2.1 = q := by rw [← hq]; rfl
    rw [hq_eq] at hlocV
    rw [K_coreRel_odd_split]
    refine ⟨((coreKey_eq_iff (by omega) _ _ _ _).mp hmatch).1, ?_⟩
    rw [← starBlowup_local_iff hr u v q w_lo hmatch]
    by_cases hcol : starColor r hr ℓ.1 = 0
    · simp only [hcol, ↓reduceIte] at hlocU hlocV
      rw [hlocU, hlocV]
      dsimp only
      rw [← add_assoc, zmod2_add_self, zero_add]
    · simp only [hcol, ↓reduceIte] at hlocU hlocV
      rw [hlocV, hlocU]
      dsimp only
      calc ℓ.2.2 + (starAliceLoc r u q).1 * (1 + ℓ.2.1) + ℓ.2.2
          = (ℓ.2.2 + ℓ.2.2) + (starAliceLoc r u q).1 * (1 + ℓ.2.1) := by abel
        _ = (starAliceLoc r u q).1 * (1 + ℓ.2.1) := by rw [zmod2_add_self, zero_add]
  covers u v huv := by
    have ⟨hlow, htop⟩ := (K_coreRel_odd_split r u v).mp huv
    let w_lo : Fin (2 ^ r) := ⟨(oddCoreLow r u).2.val % 2 ^ r, Nat.mod_lt _ (by positivity)⟩
    let c_m : ℕ := if (oddCoreLow r v).2.val % 2 ^ r < (oddCoreLow r u).2.val % 2 ^ r then 1 else 0
    let q : Fin (2 ^ (2 * r - r)) :=
      ⟨((oddCoreLow r v).2.val / 2 ^ r + 2 ^ (2 * r - r) - c_m) % 2 ^ (2 * r - r),
       Nat.mod_lt _ (by positivity)⟩
    have hmatch := (coreKey_eq_iff (by omega : r ≤ 2 * r) (oddCoreLow r u) (oddCoreLow r v) q w_lo).mpr
      ⟨hlow, rfl, rfl⟩
    have hloc := (starBlowup_local_iff hr u v q w_lo hmatch).mpr htop
    let ℓ0 := coreAliceKey (2 * r) r (by omega) (oddCoreLow r u) q
    have hq_ℓ0 : ℓ0.2.2.1 = q := rfl
    by_cases hcol : starColor r hr ℓ0 = 0
    · refine ⟨(ℓ0, (starAliceLoc r u q).1, (starAliceLoc r u q).2), ?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, q, rfl, by simp [hcol]⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, w_lo, hmatch.symm, ?_⟩
        simp only [hcol, ↓reduceIte, hq_ℓ0]
        calc (starBobLoc r v w_lo q).2
            = ((starAliceLoc r u q).2 + (starAliceLoc r u q).2) + (starBobLoc r v w_lo q).2 := by
              rw [zmod2_add_self, zero_add]
          _ = (starAliceLoc r u q).2 + ((starAliceLoc r u q).2 + (starBobLoc r v w_lo q).2) :=
              add_assoc _ _ _
          _ = (starAliceLoc r u q).2 + (starAliceLoc r u q).1 * (1 + (starBobLoc r v w_lo q).1) := by
              rw [hloc]
    · refine ⟨(ℓ0, (starBobLoc r v w_lo q).1, (starBobLoc r v w_lo q).2), ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, q, rfl, ?_⟩
        simp only [hcol, ↓reduceIte]
        calc (starAliceLoc r u q).2
            = (starAliceLoc r u q).2 + ((starBobLoc r v w_lo q).2 + (starBobLoc r v w_lo q).2) := by
              rw [zmod2_add_self, add_zero]
          _ = (starBobLoc r v w_lo q).2 + ((starAliceLoc r u q).2 + (starBobLoc r v w_lo q).2) := by abel
          _ = (starBobLoc r v w_lo q).2 + (starAliceLoc r u q).1 * (1 + (starBobLoc r v w_lo q).1) := by
              rw [hloc]
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, w_lo, hmatch.symm, by simp [hcol, hq_ℓ0]⟩

theorem starBlowupPartition_isPartition (r : ℕ) (hr : 1 ≤ r) :
    (starBlowupPartition r hr).IsPartition := by
  intro u v huv
  rcases (starBlowupPartition r hr).covers u v huv with ⟨l0, hU0, hV0⟩
  refine ⟨l0, ⟨hU0, hV0⟩, ?_⟩
  rintro ℓ ⟨hU, hV⟩
  simp only [starBlowupPartition, Finset.mem_filter, Finset.mem_univ, true_and] at hU0 hV0 hU hV
  rcases hU0 with ⟨q0, hq0, hlocU0⟩
  rcases hV0 with ⟨w0, hw0, hlocV0⟩
  rcases hU with ⟨q, hq, hlocU⟩
  rcases hV with ⟨w, hw, hlocV⟩
  have hm0 := (coreKey_eq_iff (by omega : r ≤ 2 * r) _ _ _ _).mp (hq0.trans hw0.symm)
  have hm := (coreKey_eq_iff (by omega : r ≤ 2 * r) _ _ _ _).mp (hq.trans hw.symm)
  have hqq : q = q0 := Fin.ext (hm.2.2.trans hm0.2.2.symm)
  have hww : w = w0 := Fin.ext (hm.2.1.trans hm0.2.1.symm)
  have hℓ0 : ℓ.1 = l0.1 := by rw [← hq, ← hq0, hqq]
  have hqℓ : ℓ.1.2.2.1 = q := by rw [← hq]; rfl
  have hqℓ0 : l0.1.2.2.1 = q0 := by rw [← hq0]; rfl
  rw [hqℓ] at hlocV; rw [hqℓ0] at hlocV0
  by_cases hcol : starColor r hr ℓ.1 = 0
  · have hcol0 : starColor r hr l0.1 = 0 := hℓ0 ▸ hcol
    simp only [hcol, ↓reduceIte] at hlocU
    simp only [hcol0, ↓reduceIte] at hlocU0
    have hp : (ℓ.2.1, ℓ.2.2) = (l0.2.1, l0.2.2) := by
      rw [← hlocU, ← hlocU0, hqq]
    exact Prod.ext hℓ0 hp
  · have hcol0 : starColor r hr l0.1 ≠ 0 := fun h => hcol (hℓ0.symm ▸ h)
    simp only [hcol, ↓reduceIte] at hlocV
    simp only [hcol0, ↓reduceIte] at hlocV0
    have hp : (ℓ.2.1, ℓ.2.2) = (l0.2.1, l0.2.2) := by
      rw [← hlocV, ← hlocV0, hqq, hww]
    exact Prod.ext hℓ0 hp

private lemma zmod2_ne_iff_eq_add_one (a b : ZMod 2) : a ≠ b ↔ a = b + 1 := by
  revert a b
  decide

theorem starBlowupPartition_rowLoad (r : ℕ) (hr : 1 ≤ r)
    (u : (Fin (2 * r + 1) → ZMod 2) × Fin (2 ^ (2 * r + 1))) :
    (starBlowupPartition r hr).rowLoad u = 3 * 2 ^ (r - 1) := by
  let : DecidableEq (IICStarCoreLabel (2 * r) r) := inferInstance
  unfold ExactBicliqueCover.rowLoad starBlowupPartition
  dsimp only
  -- Split by `q : Fin (2^(2*r - r))`: each `q` with color 0 yields 1 label, color 1 yields 2 labels.
  let f : Fin (2 ^ (2 * r - r)) → Finset (IICStarCoreLabel (2 * r) r × ZMod 2 × ZMod 2) := fun q =>
    let ℓ0 := coreAliceKey (2 * r) r (by omega) (oddCoreLow r u) q
    if starColor r hr ℓ0 = 0 then
      {(ℓ0, (starAliceLoc r u q).1, (starAliceLoc r u q).2)}
    else
      Finset.univ.image fun p1 : ZMod 2 =>
        (ℓ0, p1, (starAliceLoc r u q).2 + (starAliceLoc r u q).1 * (1 + p1))
  have hset : (Finset.univ.filter fun ℓ : IICStarCoreLabel (2 * r) r × ZMod 2 × ZMod 2 =>
      u ∈ Finset.univ.filter fun u' =>
        ∃ q : Fin (2 ^ (2 * r - r)),
          coreAliceKey (2 * r) r (by omega) (oddCoreLow r u') q = ℓ.1 ∧
          if starColor r hr ℓ.1 = 0 then starAliceLoc r u' q = (ℓ.2.1, ℓ.2.2)
          else (starAliceLoc r u' q).2 = ℓ.2.2 + (starAliceLoc r u' q).1 * (1 + ℓ.2.1)) =
      Finset.univ.biUnion f := by
    ext ⟨ℓ0, p1, p2⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, f]
    constructor
    · rintro ⟨q, rfl, hloc⟩
      refine ⟨q, ?_⟩
      by_cases hcol : starColor r hr (coreAliceKey (2 * r) r (by omega) (oddCoreLow r u) q) = 0
      · simp only [hcol, ↓reduceIte, Finset.mem_singleton] at hloc ⊢
        exact Prod.ext rfl (Prod.ext (congrArg Prod.fst hloc).symm (congrArg Prod.snd hloc).symm)
      · simp only [hcol, ↓reduceIte, Finset.mem_image, Finset.mem_univ, true_and] at hloc ⊢
        refine ⟨p1, Prod.ext rfl (Prod.ext rfl ?_)⟩
        rw [hloc, add_assoc, zmod2_add_self, add_zero]
    · rintro ⟨q, hmem⟩
      by_cases hcol : starColor r hr (coreAliceKey (2 * r) r (by omega) (oddCoreLow r u) q) = 0
      · simp only [hcol, ↓reduceIte, Finset.mem_singleton, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩
        exact ⟨q, rfl, by simp [hcol]⟩
      · simp only [hcol, ↓reduceIte, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq] at hmem
        rcases hmem with ⟨p1', rfl, rfl, rfl⟩
        refine ⟨q, rfl, ?_⟩
        simp only [hcol, ↓reduceIte]
        rw [add_assoc, zmod2_add_self, add_zero]
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin (2 ^ (2 * r - r))))) f := by
    intro q1 _ q2 _ hne
    change Disjoint (f q1) (f q2)
    rw [Finset.disjoint_left]
    intro ℓ h1 h2
    have hfst1 : ℓ.1.2.2.1 = q1 := by
      simp only [f] at h1
      split_ifs at h1
      · rw [Finset.mem_singleton] at h1; rw [h1]; rfl
      · rcases Finset.mem_image.mp h1 with ⟨_, _, rfl⟩; rfl
    have hfst2 : ℓ.1.2.2.1 = q2 := by
      simp only [f] at h2
      split_ifs at h2
      · rw [Finset.mem_singleton] at h2; rw [h2]; rfl
      · rcases Finset.mem_image.mp h2 with ⟨_, _, rfl⟩; rfl
    exact hne (hfst1.symm.trans hfst2)
  have hf_card : ∀ q : Fin (2 ^ (2 * r - r)),
      (f q).card = if starColor r hr (coreAliceKey (2 * r) r (by omega) (oddCoreLow r u) q) = 0
        then 1 else 2 := by
    intro q
    simp only [f]
    split_ifs
    · simp
    · rw [Finset.card_image_of_injective]
      · simp [ZMod.card]
      · intro a b h; exact congrArg (fun x => x.2.1) h
  rw [hset, Finset.card_biUnion hdisj]
  simp_rw [hf_card]
  have hsub_r : 2 * r - r = r := by omega
  let e : Fin (2 ^ r) ≃ Fin (2 ^ (2 * r - r)) := finCongr (by rw [hsub_r])
  rw [← Equiv.sum_comp e]
  set c0 : ZMod 2 := (oddCoreLow r u).1 ⟨r - 1, by omega⟩ +
    (((oddCoreLow r u).2.val % 2 ^ r % 2 : ℕ) : ZMod 2)
  have hcol_eq : ∀ q : Fin (2 ^ r),
      starColor r hr (coreAliceKey (2 * r) r (by omega) (oddCoreLow r u) (e q)) =
        ((q.val % 2 : ℕ) : ZMod 2) + c0 := by
    intro q
    simp only [starColor, coreAliceKey, e, c0, finCongr_apply, Fin.val_cast]
    rw [add_assoc]
  simp_rw [hcol_eq]
  have hiff0 : ∀ q : Fin (2 ^ r), ((q.val % 2 : ℕ) : ZMod 2) + c0 = 0 ↔
      ((q.val % 2 : ℕ) : ZMod 2) = c0 := by
    intro q
    constructor
    · intro h
      calc ((q.val % 2 : ℕ) : ZMod 2)
          = (((q.val % 2 : ℕ) : ZMod 2) + c0) + c0 := by rw [add_assoc, zmod2_add_self, add_zero]
        _ = c0 := by rw [h, zero_add]
    · intro h; rw [h, zmod2_add_self]
  simp_rw [hiff0]
  have hsum_split : ∑ q : Fin (2 ^ r), (if ((q.val % 2 : ℕ) : ZMod 2) = c0 then (1 : ℕ) else 2) =
      (Finset.univ.filter fun q : Fin (2 ^ r) => ((q.val % 2 : ℕ) : ZMod 2) = c0).card * 1 +
      (Finset.univ.filter fun q : Fin (2 ^ r) => ((q.val % 2 : ℕ) : ZMod 2) ≠ c0).card * 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun q : Fin (2 ^ r) => ((q.val % 2 : ℕ) : ZMod 2) = c0)]
    congr 1
    · calc ∑ q ∈ Finset.univ.filter (fun q : Fin (2 ^ r) => ((q.val % 2 : ℕ) : ZMod 2) = c0),
              (if ((q.val % 2 : ℕ) : ZMod 2) = c0 then (1 : ℕ) else 2)
          = ∑ _q ∈ Finset.univ.filter (fun q : Fin (2 ^ r) => ((q.val % 2 : ℕ) : ZMod 2) = c0), 1 :=
            Finset.sum_congr rfl (fun q hq => by simp only [(Finset.mem_filter.mp hq).2, ↓reduceIte])
        _ = (Finset.univ.filter (fun q : Fin (2 ^ r) => ((q.val % 2 : ℕ) : ZMod 2) = c0)).card * 1 := by
            simp
    · calc ∑ q ∈ Finset.univ.filter (fun q : Fin (2 ^ r) => ¬((q.val % 2 : ℕ) : ZMod 2) = c0),
              (if ((q.val % 2 : ℕ) : ZMod 2) = c0 then (1 : ℕ) else 2)
          = ∑ _q ∈ Finset.univ.filter (fun q : Fin (2 ^ r) => ¬((q.val % 2 : ℕ) : ZMod 2) = c0), 2 :=
            Finset.sum_congr rfl (fun q hq => by simp only [(Finset.mem_filter.mp hq).2, ↓reduceIte])
        _ = (Finset.univ.filter (fun q : Fin (2 ^ r) => ((q.val % 2 : ℕ) : ZMod 2) ≠ c0)).card * 2 := by
            simp
  have hne_eq : (Finset.univ.filter fun q : Fin (2 ^ r) => ((q.val % 2 : ℕ) : ZMod 2) ≠ c0) =
      (Finset.univ.filter fun q : Fin (2 ^ r) => ((q.val % 2 : ℕ) : ZMod 2) = c0 + 1) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact zmod2_ne_iff_eq_add_one _ _
  rw [hsum_split, hne_eq, card_fin_two_pow_parity hr c0, card_fin_two_pow_parity hr (c0 + 1)]
  ring

theorem starBlowupPartition_colLoad (r : ℕ) (hr : 1 ≤ r)
    (v : (Fin (2 * r + 1) → ZMod 2) × Fin (2 ^ (2 * r + 1))) :
    (starBlowupPartition r hr).colLoad v = 3 * 2 ^ (r - 1) := by
  let : DecidableEq (IICStarCoreLabel (2 * r) r) := inferInstance
  unfold ExactBicliqueCover.colLoad starBlowupPartition
  dsimp only
  let f : Fin (2 ^ r) → Finset (IICStarCoreLabel (2 * r) r × ZMod 2 × ZMod 2) := fun w_lo =>
    let ℓ0 := coreBobKey (2 * r) r (by omega) (oddCoreLow r v) w_lo
    let bloc := starBobLoc r v w_lo ℓ0.2.2.1
    if starColor r hr ℓ0 = 0 then
      Finset.univ.image fun p1 : ZMod 2 => (ℓ0, p1, bloc.2 + p1 * (1 + bloc.1))
    else
      {(ℓ0, bloc.1, bloc.2)}
  have hset : (Finset.univ.filter fun ℓ : IICStarCoreLabel (2 * r) r × ZMod 2 × ZMod 2 =>
      v ∈ Finset.univ.filter fun v' =>
        ∃ w_lo : Fin (2 ^ r),
          coreBobKey (2 * r) r (by omega) (oddCoreLow r v') w_lo = ℓ.1 ∧
          if starColor r hr ℓ.1 = 0 then
            (starBobLoc r v' w_lo ℓ.1.2.2.1).2 = ℓ.2.2 + ℓ.2.1 * (1 + (starBobLoc r v' w_lo ℓ.1.2.2.1).1)
          else
            starBobLoc r v' w_lo ℓ.1.2.2.1 = (ℓ.2.1, ℓ.2.2)) =
      Finset.univ.biUnion f := by
    ext ⟨ℓ0, p1, p2⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, f]
    constructor
    · rintro ⟨w_lo, rfl, hloc⟩
      refine ⟨w_lo, ?_⟩
      by_cases hcol : starColor r hr (coreBobKey (2 * r) r (by omega) (oddCoreLow r v) w_lo) = 0
      · simp only [hcol, ↓reduceIte, Finset.mem_image, Finset.mem_univ, true_and] at hloc ⊢
        refine ⟨p1, Prod.ext rfl (Prod.ext rfl ?_)⟩
        rw [hloc, add_assoc, zmod2_add_self, add_zero]
      · simp only [hcol, ↓reduceIte, Finset.mem_singleton] at hloc ⊢
        exact Prod.ext rfl (Prod.ext (congrArg Prod.fst hloc).symm (congrArg Prod.snd hloc).symm)
    · rintro ⟨w_lo, hmem⟩
      by_cases hcol : starColor r hr (coreBobKey (2 * r) r (by omega) (oddCoreLow r v) w_lo) = 0
      · simp only [hcol, ↓reduceIte, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq] at hmem
        rcases hmem with ⟨p1', rfl, rfl, rfl⟩
        refine ⟨w_lo, rfl, ?_⟩
        simp only [hcol, ↓reduceIte]
        rw [add_assoc, zmod2_add_self, add_zero]
      · simp only [hcol, ↓reduceIte, Finset.mem_singleton, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩
        exact ⟨w_lo, rfl, by simp [hcol]⟩
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin (2 ^ r)))) f := by
    intro w1 _ w2 _ hne
    change Disjoint (f w1) (f w2)
    rw [Finset.disjoint_left]
    intro ℓ h1 h2
    have hfst1 : ℓ.1.1 = w1 := by
      simp only [f] at h1
      split_ifs at h1
      · rcases Finset.mem_image.mp h1 with ⟨_, _, rfl⟩; rfl
      · rw [Finset.mem_singleton] at h1; rw [h1]; rfl
    have hfst2 : ℓ.1.1 = w2 := by
      simp only [f] at h2
      split_ifs at h2
      · rcases Finset.mem_image.mp h2 with ⟨_, _, rfl⟩; rfl
      · rw [Finset.mem_singleton] at h2; rw [h2]; rfl
    exact hne (hfst1.symm.trans hfst2)
  have hf_card : ∀ w_lo : Fin (2 ^ r),
      (f w_lo).card = if starColor r hr (coreBobKey (2 * r) r (by omega) (oddCoreLow r v) w_lo) = 0
        then 2 else 1 := by
    intro w_lo
    simp only [f]
    split_ifs
    · rw [Finset.card_image_of_injective]
      · simp [ZMod.card]
      · intro a b h; exact congrArg (fun x => x.2.1) h
    · simp
  rw [hset, Finset.card_biUnion hdisj]
  simp_rw [hf_card]
  -- Key Step 1 cancellation: `q_0 ⊕ x_r = (z_{hi,0} ⊕ c_r) ⊕ (y_r ⊕ c_r) = z_{hi,0} ⊕ y_r`!
  set c0 : ZMod 2 := (((oddCoreLow r v).2.val / 2 ^ r % 2 : ℕ) : ZMod 2) +
    (oddCoreLow r v).1 ⟨r - 1, by omega⟩
  have h2dvd : 2 ∣ 2 ^ (2 * r - r) := dvd_pow_self 2 (by omega)
  have hpow_ge1 : 1 ≤ 2 ^ (2 * r - r) := Nat.one_le_two_pow
  have hcol_eq : ∀ w_lo : Fin (2 ^ r),
      starColor r hr (coreBobKey (2 * r) r (by omega) (oddCoreLow r v) w_lo) =
        ((w_lo.val % 2 : ℕ) : ZMod 2) + c0 := by
    intro w_lo
    simp only [starColor, coreBobKey, borrowVec, borrowBit,
      show r - 1 + 1 = r by omega, Nat.mod_eq_of_lt w_lo.isLt,
      Nat.mod_eq_of_lt (Nat.mod_lt (oddCoreLow r v).2.val (by positivity : 0 < 2 ^ r))]
    have hq_par : ((((oddCoreLow r v).2.val / 2 ^ r + 2 ^ (2 * r - r) -
        if (oddCoreLow r v).2.val % 2 ^ r < w_lo.val then 1 else 0) % 2 ^ (2 * r - r) % 2 : ℕ) : ZMod 2) =
        (((oddCoreLow r v).2.val / 2 ^ r % 2 : ℕ) : ZMod 2) +
        (if (oddCoreLow r v).2.val % 2 ^ r < w_lo.val then (1 : ZMod 2) else 0) := by
      rw [Nat.mod_mod_of_dvd _ h2dvd]
      have h2m : 2 ^ (2 * r - r) % 2 = 0 := Nat.mod_eq_zero_of_dvd h2dvd
      have hpar_aux : ∀ (n P : ℕ), 1 ≤ P → P % 2 = 0 →
          (n + P - 1) % 2 = (n % 2 + 1) % 2 ∧ (n + P) % 2 = n % 2 := by
        intro n P hP1 hP2; omega
      by_cases hlt : (oddCoreLow r v).2.val % 2 ^ r < w_lo.val
      · simp only [hlt, ↓reduceIte]
        rw [(hpar_aux _ _ hpow_ge1 h2m).1]
        have hm2 : (oddCoreLow r v).2.val / 2 ^ r % 2 < 2 := Nat.mod_lt _ (by omega)
        interval_cases ((oddCoreLow r v).2.val / 2 ^ r % 2) <;> decide
      · simp only [hlt, ↓reduceIte, Nat.sub_zero, add_zero]
        rw [(hpar_aux _ _ hpow_ge1 h2m).2]
    rw [hq_par]
    set br : ZMod 2 := if (oddCoreLow r v).2.val % 2 ^ r < w_lo.val then 1 else 0
    calc (((oddCoreLow r v).2.val / 2 ^ r % 2 : ℕ) : ZMod 2) + br +
          ((oddCoreLow r v).1 ⟨r - 1, by omega⟩ + br) + ((w_lo.val % 2 : ℕ) : ZMod 2)
        = (br + br) + (((w_lo.val % 2 : ℕ) : ZMod 2) + c0) := by simp only [c0]; abel
      _ = ((w_lo.val % 2 : ℕ) : ZMod 2) + c0 := by rw [zmod2_add_self, zero_add]
  simp_rw [hcol_eq]
  have hiff0 : ∀ w_lo : Fin (2 ^ r), ((w_lo.val % 2 : ℕ) : ZMod 2) + c0 = 0 ↔
      ((w_lo.val % 2 : ℕ) : ZMod 2) = c0 := by
    intro w_lo
    constructor
    · intro h
      calc ((w_lo.val % 2 : ℕ) : ZMod 2)
          = (((w_lo.val % 2 : ℕ) : ZMod 2) + c0) + c0 := by rw [add_assoc, zmod2_add_self, add_zero]
        _ = c0 := by rw [h, zero_add]
    · intro h; rw [h, zmod2_add_self]
  simp_rw [hiff0]
  have hsum_split : ∑ w_lo : Fin (2 ^ r), (if ((w_lo.val % 2 : ℕ) : ZMod 2) = c0 then (2 : ℕ) else 1) =
      (Finset.univ.filter fun w_lo : Fin (2 ^ r) => ((w_lo.val % 2 : ℕ) : ZMod 2) = c0).card * 2 +
      (Finset.univ.filter fun w_lo : Fin (2 ^ r) => ((w_lo.val % 2 : ℕ) : ZMod 2) ≠ c0).card * 1 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun w_lo : Fin (2 ^ r) => ((w_lo.val % 2 : ℕ) : ZMod 2) = c0)]
    congr 1
    · calc ∑ w_lo ∈ Finset.univ.filter (fun w_lo : Fin (2 ^ r) => ((w_lo.val % 2 : ℕ) : ZMod 2) = c0),
              (if ((w_lo.val % 2 : ℕ) : ZMod 2) = c0 then (2 : ℕ) else 1)
          = ∑ _w_lo ∈ Finset.univ.filter (fun w_lo : Fin (2 ^ r) => ((w_lo.val % 2 : ℕ) : ZMod 2) = c0), 2 :=
            Finset.sum_congr rfl (fun w hw => by simp only [(Finset.mem_filter.mp hw).2, ↓reduceIte])
        _ = (Finset.univ.filter (fun w_lo : Fin (2 ^ r) => ((w_lo.val % 2 : ℕ) : ZMod 2) = c0)).card * 2 := by
            simp
    · calc ∑ w_lo ∈ Finset.univ.filter (fun w_lo : Fin (2 ^ r) => ¬((w_lo.val % 2 : ℕ) : ZMod 2) = c0),
              (if ((w_lo.val % 2 : ℕ) : ZMod 2) = c0 then (2 : ℕ) else 1)
          = ∑ _w_lo ∈ Finset.univ.filter (fun w_lo : Fin (2 ^ r) => ¬((w_lo.val % 2 : ℕ) : ZMod 2) = c0), 1 :=
            Finset.sum_congr rfl (fun w hw => by simp only [(Finset.mem_filter.mp hw).2, ↓reduceIte])
        _ = (Finset.univ.filter (fun w_lo : Fin (2 ^ r) => ((w_lo.val % 2 : ℕ) : ZMod 2) ≠ c0)).card * 1 := by
            simp
  have hne_eq : (Finset.univ.filter fun w_lo : Fin (2 ^ r) => ((w_lo.val % 2 : ℕ) : ZMod 2) ≠ c0) =
      (Finset.univ.filter fun w_lo : Fin (2 ^ r) => ((w_lo.val % 2 : ℕ) : ZMod 2) = c0 + 1) := by
    ext w_lo
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact zmod2_ne_iff_eq_add_one _ _
  rw [hsum_split, hne_eq, card_fin_two_pow_parity hr c0, card_fin_two_pow_parity hr (c0 + 1)]
  ring

theorem starBlowupPartition_hasMaxLoadLe (r : ℕ) (hr : 1 ≤ r) :
    (starBlowupPartition r hr).HasMaxLoadLe (3 * 2 ^ (r - 1)) :=
  ⟨fun u => (starBlowupPartition_rowLoad r hr u).le,
   fun v => (starBlowupPartition_colLoad r hr v).le⟩

/-- Theorem 3.2 (unified upper bound for ALL `s ≥ 0` on `K_coreRel s`, Equation (3.1)):
there exists an exact biclique PARTITION of `K_coreRel s` attaining the exact local bound
`⌈(2^⌊s/2⌋ + 2^⌈s/2⌉) / 2⌉`, proving `lbc(C_t) = lbp(C_t) = ⌈(2^⌊s/2⌋ + 2^⌈s/2⌉) / 2⌉`. -/
theorem exists_optimal_local_partition_K (s : ℕ) :
    ∃ C : ExactBicliqueCover (K_coreRel s),
      C.IsPartition ∧ C.HasMaxLoadLe ((2 ^ (s / 2) + 2 ^ ((s + 1) / 2) + 1) / 2) := by
  by_cases heven : s % 2 = 0
  · let r := s / 2
    have hs_eq : s = 2 * r := by omega
    refine ⟨mechanismIICStarCore s r (by omega), mechanismIICStarCore_isPartition s r (by omega), ?_⟩
    have hval : (2 ^ (s / 2) + 2 ^ ((s + 1) / 2) + 1) / 2 = 2 ^ r := by
      have h1 : (s + 1) / 2 = r := by omega
      have h2 : s / 2 = r := rfl
      rw [h1, h2]; omega
    rw [hval]
    exact ⟨fun u => by rw [mechanismIICStarCore_rowLoad, show s - r = r by omega],
           fun v => by rw [mechanismIICStarCore_colLoad]⟩
  · cases s with
    | zero => omega
    | succ s' =>
      by_cases hs1 : s' = 0
      · subst hs1
        refine ⟨mechanismIICStarCore 1 0 (by omega), mechanismIICStarCore_isPartition 1 0 (by omega), ?_⟩
        refine ⟨fun u => ?_, fun v => ?_⟩
        · rw [mechanismIICStarCore_rowLoad]; decide
        · rw [mechanismIICStarCore_colLoad]; decide
      · let r := (s' + 1) / 2
        have hr : 1 ≤ r := by omega
        have hs_eq : 2 * r + 1 = s' + 1 := by omega
        have hval : (2 ^ ((2 * r + 1) / 2) + 2 ^ ((2 * r + 1 + 1) / 2) + 1) / 2 = 3 * 2 ^ (r - 1) := by
          have h1 : (2 * r + 1) / 2 = r := by omega
          have h2 : (2 * r + 1 + 1) / 2 = r + 1 := by omega
          have h3 : 2 ^ r = 2 * 2 ^ (r - 1) := by rw [← pow_succ', show r - 1 + 1 = r by omega]
          have h4 : 2 ^ (r + 1) = 4 * 2 ^ (r - 1) := by
            calc 2 ^ (r + 1) = 2 * 2 ^ r := by rw [pow_succ']
              _ = 4 * 2 ^ (r - 1) := by rw [h3]; ring
          rw [h1, h2, h3, h4]
          omega
        rw [← hs_eq, hval]
        exact ⟨starBlowupPartition r hr, starBlowupPartition_isPartition r hr,
               starBlowupPartition_hasMaxLoadLe r hr⟩

/-- Theorem 3.2 (unified upper bound for ALL `t ≥ 1` on `M_rel t`, Equation (3.1)):
lifting the optimal `K_coreRel (t - 1)` partition via `I_2 ⊗ C_t ⊗ J_2` yields an exact
biclique PARTITION of `M_rel t` attaining `lbc(M_t) = lbp(M_t) = ⌈(2^⌊(t-1)/2⌋ + 2^⌈(t-1)/2⌉) / 2⌉`. -/
theorem exists_optimal_local_partition_M {t : ℕ} (ht : 1 ≤ t) :
    ∃ C : ExactBicliqueCover (M_rel t),
      C.IsPartition ∧ C.HasMaxLoadLe ((2 ^ ((t - 1) / 2) + 2 ^ (t / 2) + 1) / 2) := by
  cases t with
  | zero => omega
  | succ s =>
    rcases exists_optimal_local_partition_K s with ⟨Ck, hpart, hload⟩
    refine ⟨liftCoverKToM s Ck, liftCoverKToM_isPartition s Ck hpart, ?_⟩
    simpa [Nat.add_sub_cancel] using liftCoverKToM_hasMaxLoadLe s _ Ck hload

/-! ### Proposition 3.3 & Appendix A, Proposition A.1: `s = 3` Equivariant Obstruction

We give a 100% kernel-verified (`decide`) formalization of Appendix A,
Proposition A.1 (all `48` maximal cocycle-valid `(2,4)`/`(4,2)` pairs on `Fin 8 × Fin 8`,
all `50` disjoint tilings via the canonical least-uncovered-cell exact-cover search, exact
distribution `[5, 0, 12, 0, 16, 0, 12, 0, 5]`, and universal max vertex load `= 4`), together
with Proposition 3.3 proving that no `𝔽₂³`-equivariant exact biclique cover of `K_coreRel 3`
achieves max vertex load `≤ 3`.
-/

/-- 8-bit subset of `Fin 8` represented directly by 8 booleans for fast kernel reduction. -/
structure Mask8 where
  b0 : Bool
  b1 : Bool
  b2 : Bool
  b3 : Bool
  b4 : Bool
  b5 : Bool
  b6 : Bool
  b7 : Bool
  deriving DecidableEq

namespace Mask8

def empty : Mask8 := ⟨false, false, false, false, false, false, false, false⟩

def get (m : Mask8) : Fin 8 → Bool
  | ⟨0, _⟩ => m.b0
  | ⟨1, _⟩ => m.b1
  | ⟨2, _⟩ => m.b2
  | ⟨3, _⟩ => m.b3
  | ⟨4, _⟩ => m.b4
  | ⟨5, _⟩ => m.b5
  | ⟨6, _⟩ => m.b6
  | ⟨7, _⟩ => m.b7

def ofFn (f : Fin 8 → Bool) : Mask8 :=
  ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7⟩

def ofFinset (S : Finset (Fin 8)) : Mask8 :=
  ofFn fun i => decide (i ∈ S)

def toFinset (m : Mask8) : Finset (Fin 8) :=
  Finset.univ.filter fun i => m.get i = true

def card (m : Mask8) : ℕ :=
  (if m.b0 then 1 else 0) + (if m.b1 then 1 else 0) +
  (if m.b2 then 1 else 0) + (if m.b3 then 1 else 0) +
  (if m.b4 then 1 else 0) + (if m.b5 then 1 else 0) +
  (if m.b6 then 1 else 0) + (if m.b7 then 1 else 0)

def disjoint (a b : Mask8) : Bool :=
  !(a.b0 && b.b0) && !(a.b1 && b.b1) && !(a.b2 && b.b2) && !(a.b3 && b.b3) &&
  !(a.b4 && b.b4) && !(a.b5 && b.b5) && !(a.b6 && b.b6) && !(a.b7 && b.b7)

def or (a b : Mask8) : Mask8 :=
  ⟨a.b0 || b.b0, a.b1 || b.b1, a.b2 || b.b2, a.b3 || b.b3,
   a.b4 || b.b4, a.b5 || b.b5, a.b6 || b.b6, a.b7 || b.b7⟩

def firstFalse (m : Mask8) : Option (Fin 8) :=
  if !m.b0 then some 0 else if !m.b1 then some 1 else if !m.b2 then some 2 else
  if !m.b3 then some 3 else if !m.b4 then some 4 else if !m.b5 then some 5 else
  if !m.b6 then some 6 else if !m.b7 then some 7 else none

def firstTrue (m : Mask8) : Option (Fin 8) :=
  if m.b0 then some 0 else if m.b1 then some 1 else if m.b2 then some 2 else
  if m.b3 then some 3 else if m.b4 then some 4 else if m.b5 then some 5 else
  if m.b6 then some 6 else if m.b7 then some 7 else none

lemma ext_get {a b : Mask8} (h : ∀ i : Fin 8, a.get i = b.get i) : a = b := by
  cases a; cases b
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  have h4 := h 4; have h5 := h 5; have h6 := h 6; have h7 := h 7
  simp only [get] at h0 h1 h2 h3 h4 h5 h6 h7
  subst h0 h1 h2 h3 h4 h5 h6 h7
  rfl

lemma get_ofFn (f : Fin 8 → Bool) (i : Fin 8) : (ofFn f).get i = f i := by
  fin_cases i <;> rfl

lemma get_empty (i : Fin 8) : empty.get i = false := by
  fin_cases i <;> rfl

lemma get_ofFinset (S : Finset (Fin 8)) (i : Fin 8) : (ofFinset S).get i = decide (i ∈ S) :=
  get_ofFn _ i

lemma mem_toFinset (m : Mask8) (i : Fin 8) : i ∈ m.toFinset ↔ m.get i = true := by
  simp [toFinset]

lemma toFinset_ofFinset (S : Finset (Fin 8)) : (ofFinset S).toFinset = S := by
  ext i; simp [mem_toFinset, get_ofFinset]

lemma ofFinset_toFinset (m : Mask8) : ofFinset m.toFinset = m := by
  apply ext_get; intro i; simp [get_ofFinset, mem_toFinset]

lemma toFinset_injective : Function.Injective toFinset := by
  intro a b h
  rw [← ofFinset_toFinset a, ← ofFinset_toFinset b, h]

lemma card_eq_toFinset_card (m : Mask8) : m.card = m.toFinset.card := by
  rw [toFinset, Finset.card_filter, Fin.sum_univ_eight]
  rfl

lemma get_or (a b : Mask8) (i : Fin 8) : (a.or b).get i = (a.get i || b.get i) := by
  fin_cases i <;> rfl

lemma disjoint_iff (a b : Mask8) :
    a.disjoint b = true ↔ ∀ i : Fin 8, ¬ (a.get i = true ∧ b.get i = true) := by
  constructor
  · intro h i
    simp only [disjoint, Bool.and_eq_true, Bool.not_eq_true'] at h
    fin_cases i <;> simp only [get] <;> rintro ⟨ha, hb⟩ <;> simp_all
  · intro h
    simp only [disjoint, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_imp]
    refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · intro ha; cases hb : b.b0 with | false => rfl | true => exact absurd ⟨ha, hb⟩ (h 0)
    · intro ha; cases hb : b.b1 with | false => rfl | true => exact absurd ⟨ha, hb⟩ (h 1)
    · intro ha; cases hb : b.b2 with | false => rfl | true => exact absurd ⟨ha, hb⟩ (h 2)
    · intro ha; cases hb : b.b3 with | false => rfl | true => exact absurd ⟨ha, hb⟩ (h 3)
    · intro ha; cases hb : b.b4 with | false => rfl | true => exact absurd ⟨ha, hb⟩ (h 4)
    · intro ha; cases hb : b.b5 with | false => rfl | true => exact absurd ⟨ha, hb⟩ (h 5)
    · intro ha; cases hb : b.b6 with | false => rfl | true => exact absurd ⟨ha, hb⟩ (h 6)
    · intro ha; cases hb : b.b7 with | false => rfl | true => exact absurd ⟨ha, hb⟩ (h 7)

lemma firstFalse_none_iff (m : Mask8) : m.firstFalse = none ↔ ∀ i : Fin 8, m.get i = true := by
  rcases m with ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩
  unfold firstFalse
  constructor
  · intro h i
    split_ifs at h with h0 h1 h2 h3 h4 h5 h6 h7
    fin_cases i <;> simp_all [get]
  · intro hall
    have hb0 : b0 = true := hall 0
    have hb1 : b1 = true := hall 1
    have hb2 : b2 = true := hall 2
    have hb3 : b3 = true := hall 3
    have hb4 : b4 = true := hall 4
    have hb5 : b5 = true := hall 5
    have hb6 : b6 = true := hall 6
    have hb7 : b7 = true := hall 7
    simp [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7]

lemma firstFalse_some (m : Mask8) (j : Fin 8) (h : m.firstFalse = some j) :
    m.get j = false ∧ ∀ i : Fin 8, i < j → m.get i = true := by
  unfold firstFalse at h
  split_ifs at h with h0 h1 h2 h3 h4 h5 h6 h7
  · cases h; exact ⟨by simp_all [get], fun i hi => by omega⟩
  · cases h; exact ⟨by simp_all [get], fun i hi => by fin_cases i <;> simp_all [get]⟩
  · cases h; exact ⟨by simp_all [get], fun i hi => by fin_cases i <;> simp_all [get]⟩
  · cases h; exact ⟨by simp_all [get], fun i hi => by fin_cases i <;> simp_all [get]⟩
  · cases h; exact ⟨by simp_all [get], fun i hi => by fin_cases i <;> simp_all [get]⟩
  · cases h; exact ⟨by simp_all [get], fun i hi => by fin_cases i <;> simp_all [get]⟩
  · cases h; exact ⟨by simp_all [get], fun i hi => by fin_cases i <;> simp_all [get]⟩
  · cases h; exact ⟨by simp_all [get], fun i hi => by fin_cases i <;> simp_all [get]⟩

lemma firstTrue_some_iff (m : Mask8) (j : Fin 8) :
    m.firstTrue = some j ↔ m.get j = true ∧ ∀ i : Fin 8, i < j → m.get i = false := by
  unfold firstTrue
  split_ifs with h0 h1 h2 h3 h4 h5 h6 h7
  · constructor
    · intro h; cases h; exact ⟨h0, fun i hi => by omega⟩
    · rintro ⟨hj, hlt⟩
      by_cases h0j : (0 : Fin 8) < j
      · have := hlt 0 h0j; simp [get, h0] at this
      · have : j = 0 := by ext; omega
        rw [this]
  · constructor
    · intro h; cases h; exact ⟨h1, fun i hi => by fin_cases i <;> simp_all [get]⟩
    · rintro ⟨hj, hlt⟩
      by_cases h1j : (1 : Fin 8) < j
      · have := hlt 1 h1j; simp [get, h1] at this
      · have h0ne : j ≠ 0 := by rintro rfl; simp [get, h0] at hj
        have : j = 1 := by ext; omega
        rw [this]
  · constructor
    · intro h; cases h; exact ⟨h2, fun i hi => by fin_cases i <;> simp_all [get]⟩
    · rintro ⟨hj, hlt⟩
      by_cases h2j : (2 : Fin 8) < j
      · have := hlt 2 h2j; simp [get, h2] at this
      · have : j = 2 := by fin_cases j <;> simp_all [get]
        rw [this]
  · constructor
    · intro h; cases h; exact ⟨h3, fun i hi => by fin_cases i <;> simp_all [get]⟩
    · rintro ⟨hj, hlt⟩
      by_cases h3j : (3 : Fin 8) < j
      · have := hlt 3 h3j; simp [get, h3] at this
      · have : j = 3 := by fin_cases j <;> simp_all [get]
        rw [this]
  · constructor
    · intro h; cases h; exact ⟨h4, fun i hi => by fin_cases i <;> simp_all [get]⟩
    · rintro ⟨hj, hlt⟩
      by_cases h4j : (4 : Fin 8) < j
      · have := hlt 4 h4j; simp [get, h4] at this
      · have : j = 4 := by fin_cases j <;> simp_all [get]
        rw [this]
  · constructor
    · intro h; cases h; exact ⟨h5, fun i hi => by fin_cases i <;> simp_all [get]⟩
    · rintro ⟨hj, hlt⟩
      by_cases h5j : (5 : Fin 8) < j
      · have := hlt 5 h5j; simp [get, h5] at this
      · have : j = 5 := by fin_cases j <;> simp_all [get]
        rw [this]
  · constructor
    · intro h; cases h; exact ⟨h6, fun i hi => by fin_cases i <;> simp_all [get]⟩
    · rintro ⟨hj, hlt⟩
      by_cases h6j : (6 : Fin 8) < j
      · have := hlt 6 h6j; simp [get, h6] at this
      · have : j = 6 := by fin_cases j <;> simp_all [get]
        rw [this]
  · constructor
    · intro h; cases h; exact ⟨h7, fun i hi => by fin_cases i <;> simp_all [get]⟩
    · rintro ⟨hj, hlt⟩
      have : j = 7 := by fin_cases j <;> simp_all [get]
      rw [this]
  · constructor
    · intro h; cases h
    · rintro ⟨hj, _⟩; fin_cases j <;> simp_all [get]

instance : Fintype Mask8 :=
  Fintype.ofEquiv (Fin 8 → Bool)
    { toFun := ofFn
      invFun := get
      left_inv := fun f => funext (get_ofFn f)
      right_inv := fun m => ext_get (get_ofFn m.get) }

end Mask8

/-- 8 × 8 boolean grid represented as 8 rows of `Mask8` for fast kernel reduction. -/
structure Grid8 where
  r0 : Mask8
  r1 : Mask8
  r2 : Mask8
  r3 : Mask8
  r4 : Mask8
  r5 : Mask8
  r6 : Mask8
  r7 : Mask8
  deriving DecidableEq

namespace Grid8

def empty : Grid8 :=
  ⟨Mask8.empty, Mask8.empty, Mask8.empty, Mask8.empty,
   Mask8.empty, Mask8.empty, Mask8.empty, Mask8.empty⟩

def row (g : Grid8) : Fin 8 → Mask8
  | ⟨0, _⟩ => g.r0
  | ⟨1, _⟩ => g.r1
  | ⟨2, _⟩ => g.r2
  | ⟨3, _⟩ => g.r3
  | ⟨4, _⟩ => g.r4
  | ⟨5, _⟩ => g.r5
  | ⟨6, _⟩ => g.r6
  | ⟨7, _⟩ => g.r7

def get (g : Grid8) (w z : Fin 8) : Bool := (g.row w).get z

def ofRect (wm zm : Mask8) : Grid8 :=
  ⟨if wm.b0 then zm else Mask8.empty,
   if wm.b1 then zm else Mask8.empty,
   if wm.b2 then zm else Mask8.empty,
   if wm.b3 then zm else Mask8.empty,
   if wm.b4 then zm else Mask8.empty,
   if wm.b5 then zm else Mask8.empty,
   if wm.b6 then zm else Mask8.empty,
   if wm.b7 then zm else Mask8.empty⟩

def disjoint (a b : Grid8) : Bool :=
  a.r0.disjoint b.r0 && a.r1.disjoint b.r1 && a.r2.disjoint b.r2 && a.r3.disjoint b.r3 &&
  a.r4.disjoint b.r4 && a.r5.disjoint b.r5 && a.r6.disjoint b.r6 && a.r7.disjoint b.r7

def or (a b : Grid8) : Grid8 :=
  ⟨a.r0.or b.r0, a.r1.or b.r1, a.r2.or b.r2, a.r3.or b.r3,
   a.r4.or b.r4, a.r5.or b.r5, a.r6.or b.r6, a.r7.or b.r7⟩

def firstUncovered (g : Grid8) : Option (Fin 8 × Fin 8) :=
  match g.r0.firstFalse with
  | some z => some (0, z)
  | none => match g.r1.firstFalse with
    | some z => some (1, z)
    | none => match g.r2.firstFalse with
      | some z => some (2, z)
      | none => match g.r3.firstFalse with
        | some z => some (3, z)
        | none => match g.r4.firstFalse with
          | some z => some (4, z)
          | none => match g.r5.firstFalse with
            | some z => some (5, z)
            | none => match g.r6.firstFalse with
              | some z => some (6, z)
              | none => match g.r7.firstFalse with
                | some z => some (7, z)
                | none => none

lemma get_empty (w z : Fin 8) : empty.get w z = false := by
  fin_cases w <;> exact Mask8.get_empty z

lemma get_ofRect (wm zm : Mask8) (w z : Fin 8) :
    (ofRect wm zm).get w z = (wm.get w && zm.get z) := by
  rcases wm with ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩
  fin_cases w <;> simp only [ofRect, get, row]
  · cases b0 with | false => exact Mask8.get_empty z | true => rfl
  · cases b1 with | false => exact Mask8.get_empty z | true => rfl
  · cases b2 with | false => exact Mask8.get_empty z | true => rfl
  · cases b3 with | false => exact Mask8.get_empty z | true => rfl
  · cases b4 with | false => exact Mask8.get_empty z | true => rfl
  · cases b5 with | false => exact Mask8.get_empty z | true => rfl
  · cases b6 with | false => exact Mask8.get_empty z | true => rfl
  · cases b7 with | false => exact Mask8.get_empty z | true => rfl

lemma get_or (a b : Grid8) (w z : Fin 8) :
    (a.or b).get w z = (a.get w z || b.get w z) := by
  fin_cases w <;> exact Mask8.get_or _ _ z

lemma disjoint_iff (a b : Grid8) :
    a.disjoint b = true ↔ ∀ w z : Fin 8, ¬ (a.get w z = true ∧ b.get w z = true) := by
  simp only [disjoint, Bool.and_eq_true, Mask8.disjoint_iff, get]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ w z
    fin_cases w <;> simp only [row]
    · exact h0 z
    · exact h1 z
    · exact h2 z
    · exact h3 z
    · exact h4 z
    · exact h5 z
    · exact h6 z
    · exact h7 z
  · intro h
    exact ⟨⟨⟨⟨⟨⟨⟨h 0, h 1⟩, h 2⟩, h 3⟩, h 4⟩, h 5⟩, h 6⟩, h 7⟩

lemma firstUncovered_none_iff (g : Grid8) :
    g.firstUncovered = none ↔ ∀ w z : Fin 8, g.get w z = true := by
  unfold firstUncovered
  constructor
  · intro h w z
    cases h0 : g.r0.firstFalse with
    | some _ => rw [h0] at h; cases h
    | none =>
      rw [h0] at h
      cases h1 : g.r1.firstFalse with
      | some _ => rw [h1] at h; cases h
      | none =>
        rw [h1] at h
        cases h2 : g.r2.firstFalse with
        | some _ => rw [h2] at h; cases h
        | none =>
          rw [h2] at h
          cases h3 : g.r3.firstFalse with
          | some _ => rw [h3] at h; cases h
          | none =>
            rw [h3] at h
            cases h4 : g.r4.firstFalse with
            | some _ => rw [h4] at h; cases h
            | none =>
              rw [h4] at h
              cases h5 : g.r5.firstFalse with
              | some _ => rw [h5] at h; cases h
              | none =>
                rw [h5] at h
                cases h6 : g.r6.firstFalse with
                | some _ => rw [h6] at h; cases h
                | none =>
                  rw [h6] at h
                  cases h7 : g.r7.firstFalse with
                  | some _ => rw [h7] at h; cases h
                  | none =>
                    fin_cases w <;> simp only [get, row]
                    · exact (Mask8.firstFalse_none_iff _).mp h0 z
                    · exact (Mask8.firstFalse_none_iff _).mp h1 z
                    · exact (Mask8.firstFalse_none_iff _).mp h2 z
                    · exact (Mask8.firstFalse_none_iff _).mp h3 z
                    · exact (Mask8.firstFalse_none_iff _).mp h4 z
                    · exact (Mask8.firstFalse_none_iff _).mp h5 z
                    · exact (Mask8.firstFalse_none_iff _).mp h6 z
                    · exact (Mask8.firstFalse_none_iff _).mp h7 z
  · intro hall
    have h0 : g.r0.firstFalse = none := (Mask8.firstFalse_none_iff _).mpr (hall 0)
    have h1 : g.r1.firstFalse = none := (Mask8.firstFalse_none_iff _).mpr (hall 1)
    have h2 : g.r2.firstFalse = none := (Mask8.firstFalse_none_iff _).mpr (hall 2)
    have h3 : g.r3.firstFalse = none := (Mask8.firstFalse_none_iff _).mpr (hall 3)
    have h4 : g.r4.firstFalse = none := (Mask8.firstFalse_none_iff _).mpr (hall 4)
    have h5 : g.r5.firstFalse = none := (Mask8.firstFalse_none_iff _).mpr (hall 5)
    have h6 : g.r6.firstFalse = none := (Mask8.firstFalse_none_iff _).mpr (hall 6)
    have h7 : g.r7.firstFalse = none := (Mask8.firstFalse_none_iff _).mpr (hall 7)
    simp [h0, h1, h2, h3, h4, h5, h6, h7]

lemma firstUncovered_some (g : Grid8) (w z : Fin 8) (h : g.firstUncovered = some (w, z)) :
    g.get w z = false ∧
    ∀ w' z' : Fin 8, (w' < w ∨ (w' = w ∧ z' < z)) → g.get w' z' = true := by
  unfold firstUncovered at h
  cases h0 : g.r0.firstFalse with
  | some z0 =>
    rw [h0] at h; cases h
    have ⟨hf, hlt⟩ := Mask8.firstFalse_some _ _ h0
    exact ⟨hf, fun w' z' hord => by
      rcases hord with hltw | ⟨rfl, hltz⟩
      · omega
      · exact hlt z' hltz⟩
  | none =>
    rw [h0] at h
    have hr0 := (Mask8.firstFalse_none_iff _).mp h0
    cases h1 : g.r1.firstFalse with
    | some z1 =>
      rw [h1] at h; cases h
      have ⟨hf, hlt⟩ := Mask8.firstFalse_some _ _ h1
      exact ⟨hf, fun w' z' hord => by
        rcases hord with hltw | ⟨rfl, hltz⟩
        · have : w' = 0 := by ext; omega
          rw [this]; exact hr0 z'
        · exact hlt z' hltz⟩
    | none =>
      rw [h1] at h
      have hr1 := (Mask8.firstFalse_none_iff _).mp h1
      cases h2 : g.r2.firstFalse with
      | some z2 =>
        rw [h2] at h; cases h
        have ⟨hf, hlt⟩ := Mask8.firstFalse_some _ _ h2
        exact ⟨hf, fun w' z' hord => by
          rcases hord with hltw | ⟨rfl, hltz⟩
          · fin_cases w' <;> simp_all [get, row]
          · exact hlt z' hltz⟩
      | none =>
        rw [h2] at h
        have hr2 := (Mask8.firstFalse_none_iff _).mp h2
        cases h3 : g.r3.firstFalse with
        | some z3 =>
          rw [h3] at h; cases h
          have ⟨hf, hlt⟩ := Mask8.firstFalse_some _ _ h3
          exact ⟨hf, fun w' z' hord => by
            rcases hord with hltw | ⟨rfl, hltz⟩
            · fin_cases w' <;> simp_all [get, row]
            · exact hlt z' hltz⟩
        | none =>
          rw [h3] at h
          have hr3 := (Mask8.firstFalse_none_iff _).mp h3
          cases h4 : g.r4.firstFalse with
          | some z4 =>
            rw [h4] at h; cases h
            have ⟨hf, hlt⟩ := Mask8.firstFalse_some _ _ h4
            exact ⟨hf, fun w' z' hord => by
              rcases hord with hltw | ⟨rfl, hltz⟩
              · fin_cases w' <;> simp_all [get, row]
              · exact hlt z' hltz⟩
          | none =>
            rw [h4] at h
            have hr4 := (Mask8.firstFalse_none_iff _).mp h4
            cases h5 : g.r5.firstFalse with
            | some z5 =>
              rw [h5] at h; cases h
              have ⟨hf, hlt⟩ := Mask8.firstFalse_some _ _ h5
              exact ⟨hf, fun w' z' hord => by
                rcases hord with hltw | ⟨rfl, hltz⟩
                · fin_cases w' <;> simp_all [get, row]
                · exact hlt z' hltz⟩
            | none =>
              rw [h5] at h
              have hr5 := (Mask8.firstFalse_none_iff _).mp h5
              cases h6 : g.r6.firstFalse with
              | some z6 =>
                rw [h6] at h; cases h
                have ⟨hf, hlt⟩ := Mask8.firstFalse_some _ _ h6
                exact ⟨hf, fun w' z' hord => by
                  rcases hord with hltw | ⟨rfl, hltz⟩
                  · fin_cases w' <;> simp_all [get, row]
                  · exact hlt z' hltz⟩
              | none =>
                rw [h6] at h
                have hr6 := (Mask8.firstFalse_none_iff _).mp h6
                cases h7 : g.r7.firstFalse with
                | some z7 =>
                  rw [h7] at h; cases h
                  have ⟨hf, hlt⟩ := Mask8.firstFalse_some _ _ h7
                  exact ⟨hf, fun w' z' hord => by
                    rcases hord with hltw | ⟨rfl, hltz⟩
                    · fin_cases w' <;> simp_all [get, row]
                    · exact hlt z' hltz⟩
                | none =>
                  rw [h7] at h; cases h

end Grid8

/-! #### Explicit Construction of the `48` Maximal `(2, 4)`/`(4, 2)` Pairs at `s = 3` -/

/-- Recursive 4-branch generator of all `4^k` maximal cocycle-valid pairs at borrow width `k`
(mirroring `stepMaxPair` on `List ℕ`). -/
def genMaxPairsNat : ℕ → List (List ℕ × List ℕ)
  | 0 => [([0], [0])]
  | k + 1 =>
    let M := 2 ^ k
    (genMaxPairsNat k).flatMap fun ⟨W, Z⟩ =>
      [ (W.map (fun w => 2 * w), Z.flatMap (fun z => [2 * z, 2 * z + 1])),
        (W.map (fun w => 2 * w + 1), Z.flatMap (fun z => [2 * z + 1, 2 * ((z + 1) % M)])),
        (W.flatMap (fun w => [2 * w, 2 * w + 1]), Z.map (fun z => 2 * z + 1)),
        (W.flatMap (fun w => [2 * w, 2 * ((w + M - 1) % M) + 1]), Z.map (fun z => 2 * z)) ]

/-- The `48` maximal cocycle-valid pairs of shapes `(2, 4)` and `(4, 2)` on `Fin 8 × Fin 8`. -/
def rects48 : List (Mask8 × Mask8) :=
  ((genMaxPairsNat 3).map fun ⟨W, Z⟩ =>
    (Mask8.ofFn (fun i => W.contains i.val), Mask8.ofFn (fun i => Z.contains i.val))).filter
    fun r => (r.1.card == 2 && r.2.card == 4) || (r.1.card == 4 && r.2.card == 2)

/-- 3-bit boolean borrow vector `(b_1, b_2, b_3)` on `Fin 8 × Fin 8`. -/
def borrow3Bool (w z : Fin 8) : Bool × Bool × Bool :=
  (decide (z.val % 2 < w.val % 2),
   decide (z.val % 4 < w.val % 4),
   decide (z.val < w.val))

/-- Anchored cocycle-validity predicate on `Mask8 × Mask8` for `s = 3`. -/
def isAnchoredCocycle3Bool (W Z : Mask8) : Bool :=
  match W.firstTrue, Z.firstTrue with
  | some w0, some z0 =>
    let b00 := borrow3Bool w0 z0
    (List.finRange 8).all fun w =>
      !W.get w || (List.finRange 8).all fun z =>
        !Z.get z ||
          let bwz := borrow3Bool w z
          let bw0 := borrow3Bool w z0
          let b0z := borrow3Bool w0 z
          (xor (xor bwz.1 bw0.1) (xor b0z.1 b00.1) == false) &&
          (xor (xor bwz.2.1 bw0.2.1) (xor b0z.2.1 b00.2.1) == false) &&
          (xor (xor bwz.2.2 bw0.2.2) (xor b0z.2.2 b00.2.2) == false)
  | _, _ => false

/-- Lexicographic minimum cell index `8 * w + z ∈ {0..63}` of a rectangle. -/
def rectMinCellNat (r : Mask8 × Mask8) : ℕ :=
  match r.1.firstTrue, r.2.firstTrue with
  | some w, some z => 8 * w.val + z.val
  | _, _ => 64

private lemma borrow3Bool_eq_borrowVec (w z : Fin 8) :
    (borrowVec 3 w z 0 = if (borrow3Bool w z).1 then 1 else 0) ∧
    (borrowVec 3 w z 1 = if (borrow3Bool w z).2.1 then 1 else 0) ∧
    (borrowVec 3 w z 2 = if (borrow3Bool w z).2.2 then 1 else 0) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [borrowVec, borrowBit, borrow3Bool, Nat.mod_eq_of_lt w.isLt,
    Nat.mod_eq_of_lt z.isLt]

private lemma bool_xor4_eq_false_imp_zmod2 (a b c d : Bool)
    (h : xor (xor a b) (xor c d) = false) :
    (if a then (1 : ZMod 2) else 0) + (if b then 1 else 0) +
    (if c then 1 else 0) + (if d then 1 else 0) = 0 := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all <;> decide

private lemma isAnchoredCocycle3Bool_sound {W Z : Mask8}
    (h : isAnchoredCocycle3Bool W Z = true) :
    IsCocycleValid 3 W.toFinset Z.toFinset := by
  unfold isAnchoredCocycle3Bool at h
  cases hw0 : W.firstTrue with
  | none => rw [hw0] at h; cases h
  | some w0 =>
    cases hz0 : Z.firstTrue with
    | none => rw [hw0, hz0] at h; cases h
    | some z0 =>
      rw [hw0, hz0] at h
      simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
        Bool.not_eq_true', Bool.and_eq_true, beq_iff_eq] at h
      have hanc : ∀ w z : Fin 8, W.get w = true → Z.get z = true →
          borrowVec 3 w z + borrowVec 3 w z0 + borrowVec 3 w0 z + borrowVec 3 w0 z0 = 0 := by
        intro w z hw hz
        have hw' := (h w).resolve_left (by simp [hw])
        have h' := (hw' z).resolve_left (by simp [hz])
        funext i
        simp only [Pi.add_apply, Pi.zero_apply]
        have hb1 := borrow3Bool_eq_borrowVec w z
        have hb2 := borrow3Bool_eq_borrowVec w z0
        have hb3 := borrow3Bool_eq_borrowVec w0 z
        have hb4 := borrow3Bool_eq_borrowVec w0 z0
        fin_cases i
        · change borrowVec 3 w z 0 + borrowVec 3 w z0 0 + borrowVec 3 w0 z 0 + borrowVec 3 w0 z0 0 = 0
          rw [hb1.1, hb2.1, hb3.1, hb4.1]; exact bool_xor4_eq_false_imp_zmod2 _ _ _ _ h'.1.1
        · change borrowVec 3 w z 1 + borrowVec 3 w z0 1 + borrowVec 3 w0 z 1 + borrowVec 3 w0 z0 1 = 0
          rw [hb1.2.1, hb2.2.1, hb3.2.1, hb4.2.1]; exact bool_xor4_eq_false_imp_zmod2 _ _ _ _ h'.1.2
        · change borrowVec 3 w z 2 + borrowVec 3 w z0 2 + borrowVec 3 w0 z 2 + borrowVec 3 w0 z0 2 = 0
          rw [hb1.2.2, hb2.2.2, hb3.2.2, hb4.2.2]; exact bool_xor4_eq_false_imp_zmod2 _ _ _ _ h'.2
      intro w1 hw1 w2 hw2 z1 hz1 z2 hz2
      rw [Mask8.mem_toFinset] at hw1 hw2 hz1 hz2
      have h11 := hanc w1 z1 hw1 hz1
      have h12 := hanc w1 z2 hw1 hz2
      have h21 := hanc w2 z1 hw2 hz1
      have h22 := hanc w2 z2 hw2 hz2
      calc borrowVec 3 w1 z1 + borrowVec 3 w1 z2 + borrowVec 3 w2 z1 + borrowVec 3 w2 z2
          = (borrowVec 3 w1 z1 + borrowVec 3 w1 z0 + borrowVec 3 w0 z1 + borrowVec 3 w0 z0) +
            (borrowVec 3 w1 z2 + borrowVec 3 w1 z0 + borrowVec 3 w0 z2 + borrowVec 3 w0 z0) +
            (borrowVec 3 w2 z1 + borrowVec 3 w2 z0 + borrowVec 3 w0 z1 + borrowVec 3 w0 z0) +
            (borrowVec 3 w2 z2 + borrowVec 3 w2 z0 + borrowVec 3 w0 z2 + borrowVec 3 w0 z0) := by
            funext i; simp only [Pi.add_apply]
            have h2a : ∀ x : ZMod 2, x + x = 0 := zmod2_add_self
            calc borrowVec 3 w1 z1 i + borrowVec 3 w1 z2 i + borrowVec 3 w2 z1 i + borrowVec 3 w2 z2 i
                = borrowVec 3 w1 z1 i + borrowVec 3 w1 z2 i + borrowVec 3 w2 z1 i + borrowVec 3 w2 z2 i +
                  (borrowVec 3 w1 z0 i + borrowVec 3 w1 z0 i) +
                  (borrowVec 3 w2 z0 i + borrowVec 3 w2 z0 i) +
                  (borrowVec 3 w0 z1 i + borrowVec 3 w0 z1 i) +
                  (borrowVec 3 w0 z2 i + borrowVec 3 w0 z2 i) +
                  (borrowVec 3 w0 z0 i + borrowVec 3 w0 z0 i) +
                  (borrowVec 3 w0 z0 i + borrowVec 3 w0 z0 i) := by simp [h2a]
              _ = _ := by abel
        _ = 0 := by rw [h11, h12, h21, h22]; simp

/-- Appendix A, Proposition A.1 (part 1): `rects48` has exact length `48` (`24` of shape `(2, 4)`
and `24` of shape `(4, 2)`), with no duplicates, all cocycle-valid. -/
theorem prop_A1_rects48_basic :
    rects48.length = 48 ∧
    rects48.Nodup ∧
    (rects48.filter fun r => r.1.card == 2 && r.2.card == 4).length = 24 ∧
    (rects48.filter fun r => r.1.card == 4 && r.2.card == 2).length = 24 ∧
    rects48.all (fun r =>
      isAnchoredCocycle3Bool r.1 r.2 &&
      ((r.1.card == 2 && r.2.card == 4) || (r.1.card == 4 && r.2.card == 2))) = true := by
  decide

private lemma mem_list48_iff_cocycle_shape (R48 : List (Mask8 × Mask8))
    (hlen : R48.length = 48) (hnd : R48.Nodup)
    (hallBool : R48.all (fun r =>
      isAnchoredCocycle3Bool r.1 r.2 &&
      ((r.1.card == 2 && r.2.card == 4) || (r.1.card == 4 && r.2.card == 2))) = true)
    (W Z : Finset (Fin 8)) :
    (Mask8.ofFinset W, Mask8.ofFinset Z) ∈ R48 ↔
      IsCocycleValid 3 W Z ∧
      ((W.card = 2 ∧ Z.card = 4) ∨ (W.card = 4 ∧ Z.card = 2)) := by
  classical
  have hall := List.all_eq_true.mp hallBool
  have hfwd : ∀ r ∈ R48,
      IsMaximalCocyclePair 3 r.1.toFinset r.2.toFinset ∧
      ((r.1.toFinset.card = 2 ∧ r.2.toFinset.card = 4) ∨
       (r.1.toFinset.card = 4 ∧ r.2.toFinset.card = 2)) := by
    intro r hr
    have hchk := hall r hr
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hchk
    have hcoc : IsCocycleValid 3 r.1.toFinset r.2.toFinset := isAnchoredCocycle3Bool_sound hchk.1
    have hsh : (r.1.toFinset.card = 2 ∧ r.2.toFinset.card = 4) ∨
        (r.1.toFinset.card = 4 ∧ r.2.toFinset.card = 2) := by
      rw [Mask8.card_eq_toFinset_card, Mask8.card_eq_toFinset_card] at hchk
      exact hchk.2
    have hne : IsNonemptyCocycleValid 3 r.1.toFinset r.2.toFinset := by
      refine ⟨Finset.card_pos.mp ?_, Finset.card_pos.mp ?_, hcoc⟩ <;> omega
    rcases exists_maximalCocyclePair_superset 3 hne with ⟨W', Z', hmax', hWW', hZZ'⟩
    have harea' := maxCocyclePair_area 3 hmax'
    have harea : r.1.toFinset.card * r.2.toFinset.card = 8 := by
      rcases hsh with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
    have hleW := Finset.card_le_card hWW'
    have hleZ := Finset.card_le_card hZZ'
    have hWpos : 1 ≤ r.1.toFinset.card := by rcases hsh with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
    have hZpos : 1 ≤ r.2.toFinset.card := by rcases hsh with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega
    have hWeq : W' = r.1.toFinset := by
      have : W'.card ≤ r.1.toFinset.card := by nlinarith
      exact (Finset.eq_of_subset_of_card_le hWW' this).symm
    have hZeq : Z' = r.2.toFinset := by
      have : Z'.card ≤ r.2.toFinset.card := by nlinarith
      exact (Finset.eq_of_subset_of_card_le hZZ' this).symm
    rw [hWeq, hZeq] at hmax'
    exact ⟨hmax', hsh⟩
  -- Use Theorem 2.1(c) `maxCocyclePairs_shape_card` on subtypes (avoiding `Finset.univ` reduction).
  let Sub24 := { p : Finset (Fin (2 ^ 3)) × Finset (Fin (2 ^ 3)) //
    IsMaximalCocyclePair 3 p.1 p.2 ∧ p.1.card = 2 ^ 1 ∧ p.2.card = 2 ^ (3 - 1) }
  let Sub42 := { p : Finset (Fin (2 ^ 3)) × Finset (Fin (2 ^ 3)) //
    IsMaximalCocyclePair 3 p.1 p.2 ∧ p.1.card = 2 ^ 2 ∧ p.2.card = 2 ^ (3 - 2) }
  let Sub48 := { p : Finset (Fin (2 ^ 3)) × Finset (Fin (2 ^ 3)) //
    IsMaximalCocyclePair 3 p.1 p.2 ∧ ((p.1.card = 2 ∧ p.2.card = 4) ∨ (p.1.card = 4 ∧ p.2.card = 2)) }
  have hSub48_equiv : Sub48 ≃ Sub24 ⊕ Sub42 :=
    { toFun := fun ⟨p, hmax, hsh⟩ =>
        if h24 : p.1.card = 2 ∧ p.2.card = 4 then Sum.inl ⟨p, hmax, h24.1, h24.2⟩
        else Sum.inr ⟨p, hmax, (hsh.resolve_left h24).1, (hsh.resolve_left h24).2⟩
      invFun := fun s => match s with
        | Sum.inl ⟨p, hmax, h1, h2⟩ => ⟨p, hmax, Or.inl ⟨h1, h2⟩⟩
        | Sum.inr ⟨p, hmax, h1, h2⟩ => ⟨p, hmax, Or.inr ⟨h1, h2⟩⟩
      left_inv := fun ⟨p, hmax, hsh⟩ => by
        dsimp only
        split_ifs <;> rfl
      right_inv := fun s => by
        cases s with
        | inl q =>
          rcases q with ⟨p, hmax, h1, h2⟩
          dsimp only
          have h24 : p.1.card = 2 ∧ p.2.card = 4 := ⟨h1, h2⟩
          simp [h24]
        | inr q =>
          rcases q with ⟨p, hmax, h1, h2⟩
          dsimp only
          have hnot : ¬ (p.1.card = 2 ∧ p.2.card = 4) := by omega
          simp [hnot] }
  have hcard_Sub48 : Fintype.card Sub48 = 48 := by
    rw [Fintype.card_congr hSub48_equiv, Fintype.card_sum]
    have h24 : Fintype.card Sub24 = 24 := by convert maxCocyclePairs_shape_card 3 1; decide
    have h42 : Fintype.card Sub42 = 24 := by convert maxCocyclePairs_shape_card 3 2; decide
    omega
  let f : { r : Mask8 × Mask8 // r ∈ R48 } → Sub48 :=
    fun ⟨r, hr⟩ => ⟨(r.1.toFinset, r.2.toFinset), hfwd r hr⟩
  have hf_inj : Function.Injective f := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    have hpair : (a.1.toFinset, a.2.toFinset) = (b.1.toFinset, b.2.toFinset) := congrArg Subtype.val hab
    exact Subtype.ext (Prod.ext (Mask8.toFinset_injective (congrArg Prod.fst hpair))
                                (Mask8.toFinset_injective (congrArg Prod.snd hpair)))
  have hcard_dom : Fintype.card { r : Mask8 × Mask8 // r ∈ R48 } = 48 := by
    have heq : { r : Mask8 × Mask8 // r ∈ R48 } ≃ { r // r ∈ R48.toFinset } :=
      Equiv.subtypeEquivRight fun r => List.mem_toFinset.symm
    rw [Fintype.card_congr heq, Fintype.card_coe, List.toFinset_card_of_nodup hnd, hlen]
  have hf_surj : Function.Surjective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf_inj, by rw [hcard_dom, hcard_Sub48]⟩ |>.2
  constructor
  · intro hmem
    have ⟨hmax, hsh⟩ := hfwd _ hmem
    rw [Mask8.toFinset_ofFinset, Mask8.toFinset_ofFinset] at hmax hsh
    exact ⟨hmax.1.2.2, hsh⟩
  · rintro ⟨hcoc, hsh⟩
    have hne : IsNonemptyCocycleValid 3 W Z := by
      refine ⟨Finset.card_pos.mp ?_, Finset.card_pos.mp ?_, hcoc⟩ <;> omega
    rcases exists_maximalCocyclePair_superset 3 hne with ⟨W', Z', hmax', hWW', hZZ'⟩
    have harea' := maxCocyclePair_area 3 hmax'
    have harea : W.card * Z.card = 8 := by rcases hsh with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
    have hleW := Finset.card_le_card hWW'
    have hleZ := Finset.card_le_card hZZ'
    have hWpos : 1 ≤ W.card := by rcases hsh with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
    have hZpos : 1 ≤ Z.card := by rcases hsh with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega
    have hWeq : W' = W := (Finset.eq_of_subset_of_card_le hWW' (by nlinarith)).symm
    have hZeq : Z' = Z := (Finset.eq_of_subset_of_card_le hZZ' (by nlinarith)).symm
    rw [hWeq, hZeq] at hmax'
    rcases hf_surj ⟨(W, Z), hmax', hsh⟩ with ⟨⟨r, hr⟩, hrEq⟩
    have hpair : (r.1.toFinset, r.2.toFinset) = (W, Z) := congrArg Subtype.val hrEq
    have h1 : r.1 = Mask8.ofFinset W := by
      rw [← Mask8.ofFinset_toFinset r.1]
      exact congrArg Mask8.ofFinset (congrArg Prod.fst hpair)
    have h2 : r.2 = Mask8.ofFinset Z := by
      rw [← Mask8.ofFinset_toFinset r.2]
      exact congrArg Mask8.ofFinset (congrArg Prod.snd hpair)
    rwa [← h1, ← h2]

/-- Exact characterization of `rects48`: a pair `(W, Z)` of subsets of `Fin 8` is cocycle-valid
at `s = 3` of shape `(2, 4)` or `(4, 2)` iff `(Mask8.ofFinset W, Mask8.ofFinset Z) ∈ rects48`. -/
theorem mem_rects48_iff_cocycle_shape (W Z : Finset (Fin 8)) :
    (Mask8.ofFinset W, Mask8.ofFinset Z) ∈ rects48 ↔
      IsCocycleValid 3 W Z ∧
      ((W.card = 2 ∧ Z.card = 4) ∨ (W.card = 4 ∧ Z.card = 2)) :=
  mem_list48_iff_cocycle_shape rects48
    prop_A1_rects48_basic.1 prop_A1_rects48_basic.2.1 prop_A1_rects48_basic.2.2.2.2 W Z

/-! #### Canonical Least-Uncovered-Cell Exact-Cover Search (`Search(0)`) & Kernel Certificates -/

/-- Canonical least-uncovered-cell exact-cover search of Appendix A (`Search(0)`),
maintaining the filtered list of rectangles disjoint from `cov`. -/
def searchS3Aux : ℕ → Grid8 → List (Mask8 × Mask8) → List (List (Mask8 × Mask8))
  | 0, _, _ => []
  | fuel + 1, cov, cands =>
    match cov.firstUncovered with
    | none => [[]]
    | some (w, z) =>
      let avail := cands.filter fun r => (Grid8.ofRect r.1 r.2).disjoint cov
      let atCell := avail.filter fun r => r.1.firstTrue == some w && r.2.firstTrue == some z
      atCell.flatMap fun r =>
        (searchS3Aux fuel (cov.or (Grid8.ofRect r.1 r.2)) avail).map (r :: ·)

/-- Complete list of all disjoint tilings of `Fin 8 × Fin 8` using rectangles from `rects48`. -/
def tilingsS3 : List (List (Mask8 × Mask8)) :=
  searchS3Aux 9 Grid8.empty rects48

def listRowDeg (T : List (Mask8 × Mask8)) (w : Fin 8) : ℕ :=
  (T.filter fun r => r.1.get w).length

def listColDeg (T : List (Mask8 × Mask8)) (z : Fin 8) : ℕ :=
  (T.filter fun r => r.2.get z).length

def tilingMaxLoad (T : List (Mask8 × Mask8)) : ℕ :=
  ((List.finRange 8).map (listRowDeg T) ++ (List.finRange 8).map (listColDeg T)).foldl max 0

/-- Boolean check that a list `T` is a disjoint tiling of `Fin 8 × Fin 8` by rectangles in `rects48`. -/
def isGridTilingListBool (T : List (Mask8 × Mask8)) : Bool :=
  T.all (fun r => rects48.contains r) &&
  (List.finRange 8).all fun w =>
    (List.finRange 8).all fun z =>
      (T.filter fun r => r.1.get w && r.2.get z).length == 1

/-- Boolean check that `T` is strictly sorted by `rectMinCellNat` (ensuring canonical uniqueness). -/
def isStrictlySortedMinCell : List (Mask8 × Mask8) → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => (rectMinCellNat a < rectMinCellNat b) && isStrictlySortedMinCell (b :: rest)

/-- Appendix A, Proposition A.1 (kernel-verified via `decide`):
1. `tilingsS3` finds exactly `50` disjoint `8`-rectangle tilings of `Fin 8 × Fin 8`;
2. Exact distribution by count `a` of `(2, 4)` rectangles is `[5, 0, 12, 0, 16, 0, 12, 0, 5]`;
3. Every single tiling has `max(max_w deg(w), max_z deg(z)) = 4` (`0` tilings with max load `≤ 3`);
4. Every output tiling is valid, duplicate-free, strictly sorted by minimum cell, and distinct. -/
theorem prop_A1_kernel_certificate :
    tilingsS3.length = 50 ∧
    tilingsS3.Nodup ∧
    tilingsS3.all (fun T => T.length == 8 && isGridTilingListBool T && isStrictlySortedMinCell T) = true ∧
    ([0, 1, 2, 3, 4, 5, 6, 7, 8].map fun a =>
      (tilingsS3.filter fun T => (T.filter fun r => r.1.card == 2).length == a).length) =
      [5, 0, 12, 0, 16, 0, 12, 0, 5] ∧
    tilingsS3.all (fun T => tilingMaxLoad T == 4) = true ∧
    (tilingsS3.filter fun T => decide (tilingMaxLoad T ≤ 3)).length = 0 := by
  decide

/-- A finite set `G` of `(Mask8 × Mask8)` rectangles is a disjoint tiling of `Fin 8 × Fin 8`
using rectangles from `rects48`. -/
def IsGridTiling (G : Finset (Mask8 × Mask8)) : Prop :=
  (∀ r ∈ G, r ∈ rects48) ∧
  (∀ w z : Fin 8, ∃! r, r ∈ G ∧ r.1.get w = true ∧ r.2.get z = true)

private lemma rect_in_rects48_nonempty {r : Mask8 × Mask8} (hr : r ∈ rects48) :
    (∃ w : Fin 8, r.1.get w = true) ∧ (∃ z : Fin 8, r.2.get z = true) := by
  have hsh := (mem_rects48_iff_cocycle_shape r.1.toFinset r.2.toFinset).mp (by
    rwa [Mask8.ofFinset_toFinset, Mask8.ofFinset_toFinset])
  have hW : r.1.toFinset.Nonempty := Finset.card_pos.mp (by rcases hsh.2 with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega)
  have hZ : r.2.toFinset.Nonempty := Finset.card_pos.mp (by rcases hsh.2 with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega)
  rcases hW with ⟨w, hw⟩
  rcases hZ with ⟨z, hz⟩
  exact ⟨⟨w, (Mask8.mem_toFinset _ _).mp hw⟩, ⟨z, (Mask8.mem_toFinset _ _).mp hz⟩⟩

/-- Soundness + completeness of `searchS3Aux`: any remaining set `rem` partitioning the uncovered
cells of `cov` (with `rem.card < fuel`) is found by `searchS3Aux`. -/
private lemma searchS3Aux_complete :
    ∀ (fuel : ℕ) (cov : Grid8) (cands : List (Mask8 × Mask8)) (rem : Finset (Mask8 × Mask8)),
      (∀ r ∈ rem, r ∈ cands ∧ r ∈ rects48) →
      rem.card < fuel →
      (∀ w z : Fin 8,
        if cov.get w z = true then ∀ r ∈ rem, ¬ (r.1.get w = true ∧ r.2.get z = true)
        else ∃! r, r ∈ rem ∧ r.1.get w = true ∧ r.2.get z = true) →
      ∃ T ∈ searchS3Aux fuel cov cands, T.Nodup ∧ T.toFinset = rem := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ hcard _; omega
  | succ fuel ih =>
    intro cov cands rem hsub hcard hpart
    unfold searchS3Aux
    cases hfu : cov.firstUncovered with
    | none =>
      have hall := (Grid8.firstUncovered_none_iff cov).mp hfu
      have hempty : rem = ∅ := by
        by_contra hne
        rcases Finset.nonempty_iff_ne_empty.mpr hne with ⟨r, hr⟩
        have ⟨⟨w, hw⟩, ⟨z, hz⟩⟩ := rect_in_rects48_nonempty (hsub r hr).2
        have hnc := hpart w z
        simp only [hall w z, ↓reduceIte] at hnc
        exact hnc r hr ⟨hw, hz⟩
      exact ⟨[], by simp, List.nodup_nil, by simp [hempty]⟩
    | some p =>
      rcases p with ⟨w, z⟩
      have ⟨hunc, hlt_cov⟩ := Grid8.firstUncovered_some cov w z hfu
      have hcell := hpart w z
      simp only [hunc, Bool.false_eq_true, ↓reduceIte] at hcell
      rcases hcell with ⟨r, ⟨hr_rem, hrw, hrz⟩, huniq⟩
      -- Every `r' ∈ rem` is disjoint from `cov`, hence lies in `avail`.
      let avail := cands.filter fun r' => (Grid8.ofRect r'.1 r'.2).disjoint cov
      have hrem_avail : ∀ r' ∈ rem, r' ∈ avail := by
        intro r' hr'
        rw [List.mem_filter]
        refine ⟨(hsub r' hr').1, (Grid8.disjoint_iff _ _).mpr ?_⟩
        intro w' z' ⟨hrect, hcov'⟩
        rw [Grid8.get_ofRect, Bool.and_eq_true] at hrect
        have hc := hpart w' z'
        simp only [hcov', ↓reduceIte] at hc
        exact hc r' hr' hrect
      -- `r` has minimum cell `(w, z)`, so `r ∈ atCell`.
      have hr_ftW : r.1.firstTrue = some w := by
        rw [Mask8.firstTrue_some_iff]
        refine ⟨hrw, fun w' hw' => ?_⟩
        by_contra hne
        have hw't : r.1.get w' = true := by cases h : r.1.get w' <;> simp_all
        have hcov' := hlt_cov w' z (Or.inl hw')
        have hc := hpart w' z
        simp only [hcov', ↓reduceIte] at hc
        exact hc r hr_rem ⟨hw't, hrz⟩
      have hr_ftZ : r.2.firstTrue = some z := by
        rw [Mask8.firstTrue_some_iff]
        refine ⟨hrz, fun z' hz' => ?_⟩
        by_contra hne
        have hz't : r.2.get z' = true := by cases h : r.2.get z' <;> simp_all
        have hcov' := hlt_cov w z' (Or.inr ⟨rfl, hz'⟩)
        have hc := hpart w z'
        simp only [hcov', ↓reduceIte] at hc
        exact hc r hr_rem ⟨hrw, hz't⟩
      let atCell := avail.filter fun r' => r'.1.firstTrue == some w && r'.2.firstTrue == some z
      have hr_atCell : r ∈ atCell := by
        rw [List.mem_filter]
        exact ⟨hrem_avail r hr_rem, by simp [hr_ftW, hr_ftZ]⟩
      -- Recurse on `rem' = rem.erase r` and `cov' = cov.or (Grid8.ofRect r.1 r.2)`.
      let rem' := rem.erase r
      let cov' := cov.or (Grid8.ofRect r.1 r.2)
      have hcard' : rem'.card < fuel := by
        dsimp only [rem']
        have hpos : 0 < rem.card := Finset.card_pos.mpr ⟨r, hr_rem⟩
        rw [Finset.card_erase_of_mem hr_rem]
        omega
      have hsub' : ∀ r' ∈ rem', r' ∈ avail ∧ r' ∈ rects48 := by
        intro r' hr'
        have hr'm := Finset.mem_of_mem_erase hr'
        exact ⟨hrem_avail r' hr'm, (hsub r' hr'm).2⟩
      have hpart' : ∀ w' z' : Fin 8,
          if cov'.get w' z' = true then ∀ r' ∈ rem', ¬ (r'.1.get w' = true ∧ r'.2.get z' = true)
          else ∃! r', r' ∈ rem' ∧ r'.1.get w' = true ∧ r'.2.get z' = true := by
        intro w' z'
        have hget : cov'.get w' z' = (cov.get w' z' || (r.1.get w' && r.2.get z')) := by
          rw [Grid8.get_or, Grid8.get_ofRect]
        rw [hget]
        by_cases hcov0 : cov.get w' z' = true
        · simp only [hcov0, Bool.true_or, ↓reduceIte]
          intro r' hr'
          have hc := hpart w' z'
          simp only [hcov0, ↓reduceIte] at hc
          exact hc r' (Finset.mem_of_mem_erase hr')
        · have hcovF : cov.get w' z' = false := Bool.eq_false_iff.mpr hcov0
          have hc := hpart w' z'
          simp only [hcovF, Bool.false_eq_true, ↓reduceIte] at hc
          rcases hc with ⟨r0, ⟨hr0_rem, hr0w, hr0z⟩, huniq0⟩
          by_cases hr_cov : r.1.get w' = true ∧ r.2.get z' = true
          · simp only [hcovF, hr_cov.1, hr_cov.2, Bool.and_self, Bool.false_or, ↓reduceIte]
            intro r' hr' ⟨hr'w, hr'z⟩
            have heq1 : r = r0 := huniq0 r ⟨hr_rem, hr_cov.1, hr_cov.2⟩
            have heq2 : r' = r0 := huniq0 r' ⟨Finset.mem_of_mem_erase hr', hr'w, hr'z⟩
            exact (Finset.ne_of_mem_erase hr') (heq2.trans heq1.symm)
          · have hboolF : (r.1.get w' && r.2.get z') = false := by
              cases h1 : r.1.get w' with
              | false => rfl
              | true =>
                cases h2 : r.2.get z' with
                | false => rfl
                | true => exact absurd ⟨h1, h2⟩ hr_cov
            simp only [hcovF, hboolF, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
            have hr0_ne : r0 ≠ r := by rintro rfl; exact hr_cov ⟨hr0w, hr0z⟩
            refine ⟨r0, ⟨Finset.mem_erase.mpr ⟨hr0_ne, hr0_rem⟩, hr0w, hr0z⟩, ?_⟩
            rintro r' ⟨hr', hr'w, hr'z⟩
            exact huniq0 r' ⟨Finset.mem_of_mem_erase hr', hr'w, hr'z⟩
      rcases ih cov' avail rem' hsub' hcard' hpart' with ⟨T', hT'mem, hT'nodup, hT'set⟩
      refine ⟨r :: T', ?_, ?_, ?_⟩
      · rw [List.mem_flatMap]
        exact ⟨r, hr_atCell, List.mem_map.mpr ⟨T', hT'mem, rfl⟩⟩
      · rw [List.nodup_cons]
        refine ⟨?_, hT'nodup⟩
        intro hr_in
        have : r ∈ rem' := by rw [← hT'set]; exact List.mem_toFinset.mpr hr_in
        exact (Finset.notMem_erase r rem) this
      · rw [List.toFinset_cons, hT'set, Finset.insert_erase hr_rem]

private lemma isGridTiling_card_eq_eight {G : Finset (Mask8 × Mask8)} (hG : IsGridTiling G) :
    G.card = 8 := by
  have hsum : ∑ r ∈ G, r.1.toFinset.card * r.2.toFinset.card = 64 := by
    calc ∑ r ∈ G, r.1.toFinset.card * r.2.toFinset.card
        = ∑ r ∈ G, ∑ w : Fin 8, ∑ z : Fin 8,
            if r.1.get w = true ∧ r.2.get z = true then 1 else 0 := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [← Finset.card_product]
          have heq : (r.1.toFinset ×ˢ r.2.toFinset).card =
              ∑ w : Fin 8, ∑ z : Fin 8, if r.1.get w = true ∧ r.2.get z = true then 1 else 0 := by
            rw [← Fintype.sum_prod_type', ← Finset.card_filter]
            congr 1; ext ⟨w, z⟩; simp [Mask8.mem_toFinset]
          exact heq
      _ = ∑ w : Fin 8, ∑ z : Fin 8, ∑ r ∈ G,
            if r.1.get w = true ∧ r.2.get z = true then 1 else 0 := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun w _ => Finset.sum_comm
      _ = ∑ _w : Fin 8, ∑ _z : Fin 8, (1 : ℕ) := by
          refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun z _ => ?_
          rcases hG.2 w z with ⟨r0, ⟨hr0, hr0w, hr0z⟩, huniq⟩
          rw [Finset.sum_eq_single r0]
          · simp [hr0w, hr0z]
          · intro r hr hne
            have hnot : ¬ (r.1.get w = true ∧ r.2.get z = true) := fun h => hne (huniq r ⟨hr, h.1, h.2⟩)
            simp [hnot]
          · intro hnot; exact absurd hr0 hnot
      _ = 64 := by simp
  have heach : ∀ r ∈ G, r.1.toFinset.card * r.2.toFinset.card = 8 := by
    intro r hr
    have hsh := ((mem_rects48_iff_cocycle_shape r.1.toFinset r.2.toFinset).mp (by
      rw [Mask8.ofFinset_toFinset, Mask8.ofFinset_toFinset]; exact hG.1 r hr)).2
    rcases hsh with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
  have hsum8 : ∑ r ∈ G, r.1.toFinset.card * r.2.toFinset.card = G.card * 8 := by
    rw [Finset.sum_congr rfl heach, Finset.sum_const, smul_eq_mul]
  omega

/-- Completeness of `tilingsS3`: EVERY disjoint tiling `G` of `Fin 8 × Fin 8` using rectangles
from `rects48` is produced by `tilingsS3`. -/
theorem tilingsS3_complete {G : Finset (Mask8 × Mask8)} (hG : IsGridTiling G) :
    ∃ T ∈ tilingsS3, T.Nodup ∧ T.toFinset = G := by
  have hcard : G.card < 9 := by rw [isGridTiling_card_eq_eight hG]; omega
  refine searchS3Aux_complete 9 Grid8.empty rects48 G (fun r hr => ⟨hG.1 r hr, hG.1 r hr⟩) hcard ?_
  intro w z
  simp only [Grid8.get_empty, Bool.false_eq_true, ↓reduceIte]
  exact hG.2 w z

private lemma strictlySorted_toFinset_inj :
    ∀ {T1 T2 : List (Mask8 × Mask8)},
      isStrictlySortedMinCell T1 = true →
      isStrictlySortedMinCell T2 = true →
      T1.toFinset = T2.toFinset →
      T1 = T2 := by
  intro T1
  induction T1 with
  | nil =>
    intro T2 _ _ h
    cases T2 with
    | nil => rfl
    | cons b bs =>
      have : b ∈ ([] : List (Mask8 × Mask8)).toFinset := by rw [h]; simp
      simp at this
  | cons a as ih =>
    intro T2 h1 h2 hset
    cases T2 with
    | nil =>
      have : a ∈ ([] : List (Mask8 × Mask8)).toFinset := by rw [← hset]; simp
      simp at this
    | cons b bs =>
      have hhead : ∀ (x : Mask8 × Mask8) (xs : List (Mask8 × Mask8)),
          isStrictlySortedMinCell (x :: xs) = true →
          ∀ y ∈ xs, rectMinCellNat x < rectMinCellNat y := by
        intro x xs
        induction xs generalizing x with
        | nil => intro _ y hy; simp at hy
        | cons z zs ihz =>
          intro hsort y hy
          simp only [isStrictlySortedMinCell, Bool.and_eq_true, decide_eq_true_eq] at hsort
          rcases List.mem_cons.mp hy with rfl | hy'
          · exact hsort.1
          · exact lt_trans hsort.1 (ihz z hsort.2 y hy')
      have htail : ∀ (x : Mask8 × Mask8) (xs : List (Mask8 × Mask8)),
          isStrictlySortedMinCell (x :: xs) = true → isStrictlySortedMinCell xs = true := by
        intro x xs hs
        cases xs with
        | nil => rfl
        | cons z zs =>
          simp only [isStrictlySortedMinCell, Bool.and_eq_true] at hs
          exact hs.2
      have ha_in : a ∈ b :: bs := by
        have : a ∈ (b :: bs).toFinset := by rw [← hset]; simp
        exact List.mem_toFinset.mp this
      have hb_in : b ∈ a :: as := by
        have : b ∈ (a :: as).toFinset := by rw [hset]; simp
        exact List.mem_toFinset.mp this
      have hab : a = b := by
        rcases List.mem_cons.mp ha_in with rfl | ha_bs
        · rfl
        · rcases List.mem_cons.mp hb_in with hba | hb_as
          · exact hba.symm
          · exfalso
            have hlt1 := hhead b bs h2 a ha_bs
            have hlt2 := hhead a as h1 b hb_as
            omega
      subst hab
      have ha_not_as : a ∉ as := fun hm => lt_irrefl _ (hhead a as h1 a hm)
      have ha_not_bs : a ∉ bs := fun hm => lt_irrefl _ (hhead a bs h2 a hm)
      have htail_set : as.toFinset = bs.toFinset := by
        ext x
        have hx := Finset.ext_iff.mp hset x
        simp only [List.mem_toFinset, List.mem_cons] at hx ⊢
        constructor
        · intro h
          have hne : x ≠ a := fun heq => ha_not_as (heq ▸ h)
          exact (hx.mp (Or.inr h)).resolve_left hne
        · intro h
          have hne : x ≠ a := fun heq => ha_not_bs (heq ▸ h)
          exact (hx.mpr (Or.inr h)).resolve_left hne
      rw [ih (htail a as h1) (htail a bs h2) htail_set]

private lemma strictlySorted_nodup :
    ∀ {T : List (Mask8 × Mask8)}, isStrictlySortedMinCell T = true → T.Nodup := by
  intro T
  induction T with
  | nil => intro _; exact List.nodup_nil
  | cons a as ih =>
    intro hs
    have hhead : ∀ (x : Mask8 × Mask8) (xs : List (Mask8 × Mask8)),
        isStrictlySortedMinCell (x :: xs) = true →
        ∀ y ∈ xs, rectMinCellNat x < rectMinCellNat y := by
      intro x xs
      induction xs generalizing x with
      | nil => intro _ y hy; simp at hy
      | cons z zs ihz =>
        intro hsort y hy
        simp only [isStrictlySortedMinCell, Bool.and_eq_true, decide_eq_true_eq] at hsort
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact hsort.1
        · exact lt_trans hsort.1 (ihz z hsort.2 y hy')
    have htail : isStrictlySortedMinCell as = true := by
      cases as with
      | nil => rfl
      | cons z zs =>
        simp only [isStrictlySortedMinCell, Bool.and_eq_true] at hs
        exact hs.2
    rw [List.nodup_cons]
    exact ⟨fun ha => lt_irrefl _ (hhead a as hs a ha), ih htail⟩

private lemma isGridTilingListBool_sound {T : List (Mask8 × Mask8)}
    (hnd : T.Nodup) (hb : isGridTilingListBool T = true) :
    IsGridTiling T.toFinset := by
  simp only [isGridTilingListBool, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    true_implies, beq_iff_eq, List.elem_eq_mem, decide_eq_true_eq] at hb
  constructor
  · intro r hr
    exact hb.1 r (List.mem_toFinset.mp hr)
  · intro w z
    have hlen := hb.2 w z
    have hcard : (T.toFinset.filter fun r => r.1.get w = true ∧ r.2.get z = true).card = 1 := by
      have hfilt : (T.filter fun r => r.1.get w && r.2.get z).toFinset =
          T.toFinset.filter fun r => r.1.get w = true ∧ r.2.get z = true := by
        ext r; simp [Bool.and_eq_true]
      rw [← hfilt, List.toFinset_card_of_nodup (hnd.filter _), hlen]
    rcases Finset.card_eq_one.mp hcard with ⟨r0, hr0⟩
    refine ⟨r0, ?_, ?_⟩
    · have : r0 ∈ T.toFinset.filter fun r => r.1.get w = true ∧ r.2.get z = true := by
        rw [hr0]; simp
      exact Finset.mem_filter.mp this
    · intro r hr
      have : r ∈ T.toFinset.filter fun r => r.1.get w = true ∧ r.2.get z = true :=
        Finset.mem_filter.mpr hr
      rw [hr0, Finset.mem_singleton] at this
      exact this

private lemma le_foldl_max : ∀ (l : List ℕ) (a x : ℕ), x ∈ l → x ≤ l.foldl max a := by
  intro l
  induction l with
  | nil => intro _ _ hx; simp at hx
  | cons y ys ih =>
    intro a x hx
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hx'
    · have hbase : ∀ (m : List ℕ) (b : ℕ), b ≤ m.foldl max b := by
        intro m
        induction m with
        | nil => intro b; exact le_rfl
        | cons u us ihu => intro b; exact le_trans (le_max_left b u) (ihu (max b u))
      exact le_trans (le_max_right a x) (hbase ys (max a x))
    · exact ih (max a y) x hx'

private lemma foldl_max_exists_mem :
    ∀ (l : List ℕ) (a : ℕ), l.foldl max a = a ∨ ∃ x ∈ l, l.foldl max a = x := by
  intro l
  induction l with
  | nil => intro a; exact Or.inl rfl
  | cons y ys ih =>
    intro a
    simp only [List.foldl_cons]
    rcases ih (max a y) with heq | ⟨x, hx, heq⟩
    · rcases max_choice a y with hmax | hmax
      · exact Or.inl (heq.trans hmax)
      · exact Or.inr ⟨y, List.mem_cons_self, heq.trans hmax⟩
    · exact Or.inr ⟨x, List.mem_cons_of_mem y hx, heq⟩

/-- Appendix A, Proposition A.1 (exact cardinality of all disjoint `s = 3` `(2, 4)`/`(4, 2)`
grid tilings equals `50`, and ZERO of them have max row/col degree `≤ 3`). -/
theorem prop_A1_s3_grid_obstruction :
    letI := Classical.decPred IsGridTiling
    Fintype.card { G : Finset (Mask8 × Mask8) // IsGridTiling G } = 50 ∧
    ∀ G : Finset (Mask8 × Mask8), IsGridTiling G →
      ¬ ((∀ w : Fin 8, (G.filter fun r => r.1.get w = true).card ≤ 3) ∧
         (∀ z : Fin 8, (G.filter fun r => r.2.get z = true).card ≤ 3)) := by
  classical
  have hcert := prop_A1_kernel_certificate
  have hall_valid := List.all_eq_true.mp hcert.2.2.1
  have hall_ml4 := List.all_eq_true.mp hcert.2.2.2.2.1
  constructor
  · -- Bijection between `{ T // T ∈ tilingsS3 }` and `{ G // IsGridTiling G }`
    have hbij : Fintype.card { T : List (Mask8 × Mask8) // T ∈ tilingsS3 } =
        Fintype.card { G : Finset (Mask8 × Mask8) // IsGridTiling G } := by
      refine Fintype.card_of_bijective (f := fun ⟨T, hT⟩ =>
        ⟨T.toFinset, by
          have hv := hall_valid T hT
          simp only [Bool.and_eq_true] at hv
          exact isGridTilingListBool_sound (strictlySorted_nodup hv.2) hv.1.2⟩) ⟨?_, ?_⟩
      · rintro ⟨T1, hT1⟩ ⟨T2, hT2⟩ hEq
        have hv1 := hall_valid T1 hT1
        have hv2 := hall_valid T2 hT2
        simp only [Bool.and_eq_true] at hv1 hv2
        exact Subtype.ext (strictlySorted_toFinset_inj hv1.2 hv2.2 (congrArg Subtype.val hEq))
      · rintro ⟨G, hG⟩
        rcases tilingsS3_complete hG with ⟨T, hT, _, hset⟩
        exact ⟨⟨T, hT⟩, Subtype.ext hset⟩
    rw [← hbij]
    have hcard_list : Fintype.card { T : List (Mask8 × Mask8) // T ∈ tilingsS3 } = tilingsS3.length := by
      have heq : { T : List (Mask8 × Mask8) // T ∈ tilingsS3 } ≃ { T // T ∈ tilingsS3.toFinset } :=
        Equiv.subtypeEquivRight fun T => List.mem_toFinset.symm
      rw [Fintype.card_congr heq, Fintype.card_coe, List.toFinset_card_of_nodup hcert.2.1]
    rw [hcard_list, hcert.1]
  · intro G hG ⟨hrow, hcol⟩
    rcases tilingsS3_complete hG with ⟨T, hT, hnd, hset⟩
    have hml4 : tilingMaxLoad T = 4 := beq_iff_eq.mp (hall_ml4 T hT)
    -- Some row or column achieves degree `4`, contradicting `≤ 3`.
    rcases foldl_max_exists_mem ((List.finRange 8).map (listRowDeg T) ++ (List.finRange 8).map (listColDeg T)) 0 with
      h0 | ⟨d, hd_mem, hd_eq⟩
    · change tilingMaxLoad T = 0 at h0; omega
    · have hd4 : d = 4 := by
        change tilingMaxLoad T = d at hd_eq; omega
      rw [List.mem_append] at hd_mem
      rcases hd_mem with hrm | hcm
      · rcases List.mem_map.mp hrm with ⟨w, _, rfl⟩
        have hdeg : (G.filter fun r => r.1.get w = true).card = listRowDeg T w := by
          rw [← hset]
          have hfilt : (T.filter fun r => r.1.get w).toFinset =
              T.toFinset.filter fun r => r.1.get w = true := by
            ext r; simp
          rw [← hfilt, List.toFinset_card_of_nodup (hnd.filter _)]; rfl
        have := hrow w; omega
      · rcases List.mem_map.mp hcm with ⟨z, _, rfl⟩
        have hdeg : (G.filter fun r => r.2.get z = true).card = listColDeg T z := by
          rw [← hset]
          have hfilt : (T.filter fun r => r.2.get z).toFinset =
              T.toFinset.filter fun r => r.2.get z = true := by
            ext r; simp
          rw [← hfilt, List.toFinset_card_of_nodup (hnd.filter _)]; rfl
        have := hcol z; omega

/-! #### Proposition 3.3: No `𝔽₂³`-Equivariant Cover of `K_coreRel 3` Has Max Load `≤ 3` -/

/-- Diagonal shift action of `g ∈ 𝔽₂^s` on a vertex set `S ⊆ 𝔽₂^s × Fin (2^s)`. -/
def shiftCoreSet {s : ℕ} (g : Fin s → ZMod 2)
    (S : Finset ((Fin s → ZMod 2) × Fin (2 ^ s))) :
    Finset ((Fin s → ZMod 2) × Fin (2 ^ s)) :=
  S.image fun p => (p.1 + g, p.2)

/-- An exact biclique cover `C` of `K_coreRel s` is `𝔽₂^s`-equivariant if its family of
bicliques is invariant under the diagonal shift `g · ((x', w'), (y', z')) = ((x' + g, w'), (y' + g, z'))`. -/
def IsEquivariantCover (s : ℕ) (C : ExactBicliqueCover (K_coreRel s)) : Prop :=
  ∀ (g : Fin s → ZMod 2) (ℓ : C.L),
    ∃ ℓ' : C.L, C.U ℓ' = shiftCoreSet g (C.U ℓ) ∧ C.V ℓ' = shiftCoreSet g (C.V ℓ)

private lemma shiftCoreSet_liftU (s : ℕ) (W : Finset (Fin (2 ^ s))) (w0 z0 : Fin (2 ^ s))
    (a g : Fin s → ZMod 2) :
    shiftCoreSet g (liftU s W w0 z0 a) = liftU s W w0 z0 (a + g) := by
  ext ⟨x, w⟩
  simp only [shiftCoreSet, liftU, Finset.mem_image]
  constructor
  · rintro ⟨⟨x1, w1⟩, ⟨w2, hw2, h1⟩, h2⟩
    refine ⟨w2, hw2, Prod.ext ?_ ?_⟩
    · dsimp only
      have hx1 : a + borrowVec s w2 z0 + borrowVec s w0 z0 = x1 := congrArg Prod.fst h1
      have hx2 : x1 + g = x := congrArg Prod.fst h2
      rw [← hx2, ← hx1]
      simp only [add_assoc, add_comm g]
    · dsimp only
      have hw1 : w2 = w1 := congrArg Prod.snd h1
      have hw2' : w1 = w := congrArg Prod.snd h2
      exact hw1.trans hw2'
  · rintro ⟨w2, hw2, h⟩
    refine ⟨(a + borrowVec s w2 z0 + borrowVec s w0 z0, w2), ⟨w2, hw2, rfl⟩, Prod.ext ?_ ?_⟩
    · dsimp only
      have hx : a + g + borrowVec s w2 z0 + borrowVec s w0 z0 = x := congrArg Prod.fst h
      rw [← hx]
      simp only [add_assoc, add_comm g]
    · dsimp only
      exact congrArg Prod.snd h

private lemma shiftCoreSet_liftV (s : ℕ) (Z : Finset (Fin (2 ^ s))) (w0 : Fin (2 ^ s))
    (a g : Fin s → ZMod 2) :
    shiftCoreSet g (liftV s Z w0 a) = liftV s Z w0 (a + g) := by
  ext ⟨y, z⟩
  simp only [shiftCoreSet, liftV, Finset.mem_image]
  constructor
  · rintro ⟨⟨y1, z1⟩, ⟨z2, hz2, h1⟩, h2⟩
    refine ⟨z2, hz2, Prod.ext ?_ ?_⟩
    · dsimp only
      have hy1 : a + borrowVec s w0 z2 = y1 := congrArg Prod.fst h1
      have hy2 : y1 + g = y := congrArg Prod.fst h2
      rw [← hy2, ← hy1, add_assoc, add_comm g, ← add_assoc]
    · dsimp only
      have hz1 : z2 = z1 := congrArg Prod.snd h1
      have hz2' : z1 = z := congrArg Prod.snd h2
      exact hz1.trans hz2'
  · rintro ⟨z2, hz2, h⟩
    refine ⟨(a + borrowVec s w0 z2, z2), ⟨z2, hz2, rfl⟩, Prod.ext ?_ ?_⟩
    · dsimp only
      have hy : a + g + borrowVec s w0 z2 = y := congrArg Prod.fst h
      rw [← hy, add_assoc, add_comm (borrowVec s w0 z2) g, ← add_assoc]
    · dsimp only
      exact congrArg Prod.snd h

private lemma dyadic_s3_area_ineq {a w z : ℕ} (ha : a ≤ 3) (hw1 : 1 ≤ w) (hz1 : 1 ≤ z)
    (hw : w ≤ 2 ^ a) (hz : z ≤ 2 ^ (3 - a)) :
    3 * (w * z) ≤ 4 * (w + z) ∧
    (3 * (w * z) = 4 * (w + z) ↔ (w = 2 ∧ z = 4) ∨ (w = 4 ∧ z = 2)) := by
  interval_cases a
  · simp only [pow_zero, Nat.sub_zero] at hw hz; norm_num at hz
    have : w = 1 := by omega
    subst this; constructor <;> omega
  · norm_num at hw hz
    interval_cases w <;> interval_cases z <;> omega
  · norm_num at hw hz
    interval_cases w <;> interval_cases z <;> omega
  · norm_num at hw hz
    have : z = 1 := by omega
    subst this; constructor <;> omega

/-- Proposition 3.3: No `𝔽₂³`-equivariant exact biclique cover of `K_coreRel 3` (`C_4`)
achieves maximum vertex load `≤ 3` (whereas our non-equivariant lift-colored star-blowup
partition `starBlowupPartition 1` achieves exact load `3` at every vertex). -/
theorem no_equivariant_cover_K4_load_le_3 (C : ExactBicliqueCover (K_coreRel 3))
    (heq : IsEquivariantCover 3 C) :
    ¬ C.HasMaxLoadLe 3 := by
  classical
  rintro ⟨hrow, hcol⟩
  -- Deduplicated family `B` of nonempty bicliques of `C`.
  let B : Finset (Finset ((Fin 3 → ZMod 2) × Fin 8) × Finset ((Fin 3 → ZMod 2) × Fin 8)) :=
    (Finset.univ.image fun ℓ : C.L => (C.U ℓ, C.V ℓ)).filter fun p => p.1.Nonempty ∧ p.2.Nonempty
  have hB_bic : ∀ p ∈ B, IsBiclique (K_coreRel 3) p.1 p.2 ∧ p.1.Nonempty ∧ p.2.Nonempty := by
    intro p hp
    simp only [B, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hp
    rcases hp with ⟨⟨ℓ, rfl⟩, hne⟩
    exact ⟨C.isBiclique ℓ, hne⟩
  have hB_shift : ∀ g : Fin 3 → ZMod 2, ∀ p ∈ B,
      (shiftCoreSet g p.1, shiftCoreSet g p.2) ∈ B := by
    intro g p hp
    simp only [B, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hp ⊢
    rcases hp with ⟨⟨ℓ, rfl⟩, hU, hV⟩
    rcases heq g ℓ with ⟨ℓ', h1, h2⟩
    exact ⟨⟨ℓ', Prod.ext h1 h2⟩, hU.image _, hV.image _⟩
  -- Projected grid family `𝒢` of nonempty cocycle-valid pairs on `Fin 8 × Fin 8`.
  let 𝒢 : Finset (Finset (Fin 8) × Finset (Fin 8)) :=
    B.image fun p => (projW p.1, projZ p.2)
  have hG_coc : ∀ q ∈ 𝒢, IsNonemptyCocycleValid 3 q.1 q.2 := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨⟨U, V⟩, hUV, rfl⟩
    have ⟨hbic, hUne, hVne⟩ := hB_bic _ hUV
    have h3 := (K_coreRel_biclique_iff_three_conds 3 hUne hVne).mp hbic
    exact ⟨hUne.image _, hVne.image _, h3.2.1⟩
  -- `𝒢` covers every cell `(w, z) ∈ Fin 8 × Fin 8`.
  have hG_cov : ∀ w z : Fin 8, ∃ q ∈ 𝒢, w ∈ q.1 ∧ z ∈ q.2 := by
    intro w z
    have hrel : K_coreRel 3 (borrowVec 3 w z, w) (0, z) := by
      unfold K_coreRel; simp
    rcases C.covers _ _ hrel with ⟨ℓ, hU, hV⟩
    have hBmem : (C.U ℓ, C.V ℓ) ∈ B := by
      simp only [B, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨ℓ, rfl⟩, ⟨_, hU⟩, ⟨_, hV⟩⟩
    exact ⟨(projW (C.U ℓ), projZ (C.V ℓ)), Finset.mem_image.mpr ⟨_, hBmem, rfl⟩,
      Finset.mem_image.mpr ⟨_, hU, rfl⟩, Finset.mem_image.mpr ⟨_, hV, rfl⟩⟩
  -- Row degrees in `𝒢` are bounded by `C.rowLoad (0, w) ≤ 3`.
  have hG_row : ∀ w : Fin 8, (𝒢.filter fun q => w ∈ q.1).card ≤ 3 := by
    intro w
    let Brow := B.filter fun p => ((0 : Fin 3 → ZMod 2), w) ∈ p.1
    have himg : Brow.image (fun p => (projW p.1, projZ p.2)) = 𝒢.filter fun q => w ∈ q.1 := by
      ext ⟨W, Z⟩
      simp only [Finset.mem_image, Finset.mem_filter, Brow, 𝒢]
      constructor
      · rintro ⟨⟨U, V⟩, ⟨hUV, h0w⟩, hEq⟩
        dsimp only at h0w hEq
        have hW : projW U = W := congrArg Prod.fst hEq
        exact ⟨⟨(U, V), hUV, hEq⟩, by rw [← hW]; exact Finset.mem_image.mpr ⟨_, h0w, rfl⟩⟩
      · rintro ⟨⟨⟨U0, V0⟩, hUV0, hEq0⟩, hwW⟩
        dsimp only at hEq0
        have hW0 : projW U0 = W := congrArg Prod.fst hEq0
        have hZ0 : projZ V0 = Z := congrArg Prod.snd hEq0
        have ⟨hbic0, hU0ne, hV0ne⟩ := hB_bic _ hUV0
        dsimp only at hbic0 hU0ne hV0ne
        have hw0U : ∃ x0, (x0, w) ∈ U0 := by
          rw [← hW0] at hwW
          rcases Finset.mem_image.mp hwW with ⟨⟨x0, w'⟩, hmem, hw'⟩
          dsimp only at hw'; subst hw'; exact ⟨x0, hmem⟩
        rcases hw0U with ⟨x0, hx0w⟩
        rcases hV0ne with ⟨⟨y0, z0⟩, hy0z0⟩
        have hlift0 := biclique_eq_lift hbic0 hx0w hy0z0
        -- Shift `(U0, V0)` by `g = x0` so anchor `(x0, w)` moves to `(x0 + x0, w) = (0, w)`.
        let U1 := shiftCoreSet x0 U0
        let V1 := shiftCoreSet x0 V0
        refine ⟨(U1, V1), ⟨hB_shift x0 _ hUV0, ?_⟩, ?_⟩
        · exact Finset.mem_image.mpr ⟨(x0, w), hx0w, Prod.ext (zmod2_vec_add_self x0) rfl⟩
        · have hU1 : U1 = liftU 3 W w z0 (x0 + x0) := by
            rw [show U1 = shiftCoreSet x0 U0 from rfl, hlift0.1, hW0, shiftCoreSet_liftU]
          have hV1 : V1 = liftV 3 Z w (x0 + x0) := by
            rw [show V1 = shiftCoreSet x0 V0 from rfl, hlift0.2, hZ0, shiftCoreSet_liftV]
          exact Prod.ext (by rw [hU1, projW_liftU]) (by rw [hV1, projZ_liftV])
    have hinj : Set.InjOn (fun p : Finset ((Fin 3 → ZMod 2) × Fin 8) × Finset ((Fin 3 → ZMod 2) × Fin 8) =>
        (projW p.1, projZ p.2)) Brow := by
      intro ⟨U1, V1⟩ h1 ⟨U2, V2⟩ h2 hEq
      simp only [Finset.mem_coe, Brow, Finset.mem_filter] at h1 h2
      have hW : projW U1 = projW U2 := congrArg Prod.fst hEq
      have hZ : projZ V1 = projZ V2 := congrArg Prod.snd hEq
      have ⟨hbic1, _, hV1ne⟩ := hB_bic _ h1.1
      have ⟨hbic2, _, _⟩ := hB_bic _ h2.1
      rcases hV1ne with ⟨⟨y1, z0⟩, hy1z0⟩
      have hz0 : z0 ∈ projZ V2 := by rw [← hZ]; exact Finset.mem_image.mpr ⟨_, hy1z0, rfl⟩
      rcases Finset.mem_image.mp hz0 with ⟨⟨y2, z0'⟩, hy2z0, hz'⟩
      dsimp only at hz'; subst hz'
      have hl1 := biclique_eq_lift hbic1 h1.2 hy1z0
      have hl2 := biclique_eq_lift hbic2 h2.2 hy2z0
      exact Prod.ext (by rw [hl1.1, hl2.1, hW]) (by rw [hl1.2, hl2.2, hZ])
    rw [← himg, Finset.card_image_of_injOn hinj]
    have hsub_load : Brow ⊆ (Finset.univ.filter fun ℓ : C.L => ((0 : Fin 3 → ZMod 2), w) ∈ C.U ℓ).image
        (fun ℓ => (C.U ℓ, C.V ℓ)) := by
      intro p hp
      simp only [Brow, B, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hp ⊢
      rcases hp with ⟨⟨⟨ℓ, rfl⟩, _⟩, hmem⟩
      exact ⟨ℓ, hmem, rfl⟩
    calc Brow.card
        ≤ ((Finset.univ.filter fun ℓ : C.L => ((0 : Fin 3 → ZMod 2), w) ∈ C.U ℓ).image
            (fun ℓ => (C.U ℓ, C.V ℓ))).card := Finset.card_le_card hsub_load
      _ ≤ (Finset.univ.filter fun ℓ : C.L => ((0 : Fin 3 → ZMod 2), w) ∈ C.U ℓ).card :=
          Finset.card_image_le
      _ = C.rowLoad (0, w) := rfl
      _ ≤ 3 := hrow (0, w)
  -- Column degrees in `𝒢` are bounded by `C.colLoad (0, z) ≤ 3`.
  have hG_col : ∀ z : Fin 8, (𝒢.filter fun q => z ∈ q.2).card ≤ 3 := by
    intro z
    let Bcol := B.filter fun p => ((0 : Fin 3 → ZMod 2), z) ∈ p.2
    have himg : Bcol.image (fun p => (projW p.1, projZ p.2)) = 𝒢.filter fun q => z ∈ q.2 := by
      ext ⟨W, Z⟩
      simp only [Finset.mem_image, Finset.mem_filter, Bcol, 𝒢]
      constructor
      · rintro ⟨⟨U, V⟩, ⟨hUV, h0z⟩, hEq⟩
        dsimp only at h0z hEq
        have hZ : projZ V = Z := congrArg Prod.snd hEq
        exact ⟨⟨(U, V), hUV, hEq⟩, by rw [← hZ]; exact Finset.mem_image.mpr ⟨_, h0z, rfl⟩⟩
      · rintro ⟨⟨⟨U0, V0⟩, hUV0, hEq0⟩, hzZ⟩
        dsimp only at hEq0
        have hW0 : projW U0 = W := congrArg Prod.fst hEq0
        have hZ0 : projZ V0 = Z := congrArg Prod.snd hEq0
        have ⟨hbic0, hU0ne, _⟩ := hB_bic _ hUV0
        dsimp only at hbic0 hU0ne
        have hz0V : ∃ y0, (y0, z) ∈ V0 := by
          rw [← hZ0] at hzZ
          rcases Finset.mem_image.mp hzZ with ⟨⟨y0, z'⟩, hmem, hz'⟩
          dsimp only at hz'; subst hz'; exact ⟨y0, hmem⟩
        rcases hz0V with ⟨y0, hy0z⟩
        rcases hU0ne with ⟨⟨x0, w0⟩, hx0w0⟩
        have hlift0 := biclique_eq_lift hbic0 hx0w0 hy0z
        let U1 := shiftCoreSet y0 U0
        let V1 := shiftCoreSet y0 V0
        refine ⟨(U1, V1), ⟨hB_shift y0 _ hUV0, ?_⟩, ?_⟩
        · exact Finset.mem_image.mpr ⟨(y0, z), hy0z, Prod.ext (zmod2_vec_add_self y0) rfl⟩
        · have hU1 : U1 = liftU 3 W w0 z (x0 + y0) := by
            rw [show U1 = shiftCoreSet y0 U0 from rfl, hlift0.1, hW0, shiftCoreSet_liftU]
          have hV1 : V1 = liftV 3 Z w0 (x0 + y0) := by
            rw [show V1 = shiftCoreSet y0 V0 from rfl, hlift0.2, hZ0, shiftCoreSet_liftV]
          exact Prod.ext (by rw [hU1, projW_liftU]) (by rw [hV1, projZ_liftV])
    have hinj : Set.InjOn (fun p : Finset ((Fin 3 → ZMod 2) × Fin 8) × Finset ((Fin 3 → ZMod 2) × Fin 8) =>
        (projW p.1, projZ p.2)) Bcol := by
      intro ⟨U1, V1⟩ h1 ⟨U2, V2⟩ h2 hEq
      simp only [Finset.mem_coe, Bcol, Finset.mem_filter] at h1 h2
      have hW : projW U1 = projW U2 := congrArg Prod.fst hEq
      have hZ : projZ V1 = projZ V2 := congrArg Prod.snd hEq
      have ⟨hbic1, hU1ne, _⟩ := hB_bic _ h1.1
      have ⟨hbic2, _, _⟩ := hB_bic _ h2.1
      dsimp only at hbic1 hU1ne hbic2
      rcases hU1ne with ⟨⟨x1, w0⟩, hx1w0⟩
      have hw0 : w0 ∈ projW U2 := by rw [← hW]; exact Finset.mem_image.mpr ⟨_, hx1w0, rfl⟩
      rcases Finset.mem_image.mp hw0 with ⟨⟨x2, w0'⟩, hx2w0, hw'⟩
      dsimp only at hw'
      rw [hw'] at hx2w0
      have hx1_eq : x1 = borrowVec 3 w0 z := by
        have := hbic1 (x1, w0) hx1w0 (0, z) h1.2
        simpa [K_coreRel] using this
      have hx2_eq : x2 = borrowVec 3 w0 z := by
        have := hbic2 (x2, w0) hx2w0 (0, z) h2.2
        simpa [K_coreRel] using this
      have hl1 := biclique_eq_lift hbic1 hx1w0 h1.2
      have hl2 := biclique_eq_lift hbic2 hx2w0 h2.2
      exact Prod.ext (by rw [hl1.1, hl2.1, hW, hx1_eq, hx2_eq])
                     (by rw [hl1.2, hl2.2, hZ, hx1_eq, hx2_eq])
    rw [← himg, Finset.card_image_of_injOn hinj]
    have hsub_load : Bcol ⊆ (Finset.univ.filter fun ℓ : C.L => ((0 : Fin 3 → ZMod 2), z) ∈ C.V ℓ).image
        (fun ℓ => (C.U ℓ, C.V ℓ)) := by
      intro p hp
      simp only [Bcol, B, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hp ⊢
      rcases hp with ⟨⟨⟨ℓ, rfl⟩, _⟩, hmem⟩
      exact ⟨ℓ, hmem, rfl⟩
    calc Bcol.card
        ≤ ((Finset.univ.filter fun ℓ : C.L => ((0 : Fin 3 → ZMod 2), z) ∈ C.V ℓ).image
            (fun ℓ => (C.U ℓ, C.V ℓ))).card := Finset.card_le_card hsub_load
      _ ≤ (Finset.univ.filter fun ℓ : C.L => ((0 : Fin 3 → ZMod 2), z) ∈ C.V ℓ).card :=
          Finset.card_image_le
      _ = C.colLoad (0, z) := rfl
      _ ≤ 3 := hcol (0, z)
  -- The exact Proposition 3.3 inequality chain: `192 ≥ 4 ∑ (|W|+|Z|) ≥ 3 ∑ |W||Z| ≥ 192`.
  have hterm : ∀ q ∈ 𝒢, 3 * (q.1.card * q.2.card) ≤ 4 * (q.1.card + q.2.card) ∧
      (3 * (q.1.card * q.2.card) = 4 * (q.1.card + q.2.card) ↔
        (q.1.card = 2 ∧ q.2.card = 4) ∨ (q.1.card = 4 ∧ q.2.card = 2)) := by
    intro q hq
    have hcoc := hG_coc q hq
    rcases cocycleValid_dyadic_bound 3 hcoc.2.2 with ⟨a, ha, hW, hZ⟩
    exact dyadic_s3_area_ineq ha (Finset.card_pos.mpr hcoc.1) (Finset.card_pos.mpr hcoc.2.1) hW hZ
  have hsum_deg : ∑ q ∈ 𝒢, (q.1.card + q.2.card) =
      (∑ w : Fin 8, (𝒢.filter fun q => w ∈ q.1).card) +
      (∑ z : Fin 8, (𝒢.filter fun q => z ∈ q.2).card) := by
    rw [Finset.sum_add_distrib]
    congr 1
    · calc ∑ q ∈ 𝒢, q.1.card
          = ∑ q ∈ 𝒢, ∑ w : Fin 8, if w ∈ q.1 then 1 else 0 := by
            refine Finset.sum_congr rfl fun q _ => ?_
            rw [← Finset.card_filter]; congr 1; ext w; simp
        _ = ∑ w : Fin 8, ∑ q ∈ 𝒢, if w ∈ q.1 then 1 else 0 := Finset.sum_comm
        _ = ∑ w : Fin 8, (𝒢.filter fun q => w ∈ q.1).card := by
            refine Finset.sum_congr rfl fun w _ => (Finset.card_filter _ _).symm
    · calc ∑ q ∈ 𝒢, q.2.card
          = ∑ q ∈ 𝒢, ∑ z : Fin 8, if z ∈ q.2 then 1 else 0 := by
            refine Finset.sum_congr rfl fun q _ => ?_
            rw [← Finset.card_filter]; congr 1; ext z; simp
        _ = ∑ z : Fin 8, ∑ q ∈ 𝒢, if z ∈ q.2 then 1 else 0 := Finset.sum_comm
        _ = ∑ z : Fin 8, (𝒢.filter fun q => z ∈ q.2).card := by
            refine Finset.sum_congr rfl fun z _ => (Finset.card_filter _ _).symm
  have hsum_area : ∑ q ∈ 𝒢, q.1.card * q.2.card =
      ∑ w : Fin 8, ∑ z : Fin 8, (𝒢.filter fun q => w ∈ q.1 ∧ z ∈ q.2).card := by
    calc ∑ q ∈ 𝒢, q.1.card * q.2.card
        = ∑ q ∈ 𝒢, ∑ w : Fin 8, ∑ z : Fin 8, if w ∈ q.1 ∧ z ∈ q.2 then 1 else 0 := by
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [← Finset.card_product, ← Fintype.sum_prod_type', ← Finset.card_filter]
          congr 1; ext ⟨w, z⟩; simp
      _ = ∑ w : Fin 8, ∑ z : Fin 8, ∑ q ∈ 𝒢, if w ∈ q.1 ∧ z ∈ q.2 then 1 else 0 := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun w _ => Finset.sum_comm
      _ = ∑ w : Fin 8, ∑ z : Fin 8, (𝒢.filter fun q => w ∈ q.1 ∧ z ∈ q.2).card := by
          refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun z _ =>
            (Finset.card_filter _ _).symm
  have h192_top : 4 * (∑ q ∈ 𝒢, (q.1.card + q.2.card)) ≤ 192 := by
    rw [hsum_deg]
    have h1 : ∑ w : Fin 8, (𝒢.filter fun q => w ∈ q.1).card ≤ 24 := by
      calc ∑ w : Fin 8, (𝒢.filter fun q => w ∈ q.1).card
          ≤ ∑ _w : Fin 8, 3 := Finset.sum_le_sum fun w _ => hG_row w
        _ = 24 := by simp
    have h2 : ∑ z : Fin 8, (𝒢.filter fun q => z ∈ q.2).card ≤ 24 := by
      calc ∑ z : Fin 8, (𝒢.filter fun q => z ∈ q.2).card
          ≤ ∑ _z : Fin 8, 3 := Finset.sum_le_sum fun z _ => hG_col z
        _ = 24 := by simp
    omega
  have hmid : 3 * (∑ q ∈ 𝒢, q.1.card * q.2.card) ≤ 4 * (∑ q ∈ 𝒢, (q.1.card + q.2.card)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun q hq => (hterm q hq).1
  have hcov_ge1 : ∀ w z : Fin 8, 1 ≤ (𝒢.filter fun q => w ∈ q.1 ∧ z ∈ q.2).card := by
    intro w z
    rcases hG_cov w z with ⟨q, hq, hw, hz⟩
    exact Finset.card_pos.mpr ⟨q, Finset.mem_filter.mpr ⟨hq, hw, hz⟩⟩
  have h192_bot : 192 ≤ 3 * (∑ q ∈ 𝒢, q.1.card * q.2.card) := by
    rw [hsum_area]
    have h64 : 64 ≤ ∑ w : Fin 8, ∑ z : Fin 8, (𝒢.filter fun q => w ∈ q.1 ∧ z ∈ q.2).card := by
      calc 64 = ∑ _w : Fin 8, ∑ _z : Fin 8, 1 := by simp
        _ ≤ ∑ w : Fin 8, ∑ z : Fin 8, (𝒢.filter fun q => w ∈ q.1 ∧ z ∈ q.2).card :=
          Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun z _ => hcov_ge1 w z
    omega
  -- Equality throughout forces every `q ∈ 𝒢` to have shape `(2, 4)`/`(4, 2)` and every cell to be covered once!
  have heq_mid : ∑ q ∈ 𝒢, 3 * (q.1.card * q.2.card) = ∑ q ∈ 𝒢, 4 * (q.1.card + q.2.card) := by
    rw [← Finset.mul_sum, ← Finset.mul_sum]; omega
  have heach_shape : ∀ q ∈ 𝒢, (q.1.card = 2 ∧ q.2.card = 4) ∨ (q.1.card = 4 ∧ q.2.card = 2) := by
    intro q hq
    have heq_q : 3 * (q.1.card * q.2.card) = 4 * (q.1.card + q.2.card) := by
      by_contra hne
      have hlt : 3 * (q.1.card * q.2.card) < 4 * (q.1.card + q.2.card) :=
        lt_of_le_of_ne (hterm q hq).1 hne
      have hstrict := Finset.sum_lt_sum (fun x hx => (hterm x hx).1) ⟨q, hq, hlt⟩
      omega
    exact (hterm q hq).2.mp heq_q
  have hcell_eq1 : ∀ w z : Fin 8, (𝒢.filter fun q => w ∈ q.1 ∧ z ∈ q.2).card = 1 := by
    have h64_eq : ∑ w : Fin 8, ∑ z : Fin 8, (𝒢.filter fun q => w ∈ q.1 ∧ z ∈ q.2).card = 64 := by
      rw [← hsum_area]; omega
    intro w z
    by_contra hne
    have hgt : 1 < (𝒢.filter fun q => w ∈ q.1 ∧ z ∈ q.2).card :=
      lt_of_le_of_ne (hcov_ge1 w z) (Ne.symm hne)
    have hstrict_row : ∑ _z : Fin 8, 1 < ∑ z' : Fin 8, (𝒢.filter fun q => w ∈ q.1 ∧ z' ∈ q.2).card :=
      Finset.sum_lt_sum (fun z' _ => hcov_ge1 w z') ⟨z, Finset.mem_univ z, hgt⟩
    have hstrict_all : ∑ _w : Fin 8, ∑ _z : Fin 8, 1 <
        ∑ w' : Fin 8, ∑ z' : Fin 8, (𝒢.filter fun q => w' ∈ q.1 ∧ z' ∈ q.2).card :=
      Finset.sum_lt_sum (fun w' _ => Finset.sum_le_sum fun z' _ => hcov_ge1 w' z')
        ⟨w, Finset.mem_univ w, hstrict_row⟩
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hstrict_all
    omega
  -- Transport `𝒢` to `Mask8 × Mask8` and contradict Proposition A.1!
  let Gm : Finset (Mask8 × Mask8) := 𝒢.image fun q => (Mask8.ofFinset q.1, Mask8.ofFinset q.2)
  have hinj_mask : Function.Injective (fun q : Finset (Fin 8) × Finset (Fin 8) =>
      (Mask8.ofFinset q.1, Mask8.ofFinset q.2)) := by
    intro q1 q2 h
    have h1 := congrArg (fun p : Mask8 × Mask8 => p.1.toFinset) h
    have h2 := congrArg (fun p : Mask8 × Mask8 => p.2.toFinset) h
    simp only [Mask8.toFinset_ofFinset] at h1 h2
    exact Prod.ext h1 h2
  have hGm_tiling : IsGridTiling Gm := by
    constructor
    · intro r hr
      rcases Finset.mem_image.mp hr with ⟨q, hq, rfl⟩
      exact (mem_rects48_iff_cocycle_shape q.1 q.2).mpr ⟨(hG_coc q hq).2.2, heach_shape q hq⟩
    · intro w z
      rcases Finset.card_eq_one.mp (hcell_eq1 w z) with ⟨q0, hq0⟩
      have hq0_mem : q0 ∈ 𝒢 ∧ w ∈ q0.1 ∧ z ∈ q0.2 := by
        have : q0 ∈ 𝒢.filter fun q => w ∈ q.1 ∧ z ∈ q.2 := by rw [hq0]; simp
        exact Finset.mem_filter.mp this
      refine ⟨(Mask8.ofFinset q0.1, Mask8.ofFinset q0.2),
        ⟨Finset.mem_image.mpr ⟨q0, hq0_mem.1, rfl⟩,
         by simp [Mask8.get_ofFinset, hq0_mem.2.1],
         by simp [Mask8.get_ofFinset, hq0_mem.2.2]⟩, ?_⟩
      rintro r ⟨hr, hrw, hrz⟩
      rcases Finset.mem_image.mp hr with ⟨q, hq, rfl⟩
      simp only [Mask8.get_ofFinset, decide_eq_true_eq] at hrw hrz
      have : q ∈ 𝒢.filter fun q => w ∈ q.1 ∧ z ∈ q.2 := Finset.mem_filter.mpr ⟨hq, hrw, hrz⟩
      rw [hq0, Finset.mem_singleton] at this
      rw [this]
  have hGm_row : ∀ w : Fin 8, (Gm.filter fun r => r.1.get w = true).card ≤ 3 := by
    intro w
    have hfilt : (Gm.filter fun r => r.1.get w = true) =
        (𝒢.filter fun q => w ∈ q.1).image fun q => (Mask8.ofFinset q.1, Mask8.ofFinset q.2) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_image, Gm]
      constructor
      · rintro ⟨⟨q, hq, rfl⟩, hw⟩
        exact ⟨q, ⟨hq, by simpa [Mask8.get_ofFinset] using hw⟩, rfl⟩
      · rintro ⟨q, ⟨hq, hw⟩, rfl⟩
        exact ⟨⟨q, hq, rfl⟩, by simp [Mask8.get_ofFinset, hw]⟩
    rw [hfilt, Finset.card_image_of_injective _ hinj_mask]
    exact hG_row w
  have hGm_col : ∀ z : Fin 8, (Gm.filter fun r => r.2.get z = true).card ≤ 3 := by
    intro z
    have hfilt : (Gm.filter fun r => r.2.get z = true) =
        (𝒢.filter fun q => z ∈ q.2).image fun q => (Mask8.ofFinset q.1, Mask8.ofFinset q.2) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_image, Gm]
      constructor
      · rintro ⟨⟨q, hq, rfl⟩, hz⟩
        exact ⟨q, ⟨hq, by simpa [Mask8.get_ofFinset] using hz⟩, rfl⟩
      · rintro ⟨q, ⟨hq, hz⟩, rfl⟩
        exact ⟨⟨q, hq, rfl⟩, by simp [Mask8.get_ofFinset, hz]⟩
    rw [hfilt, Finset.card_image_of_injective _ hinj_mask]
    exact hG_col z
  exact prop_A1_s3_grid_obstruction.2 Gm hGm_tiling ⟨hGm_row, hGm_col⟩

end CarryAutomaton
