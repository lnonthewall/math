module

public import CarryAutomaton.Defs
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Log
import Mathlib.Tactic

@[expose] public section

/-!
# Core Factorization and Maximal Biclique Classification (`CarryAutomaton.CoreBicliques`)

Formalization of Section 1 and Theorem 2.1 of the Paper 2 manuscript (where the borrow-core
matrix `C_t` in Paper 2 is formalized as `K_coreRel s` / `K_coreMat R s` with `s = t - 1`):
1. Biregularity of `M_t`, single-valued exact cover at `t = 1`, and the `2 × 2` triangular
   obstruction ruling out exact single-valued covers for all `t ≥ 2`.
2. Theorem 2.1(a): Exact Kronecker core factorization `M_t ≅ I_2 ⊗ K_t ⊗ J_2`,
   `2^s`-biregularity of `K_t`, `K_1 = (1)`, and `K_2 ≅ C_8`.
3. Theorem 2.1(b): Anchor-compatible lifting equivalence, irredundancy of anchor compatibility
   at `s = 1`, exact `2^s`-to-1 lift correspondence, and coincidence of lifted and projected
   maximality.
4. Theorem 2.1(c): Complete `4^s` inductive classification of maximal cocycle-valid pairs,
   exact shape counts `2^s * C(s, a)` and shape generating function `(2X + 2Y)^s`,
   `8^s` core maximal bicliques (`2 * 8^s` in `M_t`), and exact maximum biclique areas
   `A_max(K_t) = 2^s` and `A_max(M_t) = 2^(s+2)`.
-/

namespace CarryAutomaton

open Finset BigOperators

/-! ### Section 1: Biregularity and Single-Valued Obstruction for `M_t` -/

lemma M_rel_iff_eq_sub {t : ℕ} (r c : Fin (2 ^ t) × Fin (2 ^ t)) :
    M_rel t r c ↔ (r.1.val ^^^ c.1.val) = (c.2.val + (2 ^ t - r.2.val)) % 2 ^ t := by
  unfold M_rel
  have h1 : r.1.val ^^^ c.1.val < 2 ^ t := Nat.xor_lt_two_pow r.1.isLt c.1.isLt
  have h2 : r.2.val < 2 ^ t := r.2.isLt
  have h3 : c.2.val < 2 ^ t := c.2.isLt
  constructor
  · intro h
    have hmod : ((r.1.val ^^^ c.1.val) + r.2.val + (2 ^ t - r.2.val)) % 2 ^ t =
        (c.2.val + (2 ^ t - r.2.val)) % 2 ^ t := by
      rw [Nat.add_mod, h, Nat.add_mod_mod]
    have hadd : (r.1.val ^^^ c.1.val) + r.2.val + (2 ^ t - r.2.val) =
        (r.1.val ^^^ c.1.val) + 2 ^ t := by omega
    rw [hadd, Nat.add_mod_right, Nat.mod_eq_of_lt h1] at hmod
    exact hmod
  · intro h
    rw [h]
    have hmod : ((c.2.val + (2 ^ t - r.2.val)) % 2 ^ t + r.2.val) % 2 ^ t =
        (c.2.val + (2 ^ t - r.2.val) + r.2.val) % 2 ^ t := by
      rw [Nat.mod_add_mod]
    rw [hmod]
    have hadd : c.2.val + (2 ^ t - r.2.val) + r.2.val = c.2.val + 2 ^ t := by omega
    rw [hadd, Nat.add_mod_right, Nat.mod_eq_of_lt h3]

theorem M_rel_row_card (t : ℕ) (r : Fin (2 ^ t) × Fin (2 ^ t)) :
    (Finset.univ.filter fun c => M_rel t r c).card = 2 ^ t := by
  have hcard : (Finset.univ.filter fun c => M_rel t r c).card =
      (Finset.univ : Finset (Fin (2 ^ t))).card := by
    refine Finset.card_bij
      (fun c _ => c.1)
      (fun _ _ => Finset.mem_univ _)
      (fun c1 hc1 c2 hc2 h => ?_)
      (fun v _ => ?_)
    · rw [Finset.mem_filter] at hc1 hc2
      have h1 : ((r.1.val ^^^ c1.1.val) + r.2.val) % 2 ^ t = c1.2.val := hc1.2
      have h2 : ((r.1.val ^^^ c2.1.val) + r.2.val) % 2 ^ t = c2.2.val := hc2.2
      apply Prod.ext h
      apply Fin.ext
      rw [← h1, ← h2, h]
    · refine ⟨(v, ⟨((r.1.val ^^^ v.val) + r.2.val) % 2 ^ t, Nat.mod_lt _ (by positivity)⟩),
        ?_, rfl⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, rfl⟩
  simpa using hcard

theorem M_rel_col_card (t : ℕ) (c : Fin (2 ^ t) × Fin (2 ^ t)) :
    (Finset.univ.filter fun r => M_rel t r c).card = 2 ^ t := by
  have hcard : (Finset.univ.filter fun r => M_rel t r c).card =
      (Finset.univ : Finset (Fin (2 ^ t))).card := by
    refine Finset.card_bij
      (fun r _ => r.2)
      (fun _ _ => Finset.mem_univ _)
      (fun r1 hr1 r2 hr2 h => ?_)
      (fun w _ => ?_)
    · rw [Finset.mem_filter] at hr1 hr2
      have h1 := (M_rel_iff_eq_sub r1 c).mp hr1.2
      have h2 := (M_rel_iff_eq_sub r2 c).mp hr2.2
      apply Prod.ext _ h
      apply Fin.ext
      have hxor : r1.1.val ^^^ c.1.val = r2.1.val ^^^ c.1.val := by
        rw [h1, h2, h]
      have := congrArg (· ^^^ c.1.val) hxor
      simpa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] using this
    · let d := (c.2.val + (2 ^ t - w.val)) % 2 ^ t
      have hd : d < 2 ^ t := Nat.mod_lt _ (by positivity)
      let u : Fin (2 ^ t) := ⟨d ^^^ c.1.val, Nat.xor_lt_two_pow hd c.1.isLt⟩
      refine ⟨(u, w), ?_, rfl⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, (M_rel_iff_eq_sub (u, w) c).mpr ?_⟩
      change (d ^^^ c.1.val) ^^^ c.1.val = d
      simp [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  simpa using hcard

theorem M_rel_edge_card (t : ℕ) :
    (Finset.univ.filter fun p : (Fin (2 ^ t) × Fin (2 ^ t)) × (Fin (2 ^ t) × Fin (2 ^ t)) =>
      M_rel t p.1 p.2).card = 2 ^ (3 * t) := by
  have h1 : (Finset.univ.filter fun p : (Fin (2 ^ t) × Fin (2 ^ t)) × (Fin (2 ^ t) × Fin (2 ^ t)) =>
      M_rel t p.1 p.2).card =
      ∑ r : Fin (2 ^ t) × Fin (2 ^ t), (Finset.univ.filter fun c => M_rel t r c).card := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.card_filter]
  rw [h1]
  simp only [M_rel_row_card, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, smul_eq_mul]
  calc 2 ^ t * 2 ^ t * 2 ^ t = 2 ^ (t + t + t) := by rw [← pow_add, ← pow_add]
    _ = 2 ^ (3 * t) := by ring_nf

/-- At `t = 1`, `M_1` admits an exact single-valued factorization over `Fin 2`. -/
theorem M_rel_one_single_valued :
    ∃ fA fB : Fin (2 ^ 1) × Fin (2 ^ 1) → Fin 2,
      ∀ r c, M_rel 1 r c ↔ fA r = fB c := by
  refine ⟨fun r => ⟨(r.1.val ^^^ r.2.val) % 2, Nat.mod_lt _ (by omega)⟩,
          fun c => ⟨(c.1.val ^^^ c.2.val) % 2, Nat.mod_lt _ (by omega)⟩, ?_⟩
  intro ⟨u, w⟩ ⟨v, z⟩
  fin_cases u <;> fin_cases w <;> fin_cases v <;> fin_cases z <;> decide

/-- For every `t ≥ 2`, restricting `M_t` to `{(0, 0), (1, 1)}` yields `[[1, 1], [0, 1]]`. -/
theorem M_rel_two_by_two_obstruction {t : ℕ} (ht : 2 ≤ t) :
    let h0 : 0 < 2 ^ t := by positivity
    let h1 : 1 < 2 ^ t := by
      have : 4 ≤ 2 ^ t := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ t := Nat.pow_le_pow_right (by omega) ht
      omega
    let p0 : Fin (2 ^ t) × Fin (2 ^ t) := (⟨0, h0⟩, ⟨0, h0⟩)
    let p1 : Fin (2 ^ t) × Fin (2 ^ t) := (⟨1, h1⟩, ⟨1, h1⟩)
    M_rel t p0 p0 ∧ M_rel t p0 p1 ∧ ¬ M_rel t p1 p0 ∧ M_rel t p1 p1 := by
  have h2t : 4 ≤ 2 ^ t := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ t := Nat.pow_le_pow_right (by omega) ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [M_rel]
  · simp [M_rel, Nat.mod_eq_of_lt (by omega : 1 < 2 ^ t)]
  · simp only [M_rel, Nat.xor_zero]
    rw [Nat.mod_eq_of_lt (by omega : 1 + 1 < 2 ^ t)]
    omega
  · simp [M_rel, Nat.mod_eq_of_lt (by omega : 1 < 2 ^ t)]

/-- For every `t ≥ 2`, `M_t` admits NO exact single-valued label factorization. -/
theorem M_rel_no_single_valued {t : ℕ} (ht : 2 ≤ t) (L : Type*)
    (fA fB : Fin (2 ^ t) × Fin (2 ^ t) → L) :
    ¬ (∀ r c, M_rel t r c ↔ fA r = fB c) := by
  intro h
  have hobs := M_rel_two_by_two_obstruction ht
  rcases hobs with ⟨h00, h01, h10, h11⟩
  have e00 := (h _ _).mp h00
  have e01 := (h _ _).mp h01
  have e11 := (h _ _).mp h11
  have e10 : fA _ = fB _ := e11.trans (e01.symm.trans e00)
  exact h10 ((h _ _).mpr e10)

/-! ### Bitwise Carry-Borrow Arithmetic Foundation -/

/-- Fundamental binary addition carry-borrow identity:
if `w, z, d < 2^t` satisfy `(d + w) % 2^t = z`, then for every `i < t`,
bit `i` of `z` equals `d_i ⊕ w_i ⊕ 1[(w mod 2^i) > (z mod 2^i)]`. -/
lemma testBit_add_mod_two_pow {t w z d i : ℕ}
    (hadd : (d + w) % 2 ^ t = z) (hi : i < t) :
    z.testBit i = (d.testBit i ^^ w.testBit i ^^ decide (z % 2 ^ i < w % 2 ^ i)) := by
  have hpow_pos : 0 < 2 ^ i := by positivity
  have hdvd : 2 ^ (i + 1) ∣ 2 ^ t := Nat.pow_dvd_pow 2 (by omega)
  have hdvd_i : 2 ^ i ∣ 2 ^ t := Nat.pow_dvd_pow 2 (by omega)
  have hmod_ip1 : (d + w) % 2 ^ (i + 1) = z % 2 ^ (i + 1) := by
    rw [← hadd, Nat.mod_mod_of_dvd _ hdvd]
  have hmod_i : (d + w) % 2 ^ i = z % 2 ^ i := by
    rw [← hadd, Nat.mod_mod_of_dvd _ hdvd_i]
  have hcarry : (d % 2 ^ i + w % 2 ^ i) / 2 ^ i = if z % 2 ^ i < w % 2 ^ i then 1 else 0 := by
    have hdm : d % 2 ^ i < 2 ^ i := Nat.mod_lt _ hpow_pos
    have hwm : w % 2 ^ i < 2 ^ i := Nat.mod_lt _ hpow_pos
    have hsum_mod : (d % 2 ^ i + w % 2 ^ i) % 2 ^ i = z % 2 ^ i := by
      rw [← Nat.add_mod, hmod_i]
    by_cases hlt : d % 2 ^ i + w % 2 ^ i < 2 ^ i
    · have hzeq : z % 2 ^ i = d % 2 ^ i + w % 2 ^ i := by
        rw [← hsum_mod, Nat.mod_eq_of_lt hlt]
      have hnot : ¬ (z % 2 ^ i < w % 2 ^ i) := by omega
      simp [hnot, Nat.div_eq_of_lt hlt]
    · have hge : 2 ^ i ≤ d % 2 ^ i + w % 2 ^ i := by omega
      have hzeq : z % 2 ^ i = d % 2 ^ i + w % 2 ^ i - 2 ^ i := by
        rw [← hsum_mod]
        have hsub : d % 2 ^ i + w % 2 ^ i = (d % 2 ^ i + w % 2 ^ i - 2 ^ i) + 2 ^ i := by omega
        conv_lhs => rw [hsub]
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have hlt_zw : z % 2 ^ i < w % 2 ^ i := by omega
      simp only [hlt_zw, ↓reduceIte]
      have hsub : d % 2 ^ i + w % 2 ^ i = (d % 2 ^ i + w % 2 ^ i - 2 ^ i) + 1 * 2 ^ i := by omega
      rw [hsub, Nat.add_mul_div_right _ _ hpow_pos, Nat.div_eq_of_lt (by omega), zero_add]
  have hdiv_add : (d + w) / 2 ^ i = d / 2 ^ i + w / 2 ^ i + (d % 2 ^ i + w % 2 ^ i) / 2 ^ i := by
    have hd_eq := Nat.div_add_mod d (2 ^ i)
    have hw_eq := Nat.div_add_mod w (2 ^ i)
    have hr_eq := Nat.div_add_mod (d % 2 ^ i + w % 2 ^ i) (2 ^ i)
    have hrem_lt : (d % 2 ^ i + w % 2 ^ i) % 2 ^ i < 2 ^ i := Nat.mod_lt _ hpow_pos
    have htot : d + w = 2 ^ i * (d / 2 ^ i + w / 2 ^ i + (d % 2 ^ i + w % 2 ^ i) / 2 ^ i) +
        (d % 2 ^ i + w % 2 ^ i) % 2 ^ i := by
      have : 2 ^ i * (d / 2 ^ i + w / 2 ^ i + (d % 2 ^ i + w % 2 ^ i) / 2 ^ i) =
          2 ^ i * (d / 2 ^ i) + 2 ^ i * (w / 2 ^ i) +
          2 ^ i * ((d % 2 ^ i + w % 2 ^ i) / 2 ^ i) := by ring
      omega
    rw [htot, Nat.mul_add_div hpow_pos, Nat.div_eq_of_lt hrem_lt, Nat.add_zero]
  have hdiv_mod2 : ((d + w) / 2 ^ i) % 2 = (z / 2 ^ i) % 2 := by
    have h1 : ((d + w) % 2 ^ (i + 1)) / 2 ^ i = ((d + w) / 2 ^ i) % 2 := by
      rw [pow_succ', Nat.mod_mul_left_div_self]
    have h2 : (z % 2 ^ (i + 1)) / 2 ^ i = (z / 2 ^ i) % 2 := by
      rw [pow_succ', Nat.mod_mul_left_div_self]
    rw [← h1, ← h2, hmod_ip1]
  rw [hdiv_add, hcarry] at hdiv_mod2
  simp only [Nat.testBit_eq_decide_div_mod_eq]
  have hmod_sum : ∀ a b c : ℕ, (a + b + c) % 2 = (a % 2 + b % 2 + c % 2) % 2 := by
    intro a b c; omega
  rw [hmod_sum] at hdiv_mod2
  generalize ha : d / 2 ^ i % 2 = a at hdiv_mod2 ⊢
  generalize hb : w / 2 ^ i % 2 = b at hdiv_mod2 ⊢
  generalize hc : z / 2 ^ i % 2 = c at hdiv_mod2 ⊢
  have ha2 : a < 2 := ha ▸ Nat.mod_lt _ (by omega)
  have hb2 : b < 2 := hb ▸ Nat.mod_lt _ (by omega)
  have hc2 : c < 2 := hc ▸ Nat.mod_lt _ (by omega)
  by_cases hlt : z % 2 ^ i < w % 2 ^ i
  · simp only [hlt, ↓reduceIte, decide_true] at hdiv_mod2 ⊢
    interval_cases a <;> interval_cases b <;> interval_cases c <;> simp_all
  · simp only [hlt, ↓reduceIte, decide_false] at hdiv_mod2 ⊢
    interval_cases a <;> interval_cases b <;> interval_cases c <;> simp_all

/-- Bitwise equivalence for `M_rel t`:
`M_rel t (u, w) (v, z)` holds iff at every bit `i < t`,
`(u ⊕ w)_i ⊕ (v ⊕ z)_i = 1[(w mod 2^i) > (z mod 2^i)]`. -/
lemma M_rel_iff_testBit {t : ℕ} (r c : Fin (2 ^ t) × Fin (2 ^ t)) :
    M_rel t r c ↔
      ∀ i < t, (r.1.val ^^^ r.2.val).testBit i ^^ (c.1.val ^^^ c.2.val).testBit i =
        decide (c.2.val % 2 ^ i < r.2.val % 2 ^ i) := by
  let d := (c.2.val + (2 ^ t - r.2.val)) % 2 ^ t
  have hd : d < 2 ^ t := Nat.mod_lt _ (by positivity)
  have hadd : (d + r.2.val) % 2 ^ t = c.2.val := by
    have hmod : ((c.2.val + (2 ^ t - r.2.val)) % 2 ^ t + r.2.val) % 2 ^ t =
        (c.2.val + (2 ^ t - r.2.val) + r.2.val) % 2 ^ t := by
      rw [Nat.mod_add_mod]
    have h2 : r.2.val < 2 ^ t := r.2.isLt
    rw [show d = (c.2.val + (2 ^ t - r.2.val)) % 2 ^ t from rfl, hmod]
    rw [show c.2.val + (2 ^ t - r.2.val) + r.2.val = c.2.val + 2 ^ t by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt c.2.isLt]
  have hd_bit : ∀ i < t, d.testBit i =
      (r.2.val.testBit i ^^ c.2.val.testBit i ^^ decide (c.2.val % 2 ^ i < r.2.val % 2 ^ i)) := by
    intro i hi
    have hz := testBit_add_mod_two_pow hadd hi
    revert hz
    generalize d.testBit i = bd
    generalize r.2.val.testBit i = bw
    generalize c.2.val.testBit i = bz
    generalize decide (c.2.val % 2 ^ i < r.2.val % 2 ^ i) = bc
    cases bd <;> cases bw <;> cases bz <;> cases bc <;> decide
  rw [M_rel_iff_eq_sub]
  change r.1.val ^^^ c.1.val = d ↔ _
  have huv : r.1.val ^^^ c.1.val < 2 ^ t := Nat.xor_lt_two_pow r.1.isLt c.1.isLt
  constructor
  · intro heq i hi
    have htb : (r.1.val ^^^ c.1.val).testBit i = d.testBit i := by rw [heq]
    rw [hd_bit i hi, Nat.testBit_xor] at htb
    rw [Nat.testBit_xor, Nat.testBit_xor]
    revert htb
    generalize r.1.val.testBit i = bu
    generalize r.2.val.testBit i = bw
    generalize c.1.val.testBit i = bv
    generalize c.2.val.testBit i = bz
    generalize decide (c.2.val % 2 ^ i < r.2.val % 2 ^ i) = bc
    cases bu <;> cases bw <;> cases bv <;> cases bz <;> cases bc <;> decide
  · intro hall
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < t
    · have h := hall i hi
      rw [Nat.testBit_xor, Nat.testBit_xor] at h
      rw [Nat.testBit_xor, hd_bit i hi]
      revert h
      generalize r.1.val.testBit i = bu
      generalize r.2.val.testBit i = bw
      generalize c.1.val.testBit i = bv
      generalize c.2.val.testBit i = bz
      generalize decide (c.2.val % 2 ^ i < r.2.val % 2 ^ i) = bc
      cases bu <;> cases bw <;> cases bv <;> cases bz <;> cases bc <;> decide
    · have hge : t ≤ i := by omega
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le huv (Nat.pow_le_pow_right (by omega) hge)),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hd (Nat.pow_le_pow_right (by omega) hge))]

/-! ### Theorem 2.1(a): Exact Core Factorization `M_t ≅ I_2 ⊗ K_t ⊗ J_2` -/

/-- Convert a binary vector `v : Fin s → ZMod 2` to its natural number in `[0, 2^s)`. -/
def vecToNat {s : ℕ} (v : Fin s → ZMod 2) : ℕ :=
  ∑ i : Fin s, (v i).val * 2 ^ i.val

lemma zmod2_val_lt (x : ZMod 2) : x.val < 2 := x.val_lt

lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> rfl

lemma zmod2_vec_add_self {s : ℕ} (v : Fin s → ZMod 2) : v + v = 0 := by
  funext i; exact zmod2_add_self (v i)

lemma zmod2_vec_add_eq_iff {s : ℕ} (a b c : Fin s → ZMod 2) :
    a + b = c ↔ b = a + c := by
  constructor
  · intro h
    calc b = 0 + b := (zero_add b).symm
      _ = (a + a) + b := by rw [zmod2_vec_add_self]
      _ = a + (a + b) := add_assoc a a b
      _ = a + c := by rw [h]
  · intro h
    rw [h, ← add_assoc, zmod2_vec_add_self, zero_add]

lemma zmod2_vec_add_eq_iff_left {s : ℕ} (a b c : Fin s → ZMod 2) :
    a + b = c ↔ a = b + c := by
  rw [add_comm a b, zmod2_vec_add_eq_iff]

lemma vecToNat_lt {s : ℕ} (v : Fin s → ZMod 2) : vecToNat v < 2 ^ s := by
  induction s with
  | zero => simp [vecToNat]
  | succ s ih =>
    unfold vecToNat
    rw [Fin.sum_univ_castSucc]
    have h1 : ∑ i : Fin s, (v i.castSucc).val * 2 ^ i.val < 2 ^ s :=
      ih (fun i => v i.castSucc)
    have h2 : (v (Fin.last s)).val ≤ 1 := by
      have := zmod2_val_lt (v (Fin.last s)); omega
    have h3 : (v (Fin.last s)).val * 2 ^ s ≤ 2 ^ s := by
      calc (v (Fin.last s)).val * 2 ^ s ≤ 1 * 2 ^ s := Nat.mul_le_mul_right _ h2
        _ = 2 ^ s := one_mul _
    have hpow : 2 ^ (s + 1) = 2 ^ s + 2 ^ s := by ring
    simp only [Fin.val_castSucc, Fin.val_last]
    omega

lemma testBit_vecToNat {s : ℕ} (v : Fin s → ZMod 2) (i : Fin s) :
    (vecToNat v).testBit i.val = decide (v i = 1) := by
  induction s with
  | zero => exact Fin.elim0 i
  | succ s ih =>
    unfold vecToNat
    rw [Fin.sum_univ_castSucc]
    have hlow : ∑ j : Fin s, (v j.castSucc).val * 2 ^ j.val < 2 ^ s :=
      vecToNat_lt (fun j => v j.castSucc)
    have hhi_val : (v (Fin.last s)).val < 2 := zmod2_val_lt _
    refine Fin.lastCases ?_ ?_ i
    · simp only [Fin.val_castSucc, Fin.val_last, Nat.testBit_eq_decide_div_mod_eq]
      have hdiv : (∑ j : Fin s, (v j.castSucc).val * 2 ^ j.val +
          (v (Fin.last s)).val * 2 ^ s) / 2 ^ s = (v (Fin.last s)).val := by
        rw [Nat.add_mul_div_right _ _ (by positivity : 0 < 2 ^ s), Nat.div_eq_of_lt hlow, zero_add]
      rw [hdiv, Nat.mod_eq_of_lt hhi_val]
      generalize v (Fin.last s) = x
      fin_cases x <;> rfl
    · intro j
      have hj : j.val < s := j.isLt
      have hlow_tb := ih (fun k => v k.castSucc) j
      simp only [vecToNat, Fin.val_castSucc, Fin.val_last, Nat.testBit_eq_decide_div_mod_eq] at hlow_tb ⊢
      have hpow_split : 2 ^ s = 2 ^ j.val * (2 * 2 ^ (s - j.val - 1)) := by
        rw [← pow_succ', ← pow_add]
        congr 1; omega
      have hdiv : (∑ k : Fin s, (v k.castSucc).val * 2 ^ k.val +
          (v (Fin.last s)).val * 2 ^ s) / 2 ^ j.val =
          (∑ k : Fin s, (v k.castSucc).val * 2 ^ k.val) / 2 ^ j.val +
          2 * ((v (Fin.last s)).val * 2 ^ (s - j.val - 1)) := by
        rw [show (v (Fin.last s)).val * 2 ^ s =
          (2 * ((v (Fin.last s)).val * 2 ^ (s - j.val - 1))) * 2 ^ j.val by rw [hpow_split]; ring]
        rw [Nat.add_mul_div_right _ _ (by positivity : 0 < 2 ^ j.val)]
      rw [hdiv, Nat.add_mul_mod_self_left]
      exact hlow_tb

lemma natToVec_vecToNat {s : ℕ} (v : Fin s → ZMod 2) :
    (fun i : Fin s => (if (vecToNat v).testBit i.val then (1 : ZMod 2) else 0)) = v := by
  funext i
  rw [testBit_vecToNat]
  generalize v i = x
  fin_cases x <;> rfl

lemma vecToNat_natToVec {s : ℕ} (n : ℕ) (hn : n < 2 ^ s) :
    vecToNat (fun i : Fin s => if n.testBit i.val then (1 : ZMod 2) else 0) = n := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < s
  · rw [testBit_vecToNat _ ⟨k, hk⟩]
    cases n.testBit k <;> decide
  · have hge : s ≤ k := by omega
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (vecToNat_lt _) (Nat.pow_le_pow_right (by omega) hge)),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by omega) hge))]

/-- Local affine-XOR coordinate bijection
`(u, w) ↦ (x_0, (x', w'), w_{t-1})` with `x = u ⊕ w`, used identically on rows and columns. -/
def phi_coord (s : ℕ) :
    Fin (2 ^ (s + 1)) × Fin (2 ^ (s + 1)) ≃
      Fin 2 × ((Fin s → ZMod 2) × Fin (2 ^ s)) × Fin 2 where
  toFun p :=
    let x := p.1.val ^^^ p.2.val
    ( ⟨x % 2, Nat.mod_lt _ (by omega)⟩,
      ( (fun i : Fin s => if x.testBit (i.val + 1) then (1 : ZMod 2) else 0),
        ⟨p.2.val % 2 ^ s, Nat.mod_lt _ (by positivity)⟩ ),
      ⟨p.2.val / 2 ^ s, by
        have h : p.2.val < 2 ^ s * 2 := by
          simpa [pow_succ] using p.2.isLt
        exact Nat.div_lt_of_lt_mul (by linarith)⟩ )
  invFun q :=
    let w_val := q.2.1.2.val + q.2.2.val * 2 ^ s
    have hw : w_val < 2 ^ (s + 1) := by
      have h1 := q.2.1.2.isLt
      have h2 : q.2.2.val ≤ 1 := by have := q.2.2.isLt; omega
      have h3 : q.2.2.val * 2 ^ s ≤ 2 ^ s := by
        calc q.2.2.val * 2 ^ s ≤ 1 * 2 ^ s := Nat.mul_le_mul_right _ h2
          _ = 2 ^ s := one_mul _
      have hpow : 2 ^ (s + 1) = 2 ^ s + 2 ^ s := by ring
      omega
    let x_val := q.1.val + 2 * vecToNat q.2.1.1
    have hx : x_val < 2 ^ (s + 1) := by
      have h1 := q.1.isLt
      have h2 := vecToNat_lt q.2.1.1
      have hpow : 2 ^ (s + 1) = 2 * 2 ^ s := by ring
      omega
    ( ⟨x_val ^^^ w_val, Nat.xor_lt_two_pow hx hw⟩, ⟨w_val, hw⟩ )
  left_inv p := by
    rcases p with ⟨u, w⟩
    have hw_eq : w.val % 2 ^ s + w.val / 2 ^ s * 2 ^ s = w.val := by
      rw [mul_comm, add_comm]; exact Nat.div_add_mod w.val (2 ^ s)
    have hx_lt : u.val ^^^ w.val < 2 ^ (s + 1) := Nat.xor_lt_two_pow u.isLt w.isLt
    have hx_div_lt : (u.val ^^^ w.val) / 2 < 2 ^ s := by
      have hpow : 2 ^ (s + 1) = 2 * 2 ^ s := by ring
      omega
    have hx_vec : vecToNat (fun i : Fin s =>
        if (u.val ^^^ w.val).testBit (i.val + 1) then (1 : ZMod 2) else 0) =
        (u.val ^^^ w.val) / 2 := by
      have hfun : (fun i : Fin s =>
          if (u.val ^^^ w.val).testBit (i.val + 1) then (1 : ZMod 2) else 0) =
          (fun i : Fin s =>
          if ((u.val ^^^ w.val) / 2).testBit i.val then (1 : ZMod 2) else 0) := by
        funext i
        rw [Nat.testBit_succ]
      rw [hfun]
      exact vecToNat_natToVec _ hx_div_lt
    have hx_eq : (u.val ^^^ w.val) % 2 + 2 * ((u.val ^^^ w.val) / 2) = u.val ^^^ w.val := by
      rw [add_comm]; exact Nat.div_add_mod (u.val ^^^ w.val) 2
    apply Prod.ext
    · apply Fin.ext
      dsimp only
      rw [hw_eq, hx_vec, hx_eq]
      simp [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    · apply Fin.ext
      exact hw_eq
  right_inv q := by
    rcases q with ⟨x0, ⟨x', w'⟩, wtop⟩
    have hw_lt : w'.val < 2 ^ s := w'.isLt
    have hx0_lt : x0.val < 2 := x0.isLt
    have hxor_cancel : ((x0.val + 2 * vecToNat x') ^^^ (w'.val + wtop.val * 2 ^ s)) ^^^
        (w'.val + wtop.val * 2 ^ s) = x0.val + 2 * vecToNat x' := by
      simp [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    refine Prod.ext ?_ (Prod.ext (Prod.ext ?_ ?_) ?_)
    · apply Fin.ext
      dsimp only
      rw [hxor_cancel, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx0_lt]
    · dsimp only
      rw [hxor_cancel]
      funext i
      rw [Nat.testBit_succ]
      have hdiv : (x0.val + 2 * vecToNat x') / 2 = vecToNat x' := by
        rw [Nat.add_mul_div_left _ _ (by omega : 0 < 2), Nat.div_eq_of_lt hx0_lt, zero_add]
      rw [hdiv, testBit_vecToNat]
      generalize x' i = xi
      fin_cases xi <;> rfl
    · apply Fin.ext
      dsimp only
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hw_lt]
    · apply Fin.ext
      dsimp only
      rw [Nat.add_mul_div_right _ _ (by positivity : 0 < 2 ^ s), Nat.div_eq_of_lt hw_lt, zero_add]

/-- Row bijection `φ_row` for Theorem 2.1(a). -/
abbrev phi_row (s : ℕ) := phi_coord s

/-- Column bijection `φ_col` for Theorem 2.1(a). -/
abbrev phi_col (s : ℕ) := phi_coord s

/-- Theorem 2.1(a): Exact Core Factorization `M_{s+1} ≅ I_2 ⊗ K_{s+1} ⊗ J_2`. -/
theorem M_rel_core_factorization (s : ℕ) (r c : Fin (2 ^ (s + 1)) × Fin (2 ^ (s + 1))) :
    M_rel (s + 1) r c ↔
      (phi_row s r).1 = (phi_col s c).1 ∧
      K_coreRel s (phi_row s r).2.1 (phi_col s c).2.1 := by
  rw [M_rel_iff_testBit]
  simp only [K_coreRel, phi_row, phi_col, phi_coord, Equiv.coe_fn_mk]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · apply Fin.ext
      have h0 := h 0 (by omega)
      simp only [pow_zero, Nat.mod_one, lt_self_iff_false, decide_false,
        Nat.testBit_zero] at h0
      have hmod1 : (r.1.val ^^^ r.2.val) % 2 < 2 := Nat.mod_lt _ (by omega)
      have hmod2 : (c.1.val ^^^ c.2.val) % 2 < 2 := Nat.mod_lt _ (by omega)
      revert h0
      cases h1 : decide ((r.1.val ^^^ r.2.val) % 2 = 1) <;>
        cases h2 : decide ((c.1.val ^^^ c.2.val) % 2 = 1) <;> simp_all
    · funext i
      have hi := h (i.val + 1) (by omega)
      have hdvd : 2 ^ (i.val + 1) ∣ 2 ^ s := Nat.pow_dvd_pow 2 (by omega)
      have hm1 : r.2.val % 2 ^ s % 2 ^ (i.val + 1) = r.2.val % 2 ^ (i.val + 1) :=
        Nat.mod_mod_of_dvd _ hdvd
      have hm2 : c.2.val % 2 ^ s % 2 ^ (i.val + 1) = c.2.val % 2 ^ (i.val + 1) :=
        Nat.mod_mod_of_dvd _ hdvd
      simp only [Pi.add_apply, borrowVec, borrowBit, hm1, hm2]
      revert hi
      generalize (r.1.val ^^^ r.2.val).testBit (i.val + 1) = b1
      generalize (c.1.val ^^^ c.2.val).testBit (i.val + 1) = b2
      by_cases hlt : c.2.val % 2 ^ (i.val + 1) < r.2.val % 2 ^ (i.val + 1)
      · simp only [hlt, ↓reduceIte, decide_true]
        cases b1 <;> cases b2 <;> decide
      · simp only [hlt, ↓reduceIte, decide_false]
        cases b1 <;> cases b2 <;> decide
  · rintro ⟨h0, hcore⟩ i hi
    cases i with
    | zero =>
      simp only [pow_zero, Nat.mod_one, lt_self_iff_false, decide_false, Nat.testBit_zero]
      have hv : (r.1.val ^^^ r.2.val) % 2 = (c.1.val ^^^ c.2.val) % 2 := congrArg Fin.val h0
      rw [hv]
      cases decide ((c.1.val ^^^ c.2.val) % 2 = 1) <;> rfl
    | succ k =>
      have hk : k < s := by omega
      have hki := congrFun hcore ⟨k, hk⟩
      have hdvd : 2 ^ (k + 1) ∣ 2 ^ s := Nat.pow_dvd_pow 2 (by omega)
      have hm1 : r.2.val % 2 ^ s % 2 ^ (k + 1) = r.2.val % 2 ^ (k + 1) :=
        Nat.mod_mod_of_dvd _ hdvd
      have hm2 : c.2.val % 2 ^ s % 2 ^ (k + 1) = c.2.val % 2 ^ (k + 1) :=
        Nat.mod_mod_of_dvd _ hdvd
      simp only [Pi.add_apply, borrowVec, borrowBit, hm1, hm2] at hki
      revert hki
      generalize (r.1.val ^^^ r.2.val).testBit (k + 1) = b1
      generalize (c.1.val ^^^ c.2.val).testBit (k + 1) = b2
      by_cases hlt : c.2.val % 2 ^ (k + 1) < r.2.val % 2 ^ (k + 1)
      · simp only [hlt, ↓reduceIte, decide_true]
        cases b1 <;> cases b2 <;> decide
      · simp only [hlt, ↓reduceIte, decide_false]
        cases b1 <;> cases b2 <;> decide

theorem K_coreRel_row_card (s : ℕ) (r : (Fin s → ZMod 2) × Fin (2 ^ s)) :
    (Finset.univ.filter fun c => K_coreRel s r c).card = 2 ^ s := by
  have hcard : (Finset.univ.filter fun c => K_coreRel s r c).card =
      (Finset.univ : Finset (Fin (2 ^ s))).card := by
    refine Finset.card_bij
      (fun c _ => c.2)
      (fun _ _ => Finset.mem_univ _)
      (fun c1 hc1 c2 hc2 h => ?_)
      (fun z _ => ?_)
    · rw [Finset.mem_filter] at hc1 hc2
      apply Prod.ext _ h
      have h1 : c1.1 = r.1 + borrowVec s r.2 c1.2 := (zmod2_vec_add_eq_iff _ _ _).mp hc1.2
      have h2 : c2.1 = r.1 + borrowVec s r.2 c2.2 := (zmod2_vec_add_eq_iff _ _ _).mp hc2.2
      rw [h1, h2, h]
    · refine ⟨(r.1 + borrowVec s r.2 z, z), ?_, rfl⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (zmod2_vec_add_eq_iff _ _ _).mpr rfl⟩
  simpa using hcard

theorem K_coreRel_col_card (s : ℕ) (c : (Fin s → ZMod 2) × Fin (2 ^ s)) :
    (Finset.univ.filter fun r => K_coreRel s r c).card = 2 ^ s := by
  have hcard : (Finset.univ.filter fun r => K_coreRel s r c).card =
      (Finset.univ : Finset (Fin (2 ^ s))).card := by
    refine Finset.card_bij
      (fun r _ => r.2)
      (fun _ _ => Finset.mem_univ _)
      (fun r1 hr1 r2 hr2 h => ?_)
      (fun w _ => ?_)
    · rw [Finset.mem_filter] at hr1 hr2
      apply Prod.ext _ h
      have h1 : r1.1 = c.1 + borrowVec s r1.2 c.2 := (zmod2_vec_add_eq_iff_left _ _ _).mp hr1.2
      have h2 : r2.1 = c.1 + borrowVec s r2.2 c.2 := (zmod2_vec_add_eq_iff_left _ _ _).mp hr2.2
      rw [h1, h2, h]
    · refine ⟨(c.1 + borrowVec s w c.2, w), ?_, rfl⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (zmod2_vec_add_eq_iff_left _ _ _).mpr rfl⟩
  simpa using hcard

theorem K_coreRel_edge_card (s : ℕ) :
    (Finset.univ.filter fun p :
      ((Fin s → ZMod 2) × Fin (2 ^ s)) × ((Fin s → ZMod 2) × Fin (2 ^ s)) =>
      K_coreRel s p.1 p.2).card = 2 ^ (3 * s) := by
  have h1 : (Finset.univ.filter fun p :
      ((Fin s → ZMod 2) × Fin (2 ^ s)) × ((Fin s → ZMod 2) × Fin (2 ^ s)) =>
      K_coreRel s p.1 p.2).card =
      ∑ r : (Fin s → ZMod 2) × Fin (2 ^ s), (Finset.univ.filter fun c => K_coreRel s r c).card := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.card_filter]
  rw [h1]
  simp only [K_coreRel_row_card, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_pi, Fintype.card_fin, ZMod.card, Finset.prod_const, smul_eq_mul]
  calc 2 ^ s * 2 ^ s * 2 ^ s = 2 ^ (s + s + s) := by rw [← pow_add, ← pow_add]
    _ = 2 ^ (3 * s) := by ring_nf

/-- At `t = 1` (`s = 0`), `K_1 = (1)`. -/
theorem K_coreRel_zero (r c : (Fin 0 → ZMod 2) × Fin (2 ^ 0)) : K_coreRel 0 r c := by
  unfold K_coreRel
  funext i
  exact Fin.elim0 i

theorem K_coreMat_zero (R : Type*) [Zero R] [One R] (r c : (Fin 0 → ZMod 2) × Fin (2 ^ 0)) :
    K_coreMat R 0 r c = 1 := by
  simp [K_coreMat, K_coreRel_zero]

/-- Explicit `C_8` row ordering of `K_2` (`s = 1`): `(0,0), (0,1), (1,0), (1,1)`. -/
def c8RowOrder : Fin 4 ≃ (Fin 1 → ZMod 2) × Fin (2 ^ 1) where
  toFun i := (fun _ => ((i.val / 2 : ℕ) : ZMod 2), ⟨i.val % 2, Nat.mod_lt _ (by omega)⟩)
  invFun p := ⟨2 * (p.1 0).val + p.2.val, by
    have h1 := (p.1 0).val_lt; have h2 := p.2.isLt; omega⟩
  left_inv i := by fin_cases i <;> decide
  right_inv p := by
    rcases p with ⟨x, w⟩
    have hx : x = fun _ => x 0 := by funext i; fin_cases i; rfl
    rw [hx]
    generalize x 0 = a
    fin_cases a <;> fin_cases w <;> rfl

/-- Explicit `C_8` column ordering of `K_2` (`s = 1`): `(0,1), (1,0), (1,1), (0,0)`. -/
def c8ColOrder : Fin 4 ≃ (Fin 1 → ZMod 2) × Fin (2 ^ 1) where
  toFun j :=
    let k := (j.val + 1) % 4
    (fun _ => ((k / 2 : ℕ) : ZMod 2), ⟨k % 2, Nat.mod_lt _ (by omega)⟩)
  invFun p := ⟨(2 * (p.1 0).val + p.2.val + 3) % 4, Nat.mod_lt _ (by omega)⟩
  left_inv j := by fin_cases j <;> decide
  right_inv p := by
    rcases p with ⟨y, z⟩
    have hy : y = fun _ => y 0 := by funext i; fin_cases i; rfl
    rw [hy]
    generalize y 0 = a
    fin_cases a <;> fin_cases z <;> rfl

/-- At `t = 2` (`s = 1`), `K_2` is isomorphic to the biadjacency matrix of the 8-cycle `C_8`. -/
theorem K_coreRel_one_C8 (i j : Fin 4) :
    K_coreRel 1 (c8RowOrder i) (c8ColOrder j) ↔ j = i ∨ j = i - 1 := by
  have hiff : K_coreRel 1 (c8RowOrder i) (c8ColOrder j) ↔
      ((c8RowOrder i).1 0 + (c8ColOrder j).1 0 = borrowVec 1 (c8RowOrder i).2 (c8ColOrder j).2 0) := by
    constructor
    · intro h; exact congrFun h 0
    · intro h; funext k; fin_cases k; exact h
  rw [hiff]
  fin_cases i <;> fin_cases j <;> simp [c8RowOrder, c8ColOrder, borrowVec, borrowBit] <;>
    first | rfl | decide

/-! ### Theorem 2.1(b): Anchor-Compatible Lifting Equivalence -/

instance {α β : Type*} {R : α → β → Prop} [∀ r c, Decidable (R r c)]
    (U : Finset α) (V : Finset β) : Decidable (IsBiclique R U V) :=
  inferInstanceAs (Decidable (∀ r ∈ U, ∀ c ∈ V, R r c))

/-- The 2-adic four-point cocycle condition on `(W, Z) ⊆ {0, ..., 2^s - 1}²`. -/
def IsCocycleValid (s : ℕ) (W Z : Finset (Fin (2 ^ s))) : Prop :=
  ∀ w1 ∈ W, ∀ w2 ∈ W, ∀ z1 ∈ Z, ∀ z2 ∈ Z,
    borrowVec s w1 z1 + borrowVec s w1 z2 + borrowVec s w2 z1 + borrowVec s w2 z2 = 0

instance (s : ℕ) (W Z : Finset (Fin (2 ^ s))) : Decidable (IsCocycleValid s W Z) :=
  inferInstanceAs (Decidable (∀ w1 ∈ W, ∀ w2 ∈ W, ∀ z1 ∈ Z, ∀ z2 ∈ Z,
    borrowVec s w1 z1 + borrowVec s w1 z2 + borrowVec s w2 z1 + borrowVec s w2 z2 = 0))

/-- A nonempty cocycle-valid projected pair `(W, Z)`. -/
def IsNonemptyCocycleValid (s : ℕ) (W Z : Finset (Fin (2 ^ s))) : Prop :=
  W.Nonempty ∧ Z.Nonempty ∧ IsCocycleValid s W Z

/-- An inclusion-maximal nonempty cocycle-valid projected pair `(W, Z)`. -/
def IsMaximalCocyclePair (s : ℕ) (W Z : Finset (Fin (2 ^ s))) : Prop :=
  IsNonemptyCocycleValid s W Z ∧
    ∀ W' Z', IsCocycleValid s W' Z' → W ⊆ W' → Z ⊆ Z' → W' = W ∧ Z' = Z

/-- Row projection `W = π_{w'}(U)`. -/
def projW {s : ℕ} (U : Finset ((Fin s → ZMod 2) × Fin (2 ^ s))) : Finset (Fin (2 ^ s)) :=
  U.image Prod.snd

/-- Column projection `Z = π_{z'}(V)`. -/
def projZ {s : ℕ} (V : Finset ((Fin s → ZMod 2) × Fin (2 ^ s))) : Finset (Fin (2 ^ s)) :=
  V.image Prod.snd

/-- Anchor compatibility at some anchor `(x0, w0) ∈ U, (y0, z0) ∈ V`. -/
def IsAnchorCompatible (s : ℕ)
    (U V : Finset ((Fin s → ZMod 2) × Fin (2 ^ s))) : Prop :=
  ∃ x0 w0 y0 z0, (x0, w0) ∈ U ∧ (y0, z0) ∈ V ∧
    (∀ x w, (x, w) ∈ U → x + y0 = borrowVec s w z0) ∧
    (∀ y z, (y, z) ∈ V → x0 + y = borrowVec s w0 z)

/-- Explicit anchor-compatible row lift `U_a` from `(W, Z)` anchored at `(w0, z0)` with shift `a`. -/
def liftU (s : ℕ) (W : Finset (Fin (2 ^ s))) (w0 z0 : Fin (2 ^ s)) (a : Fin s → ZMod 2) :
    Finset ((Fin s → ZMod 2) × Fin (2 ^ s)) :=
  W.image fun w => (a + borrowVec s w z0 + borrowVec s w0 z0, w)

/-- Explicit anchor-compatible column lift `V_a` from `(W, Z)` anchored at `w0` with shift `a`. -/
def liftV (s : ℕ) (Z : Finset (Fin (2 ^ s))) (w0 : Fin (2 ^ s)) (a : Fin s → ZMod 2) :
    Finset ((Fin s → ZMod 2) × Fin (2 ^ s)) :=
  Z.image fun z => (a + borrowVec s w0 z, z)

lemma zmod2_vec_four_cancel {s : ℕ} (a b c d : Fin s → ZMod 2) :
    (a + b) + (a + d) + (c + b) + (c + d) = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize a i = ai; generalize b i = bi; generalize c i = ci; generalize d i = di
  fin_cases ai <;> fin_cases bi <;> fin_cases ci <;> fin_cases di <;> rfl

lemma zmod2_vec_cocycle_solve {s : ℕ} (c11 c12 c21 c22 x1 y1 x2 y2 : Fin s → ZMod 2)
    (hcoc : c11 + c12 + c21 + c22 = 0)
    (h12 : x1 + y2 = c12) (h21 : x2 + y1 = c21) (h22 : x2 + y2 = c22) :
    x1 + y1 = c11 := by
  calc x1 + y1 = (x1 + y1) + 0 := (add_zero _).symm
    _ = (x1 + y1) + (c11 + c12 + c21 + c22) := by rw [hcoc]
    _ = c11 + ((x1 + x1) + (y1 + y1) + (x2 + x2) + (y2 + y2)) := by
        rw [← h12, ← h21, ← h22]; abel
    _ = c11 := by simp [zmod2_vec_add_self]

lemma injOn_snd_of_card_eq_proj {s : ℕ} (S : Finset ((Fin s → ZMod 2) × Fin (2 ^ s)))
    (hcard : S.card = (S.image Prod.snd).card) :
    ∀ x1 x2 w, (x1, w) ∈ S → (x2, w) ∈ S → x1 = x2 := by
  have hinj := Finset.injOn_of_card_image_eq hcard.symm
  intro x1 x2 w h1 h2
  have heq := hinj h1 h2 rfl
  exact congrArg Prod.fst heq

lemma card_eq_proj_of_injOn_snd {s : ℕ} (S : Finset ((Fin s → ZMod 2) × Fin (2 ^ s)))
    (hinj : ∀ x1 x2 w, (x1, w) ∈ S → (x2, w) ∈ S → x1 = x2) :
    S.card = (S.image Prod.snd).card := by
  symm
  apply Finset.card_image_of_injOn
  intro p1 hp1 p2 hp2 h
  apply Prod.ext _ h
  have h2' : (p2.1, p1.2) ∈ S := by rw [h]; exact hp2
  exact hinj p1.1 p2.1 p1.2 hp1 h2'

/-- Theorem 2.1(b) (three-part characterization): a nonempty rectangle `U × V` is an all-ones
biclique of `K_coreRel s` if and only if (i) `|U| = |W|` and `|V| = |Z|`,
(ii) `(W, Z)` satisfies the 4-point 2-adic cocycle condition, and
(iii) anchor compatibility holds at some (equivalently, every) anchor. -/
theorem K_coreRel_biclique_iff_three_conds (s : ℕ)
    {U V : Finset ((Fin s → ZMod 2) × Fin (2 ^ s))}
    (hU : U.Nonempty) (hV : V.Nonempty) :
    IsBiclique (K_coreRel s) U V ↔
      (U.card = (projW U).card ∧ V.card = (projZ V).card) ∧
      IsCocycleValid s (projW U) (projZ V) ∧
      IsAnchorCompatible s U V := by
  constructor
  · intro hbic
    rcases hU with ⟨⟨x0, w0⟩, h0U⟩
    rcases hV with ⟨⟨y0, z0⟩, h0V⟩
    have hUinj : ∀ x1 x2 w, (x1, w) ∈ U → (x2, w) ∈ U → x1 = x2 := by
      intro x1 x2 w h1 h2
      have e1 : x1 + y0 = borrowVec s w z0 := hbic (x1, w) h1 (y0, z0) h0V
      have e2 : x2 + y0 = borrowVec s w z0 := hbic (x2, w) h2 (y0, z0) h0V
      rw [(zmod2_vec_add_eq_iff_left _ _ _).mp e1, (zmod2_vec_add_eq_iff_left _ _ _).mp e2]
    have hVinj : ∀ y1 y2 z, (y1, z) ∈ V → (y2, z) ∈ V → y1 = y2 := by
      intro y1 y2 z h1 h2
      have e1 : x0 + y1 = borrowVec s w0 z := hbic (x0, w0) h0U (y1, z) h1
      have e2 : x0 + y2 = borrowVec s w0 z := hbic (x0, w0) h0U (y2, z) h2
      rw [(zmod2_vec_add_eq_iff _ _ _).mp e1, (zmod2_vec_add_eq_iff _ _ _).mp e2]
    refine ⟨⟨card_eq_proj_of_injOn_snd U hUinj, card_eq_proj_of_injOn_snd V hVinj⟩, ?_, ?_⟩
    · intro w1 hw1 w2 hw2 z1 hz1 z2 hz2
      simp only [projW, projZ, Finset.mem_image, Prod.exists] at hw1 hw2 hz1 hz2
      rcases hw1 with ⟨x1, w1', hx1, hw1'⟩
      rcases hw2 with ⟨x2, w2', hx2, hw2'⟩
      rcases hz1 with ⟨y1, z1', hy1, hz1'⟩
      rcases hz2 with ⟨y2, z2', hy2, hz2'⟩
      subst hw1'; subst hw2'; subst hz1'; subst hz2'
      have e11 : x1 + y1 = borrowVec s w1' z1' := hbic _ hx1 _ hy1
      have e12 : x1 + y2 = borrowVec s w1' z2' := hbic _ hx1 _ hy2
      have e21 : x2 + y1 = borrowVec s w2' z1' := hbic _ hx2 _ hy1
      have e22 : x2 + y2 = borrowVec s w2' z2' := hbic _ hx2 _ hy2
      rw [← e11, ← e12, ← e21, ← e22]
      exact zmod2_vec_four_cancel x1 y1 x2 y2
    · exact ⟨x0, w0, y0, z0, h0U, h0V,
        fun x w h => hbic (x, w) h (y0, z0) h0V,
        fun y z h => hbic (x0, w0) h0U (y, z) h⟩
  · rintro ⟨⟨_, _⟩, hcoc, ⟨x0, w0, y0, z0, h0U, h0V, hancU, hancV⟩⟩
    intro ⟨x, w⟩ hxw ⟨y, z⟩ hyz
    have hw : w ∈ projW U := Finset.mem_image.mpr ⟨(x, w), hxw, rfl⟩
    have hw0 : w0 ∈ projW U := Finset.mem_image.mpr ⟨(x0, w0), h0U, rfl⟩
    have hz : z ∈ projZ V := Finset.mem_image.mpr ⟨(y, z), hyz, rfl⟩
    have hz0 : z0 ∈ projZ V := Finset.mem_image.mpr ⟨(y0, z0), h0V, rfl⟩
    exact zmod2_vec_cocycle_solve _ _ _ _ x y x0 y0
      (hcoc w hw w0 hw0 z hz z0 hz0)
      (hancU x w hxw) (hancV y z hyz) (hancU x0 w0 h0U)

/-- Every anchor in a biclique satisfies anchor compatibility. -/
theorem K_coreRel_biclique_every_anchor (s : ℕ)
    {U V : Finset ((Fin s → ZMod 2) × Fin (2 ^ s))}
    (hbic : IsBiclique (K_coreRel s) U V)
    {x0 w0 y0 z0} (h0U : (x0, w0) ∈ U) (h0V : (y0, z0) ∈ V) :
    (∀ x w, (x, w) ∈ U → x + y0 = borrowVec s w z0) ∧
    (∀ y z, (y, z) ∈ V → x0 + y = borrowVec s w0 z) :=
  ⟨fun x w h => hbic (x, w) h (y0, z0) h0V,
   fun y z h => hbic (x0, w0) h0U (y, z) h⟩

/-- Theorem 2.1(b): Irredundancy of anchor compatibility (iii) at `s = 1`.
The singleton pair `U = {(0, 0)}, V = {(1, 0)}` satisfies (i) and (ii) vacuously
while failing `K_coreRel 1`. -/
theorem anchor_condition_irredundant :
    let U : Finset ((Fin 1 → ZMod 2) × Fin (2 ^ 1)) := {(fun _ => 0, ⟨0, by decide⟩)}
    let V : Finset ((Fin 1 → ZMod 2) × Fin (2 ^ 1)) := {(fun _ => 1, ⟨0, by decide⟩)}
    U.Nonempty ∧ V.Nonempty ∧
    U.card = (projW U).card ∧ V.card = (projZ V).card ∧
    IsCocycleValid 1 (projW U) (projZ V) ∧
    ¬ IsBiclique (K_coreRel 1) U V := by
  dsimp only
  refine ⟨by simp, by simp, by simp [projW], by simp [projZ], ?_, ?_⟩
  · intro w1 hw1 w2 hw2 z1 hz1 z2 hz2
    simp only [projW, projZ, Finset.image_singleton, Finset.mem_singleton] at hw1 hw2 hz1 hz2
    subst hw1; subst hw2; subst hz1; subst hz2
    funext i; fin_cases i; decide
  · intro hbic
    have h0 := hbic (fun _ => 0, ⟨0, by decide⟩) (by simp) (fun _ => 1, ⟨0, by decide⟩) (by simp)
    have h0' := congrFun h0 0
    simp [borrowVec, borrowBit] at h0'

lemma projW_liftU (s : ℕ) (W : Finset (Fin (2 ^ s))) (w0 z0 : Fin (2 ^ s))
    (a : Fin s → ZMod 2) :
    projW (liftU s W w0 z0 a) = W := by
  ext w
  simp [projW, liftU]

lemma projZ_liftV (s : ℕ) (Z : Finset (Fin (2 ^ s))) (w0 : Fin (2 ^ s))
    (a : Fin s → ZMod 2) :
    projZ (liftV s Z w0 a) = Z := by
  ext z
  simp [projZ, liftV]

lemma card_liftU (s : ℕ) (W : Finset (Fin (2 ^ s))) (w0 z0 : Fin (2 ^ s))
    (a : Fin s → ZMod 2) :
    (liftU s W w0 z0 a).card = W.card := by
  apply Finset.card_image_of_injective
  intro w1 w2 h
  exact congrArg Prod.snd h

lemma card_liftV (s : ℕ) (Z : Finset (Fin (2 ^ s))) (w0 : Fin (2 ^ s))
    (a : Fin s → ZMod 2) :
    (liftV s Z w0 a).card = Z.card := by
  apply Finset.card_image_of_injective
  intro z1 z2 h
  exact congrArg Prod.snd h

lemma mem_liftU_anchor (s : ℕ) {W : Finset (Fin (2 ^ s))} {w0 : Fin (2 ^ s)}
    (hw0 : w0 ∈ W) (z0 : Fin (2 ^ s)) (a : Fin s → ZMod 2) :
    (a, w0) ∈ liftU s W w0 z0 a := by
  simp only [liftU, Finset.mem_image]
  refine ⟨w0, hw0, ?_⟩
  refine Prod.ext ?_ rfl
  rw [add_assoc, zmod2_vec_add_self, add_zero]

lemma lift_isBiclique (s : ℕ) {W Z : Finset (Fin (2 ^ s))}
    (hcoc : IsCocycleValid s W Z) {w0 z0 : Fin (2 ^ s)}
    (hw0 : w0 ∈ W) (hz0 : z0 ∈ Z) (a : Fin s → ZMod 2) :
    IsBiclique (K_coreRel s) (liftU s W w0 z0 a) (liftV s Z w0 a) := by
  intro r hr c hc
  simp only [liftU, liftV, Finset.mem_image] at hr hc
  rcases hr with ⟨w, hw, rfl⟩
  rcases hc with ⟨z, hz, rfl⟩
  unfold K_coreRel
  have hc4 := hcoc w hw w0 hw0 z hz z0 hz0
  calc (a + borrowVec s w z0 + borrowVec s w0 z0) + (a + borrowVec s w0 z)
      = (a + a) + (borrowVec s w z0 + borrowVec s w0 z + borrowVec s w0 z0) := by abel
    _ = borrowVec s w z0 + borrowVec s w0 z + borrowVec s w0 z0 := by
        rw [zmod2_vec_add_self, zero_add]
    _ = (borrowVec s w z + borrowVec s w z) +
          (borrowVec s w z0 + borrowVec s w0 z + borrowVec s w0 z0) := by
        rw [zmod2_vec_add_self, zero_add]
    _ = borrowVec s w z +
          (borrowVec s w z + borrowVec s w z0 + borrowVec s w0 z + borrowVec s w0 z0) := by abel
    _ = borrowVec s w z := by rw [hc4, add_zero]

/-- Uniqueness of an anchor-compatible lift once `(W, Z)` and anchor value `a = x'(w0)` are fixed. -/
lemma biclique_eq_lift {s : ℕ} {U V : Finset ((Fin s → ZMod 2) × Fin (2 ^ s))}
    (hbic : IsBiclique (K_coreRel s) U V)
    {a : Fin s → ZMod 2} {w0 : Fin (2 ^ s)} {y0 : Fin s → ZMod 2} {z0 : Fin (2 ^ s)}
    (haU : (a, w0) ∈ U) (hyV : (y0, z0) ∈ V) :
    U = liftU s (projW U) w0 z0 a ∧ V = liftV s (projZ V) w0 a := by
  have h00 : a + y0 = borrowVec s w0 z0 := hbic (a, w0) haU (y0, z0) hyV
  have hy0_eq : y0 = a + borrowVec s w0 z0 := (zmod2_vec_add_eq_iff _ _ _).mp h00
  constructor
  · ext ⟨x, w⟩
    simp only [liftU, projW, Finset.mem_image, Prod.exists]
    constructor
    · intro hxw
      refine ⟨w, ⟨x, w, hxw, rfl⟩, ?_⟩
      refine Prod.ext ?_ rfl
      have h1 : x + y0 = borrowVec s w z0 := hbic (x, w) hxw (y0, z0) hyV
      have hx : x = y0 + borrowVec s w z0 := (zmod2_vec_add_eq_iff_left _ _ _).mp h1
      rw [hx, hy0_eq, add_assoc, add_comm (borrowVec s w z0), ← add_assoc]
    · rintro ⟨w', ⟨x', w'', hx'w', hw''⟩, heq⟩
      subst hw''
      have hx_eq : a + borrowVec s w'' z0 + borrowVec s w0 z0 = x := congrArg Prod.fst heq
      have hw_eq : w'' = w := congrArg Prod.snd heq
      subst hw_eq
      have h1 : x' + y0 = borrowVec s w'' z0 := hbic (x', w'') hx'w' (y0, z0) hyV
      have hx' : x' = y0 + borrowVec s w'' z0 := (zmod2_vec_add_eq_iff_left _ _ _).mp h1
      have hxx' : x = x' := by
        rw [← hx_eq, hx', hy0_eq]
        abel
      rw [hxx']
      exact hx'w'
  · ext ⟨y, z⟩
    simp only [liftV, projZ, Finset.mem_image, Prod.exists]
    constructor
    · intro hyz
      refine ⟨z, ⟨y, z, hyz, rfl⟩, ?_⟩
      refine Prod.ext ?_ rfl
      exact ((zmod2_vec_add_eq_iff _ _ _).mp (hbic (a, w0) haU (y, z) hyz)).symm
    · rintro ⟨z', ⟨y', z'', hy'z', hz''⟩, heq⟩
      subst hz''
      have hy_eq : a + borrowVec s w0 z'' = y := congrArg Prod.fst heq
      have hz_eq : z'' = z := congrArg Prod.snd heq
      subst hz_eq
      have hy' : y' = a + borrowVec s w0 z'' :=
        (zmod2_vec_add_eq_iff _ _ _).mp (hbic (a, w0) haU (y', z'') hy'z')
      rw [← hy_eq, ← hy']
      exact hy'z'

/-- Theorem 2.1(b): Exact `2^s`-to-1 equivalence between `(Fin s → ZMod 2)` and all
anchor-compatible biclique lifts `(U, V)` of a nonempty cocycle-valid pair `(W, Z)`. -/
noncomputable def cocycleLiftsEquiv (s : ℕ) {W Z : Finset (Fin (2 ^ s))}
    (hWZ : IsNonemptyCocycleValid s W Z) (w0 : Fin (2 ^ s)) (hw0 : w0 ∈ W)
    (z0 : Fin (2 ^ s)) (hz0 : z0 ∈ Z) :
    (Fin s → ZMod 2) ≃
      { p : Finset ((Fin s → ZMod 2) × Fin (2 ^ s)) × Finset ((Fin s → ZMod 2) × Fin (2 ^ s)) //
        IsBiclique (K_coreRel s) p.1 p.2 ∧ projW p.1 = W ∧ projZ p.2 = Z } where
  toFun a :=
    ⟨(liftU s W w0 z0 a, liftV s Z w0 a),
     ⟨lift_isBiclique s hWZ.2.2 hw0 hz0 a, projW_liftU s W w0 z0 a, projZ_liftV s Z w0 a⟩⟩
  invFun p :=
    have hw0_in : w0 ∈ projW p.1.1 := by rw [p.2.2.1]; exact hw0
    (Finset.mem_image.mp hw0_in).choose.1
  left_inv a := by
    dsimp only
    set ch := (Finset.mem_image.mp (show w0 ∈ projW (liftU s W w0 z0 a) by
      rw [projW_liftU]; exact hw0)).choose with hch_def
    have hch_mem : ch ∈ liftU s W w0 z0 a :=
      (Finset.mem_image.mp (show w0 ∈ projW (liftU s W w0 z0 a) by
        rw [projW_liftU]; exact hw0)).choose_spec.1
    have hch_snd : ch.2 = w0 :=
      (Finset.mem_image.mp (show w0 ∈ projW (liftU s W w0 z0 a) by
        rw [projW_liftU]; exact hw0)).choose_spec.2
    simp only [liftU, Finset.mem_image] at hch_mem
    rcases hch_mem with ⟨w, _, hweq⟩
    have hw_eq : w = w0 := by
      have := congrArg Prod.snd hweq
      dsimp only at this
      exact this.trans hch_snd
    subst hw_eq
    have hfst := congrArg Prod.fst hweq
    dsimp only at hfst
    rw [← hfst, add_assoc, zmod2_vec_add_self, add_zero]
  right_inv p := by
    rcases p with ⟨⟨U, V⟩, hbic, hW, hZ⟩
    apply Subtype.ext
    dsimp only
    have hw0_in : w0 ∈ projW U := by rw [hW]; exact hw0
    have hz0_in : z0 ∈ projZ V := by rw [hZ]; exact hz0
    set r0 := (Finset.mem_image.mp hw0_in).choose
    have hr0_mem : r0 ∈ U := (Finset.mem_image.mp hw0_in).choose_spec.1
    have hr0_snd : r0.2 = w0 := (Finset.mem_image.mp hw0_in).choose_spec.2
    rcases Finset.mem_image.mp hz0_in with ⟨⟨y0, z0'⟩, hy0V, hz0_eq⟩
    dsimp only at hz0_eq
    subst hz0_eq
    have hr0_eq : (r0.1, w0) ∈ U := by rw [← hr0_snd]; exact hr0_mem
    have ⟨hUeq, hVeq⟩ := biclique_eq_lift hbic hr0_eq hy0V
    rw [hW] at hUeq
    rw [hZ] at hVeq
    exact Prod.ext hUeq.symm hVeq.symm

theorem cocycle_lifts_card (s : ℕ) {W Z : Finset (Fin (2 ^ s))}
    (hWZ : IsNonemptyCocycleValid s W Z) :
    (Finset.univ.filter fun
      p : Finset ((Fin s → ZMod 2) × Fin (2 ^ s)) × Finset ((Fin s → ZMod 2) × Fin (2 ^ s)) =>
      IsBiclique (K_coreRel s) p.1 p.2 ∧ projW p.1 = W ∧ projZ p.2 = Z).card = 2 ^ s := by
  classical
  rcases hWZ.1 with ⟨w0, hw0⟩
  rcases hWZ.2.1 with ⟨z0, hz0⟩
  have h1 : (Finset.univ.filter fun
      p : Finset ((Fin s → ZMod 2) × Fin (2 ^ s)) × Finset ((Fin s → ZMod 2) × Fin (2 ^ s)) =>
      IsBiclique (K_coreRel s) p.1 p.2 ∧ projW p.1 = W ∧ projZ p.2 = Z).card =
      Fintype.card { p : Finset ((Fin s → ZMod 2) × Fin (2 ^ s)) ×
          Finset ((Fin s → ZMod 2) × Fin (2 ^ s)) //
        IsBiclique (K_coreRel s) p.1 p.2 ∧ projW p.1 = W ∧ projZ p.2 = Z } := by
    rw [Fintype.card_subtype]
  rw [h1, ← Fintype.card_congr (cocycleLiftsEquiv s hWZ w0 hw0 z0 hz0)]
  simp [ZMod.card]

/-- Theorem 2.1(b): Coincidence of lifted maximality in `K_coreRel s` and projected maximality. -/
theorem lift_isMaximalBiclique_iff (s : ℕ)
    {U V : Finset ((Fin s → ZMod 2) × Fin (2 ^ s))}
    (hUV : IsNonemptyBiclique (K_coreRel s) U V) :
    IsMaximalBiclique (K_coreRel s) U V ↔ IsMaximalCocyclePair s (projW U) (projZ V) := by
  rcases hUV with ⟨hUne, hVne, hbic⟩
  have h3 := (K_coreRel_biclique_iff_three_conds s hUne hVne).mp hbic
  rcases h3 with ⟨⟨hUcard, hVcard⟩, hcoc, _⟩
  have hWne : (projW U).Nonempty := hUne.image Prod.snd
  have hZne : (projZ V).Nonempty := hVne.image Prod.snd
  constructor
  · intro hmax
    refine ⟨⟨hWne, hZne, hcoc⟩, ?_⟩
    intro W' Z' hcoc' hWW' hZZ'
    rcases hUne with ⟨⟨a, w0⟩, haU⟩
    rcases hVne with ⟨⟨y0, z0⟩, hy0V⟩
    have hw0W : w0 ∈ projW U := Finset.mem_image.mpr ⟨(a, w0), haU, rfl⟩
    have hz0Z : z0 ∈ projZ V := Finset.mem_image.mpr ⟨(y0, z0), hy0V, rfl⟩
    have ⟨hUeq, hVeq⟩ := biclique_eq_lift hbic haU hy0V
    let U' := liftU s W' w0 z0 a
    let V' := liftV s Z' w0 a
    have hbic' : IsBiclique (K_coreRel s) U' V' :=
      lift_isBiclique s hcoc' (hWW' hw0W) (hZZ' hz0Z) a
    have hUU' : U ⊆ U' := by
      rw [hUeq]; exact Finset.image_subset_image hWW'
    have hVV' : V ⊆ V' := by
      rw [hVeq]; exact Finset.image_subset_image hZZ'
    have ⟨hU'eq, hV'eq⟩ := hmax.2 U' V' hbic' hUU' hVV'
    constructor
    · rw [← projW_liftU s W' w0 z0 a, show liftU s W' w0 z0 a = U' from rfl, hU'eq]
    · rw [← projZ_liftV s Z' w0 a, show liftV s Z' w0 a = V' from rfl, hV'eq]
  · intro hmaxP
    refine ⟨⟨hUne, hVne, hbic⟩, ?_⟩
    intro U' V' hbic' hUU' hVV'
    have hU'ne : U'.Nonempty := hUne.mono hUU'
    have hV'ne : V'.Nonempty := hVne.mono hVV'
    have h3' := (K_coreRel_biclique_iff_three_conds s hU'ne hV'ne).mp hbic'
    have hWW' : projW U ⊆ projW U' := Finset.image_subset_image hUU'
    have hZZ' : projZ V ⊆ projZ V' := Finset.image_subset_image hVV'
    have ⟨hW'eq, hZ'eq⟩ := hmaxP.2 (projW U') (projZ V') h3'.2.1 hWW' hZZ'
    have hcardU' : U'.card = U.card := by rw [h3'.1.1, hW'eq, ← hUcard]
    have hcardV' : V'.card = V.card := by rw [h3'.1.2, hZ'eq, ← hVcard]
    exact ⟨Finset.eq_of_subset_of_card_le hUU' hcardU'.le |>.symm,
           Finset.eq_of_subset_of_card_le hVV' hcardV'.le |>.symm⟩

/-! ### Theorem 2.1(c): Complete `4^s` Classification, Shape Generating Function, `8^s` Core Maximal Bicliques, and `A_max` -/

/-- Even embedding `w ↦ 2w` from `Fin (2^s)` to `Fin (2^(s+1))`. -/
def embEven {s : ℕ} (w : Fin (2 ^ s)) : Fin (2 ^ (s + 1)) :=
  ⟨2 * w.val, by
    have := w.isLt
    have h : 2 ^ (s + 1) = 2 * 2 ^ s := by ring
    omega⟩

/-- Odd embedding `w ↦ 2w + 1` from `Fin (2^s)` to `Fin (2^(s+1))`. -/
def embOdd {s : ℕ} (w : Fin (2 ^ s)) : Fin (2 ^ (s + 1)) :=
  ⟨2 * w.val + 1, by
    have := w.isLt
    have h : 2 ^ (s + 1) = 2 * 2 ^ s := by ring
    omega⟩

/-- Halving projection `x ↦ ⌊x / 2⌋` from `Fin (2^(s+1))` to `Fin (2^s)`. -/
def halfFin {s : ℕ} (x : Fin (2 ^ (s + 1))) : Fin (2 ^ s) :=
  ⟨x.val / 2, by
    have := x.isLt
    have h : 2 ^ (s + 1) = 2 * 2 ^ s := by ring
    omega⟩

/-- Cyclic shift `θ_-(z) = (z - 1) mod 2^(s+1)`. -/
def thetaMinus {s : ℕ} (z : Fin (2 ^ (s + 1))) : Fin (2 ^ (s + 1)) :=
  ⟨(z.val + 2 ^ (s + 1) - 1) % 2 ^ (s + 1), Nat.mod_lt _ (by positivity)⟩

/-- Cyclic shift `θ_+(w) = (w + 1) mod 2^(s+1)`. -/
def thetaPlus {s : ℕ} (w : Fin (2 ^ (s + 1))) : Fin (2 ^ (s + 1)) :=
  ⟨(w.val + 1) % 2 ^ (s + 1), Nat.mod_lt _ (by positivity)⟩

lemma embEven_injective {s : ℕ} : Function.Injective (@embEven s) := by
  intro a b h; apply Fin.ext; have := congrArg Fin.val h; simp [embEven] at this; omega

lemma embOdd_injective {s : ℕ} : Function.Injective (@embOdd s) := by
  intro a b h; apply Fin.ext; have := congrArg Fin.val h; simp [embOdd] at this; omega

lemma halfFin_embEven {s : ℕ} (w : Fin (2 ^ s)) : halfFin (embEven w) = w := by
  apply Fin.ext; simp [halfFin, embEven]

lemma halfFin_embOdd {s : ℕ} (w : Fin (2 ^ s)) : halfFin (embOdd w) = w := by
  apply Fin.ext; simp [halfFin, embOdd]; omega

lemma embEven_halfFin {s : ℕ} {x : Fin (2 ^ (s + 1))} (hx : x.val % 2 = 0) :
    embEven (halfFin x) = x := by
  apply Fin.ext; simp [embEven, halfFin]; omega

lemma embOdd_halfFin {s : ℕ} {x : Fin (2 ^ (s + 1))} (hx : x.val % 2 = 1) :
    embOdd (halfFin x) = x := by
  apply Fin.ext; simp [embOdd, halfFin]; omega

lemma thetaPlus_thetaMinus {s : ℕ} (z : Fin (2 ^ (s + 1))) : thetaPlus (thetaMinus z) = z := by
  apply Fin.ext
  simp only [thetaPlus, thetaMinus]
  have hz := z.isLt
  have hpos : 1 ≤ 2 ^ (s + 1) := Nat.one_le_two_pow
  rw [Nat.mod_add_mod]
  have hsub : z.val + 2 ^ (s + 1) - 1 + 1 = z.val + 2 ^ (s + 1) := by omega
  rw [hsub, Nat.add_mod_right, Nat.mod_eq_of_lt hz]

lemma thetaMinus_thetaPlus {s : ℕ} (w : Fin (2 ^ (s + 1))) : thetaMinus (thetaPlus w) = w := by
  apply Fin.ext
  simp only [thetaPlus, thetaMinus]
  have hw := w.isLt
  have hpos : 1 ≤ 2 ^ (s + 1) := Nat.one_le_two_pow
  by_cases hlast : w.val + 1 = 2 ^ (s + 1)
  · rw [hlast, Nat.mod_self, zero_add, Nat.mod_eq_of_lt (by omega)]
    omega
  · have hmod : (w.val + 1) % 2 ^ (s + 1) = w.val + 1 := Nat.mod_eq_of_lt (by omega)
    rw [hmod]
    have hsub : w.val + 1 + 2 ^ (s + 1) - 1 = w.val + 2 ^ (s + 1) := by omega
    rw [hsub, Nat.add_mod_right, Nat.mod_eq_of_lt hw]

lemma thetaMinus_bijective {s : ℕ} : Function.Bijective (@thetaMinus s) :=
  Function.bijective_iff_has_inverse.mpr ⟨thetaPlus, thetaPlus_thetaMinus, thetaMinus_thetaPlus⟩

lemma thetaPlus_bijective {s : ℕ} : Function.Bijective (@thetaPlus s) :=
  Function.bijective_iff_has_inverse.mpr ⟨thetaMinus, thetaMinus_thetaPlus, thetaPlus_thetaMinus⟩

lemma filter_halfFin_eq_union {s : ℕ} (A : Finset (Fin (2 ^ s))) :
    (Finset.univ.filter fun x : Fin (2 ^ (s + 1)) => halfFin x ∈ A) =
      A.image embEven ∪ A.image embOdd := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_image]
  constructor
  · intro hx
    by_cases hpar : x.val % 2 = 0
    · exact Or.inl ⟨halfFin x, hx, embEven_halfFin hpar⟩
    · exact Or.inr ⟨halfFin x, hx, embOdd_halfFin (by omega)⟩
  · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
    · rwa [halfFin_embEven]
    · rwa [halfFin_embOdd]

lemma card_filter_halfFin {s : ℕ} (A : Finset (Fin (2 ^ s))) :
    (Finset.univ.filter fun x : Fin (2 ^ (s + 1)) => halfFin x ∈ A).card = 2 * A.card := by
  rw [filter_halfFin_eq_union, Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injective _ embEven_injective,
        Finset.card_image_of_injective _ embOdd_injective]
    ring
  · rw [Finset.disjoint_left]
    intro x h1 h2
    simp only [Finset.mem_image] at h1 h2
    rcases h1 with ⟨a, _, rfl⟩
    rcases h2 with ⟨b, _, h⟩
    have := congrArg Fin.val h
    simp [embEven, embOdd] at this
    omega

lemma card_filter_halfFin_thetaMinus {s : ℕ} (A : Finset (Fin (2 ^ s))) :
    (Finset.univ.filter fun z : Fin (2 ^ (s + 1)) => halfFin (thetaMinus z) ∈ A).card =
      2 * A.card := by
  have heq : (Finset.univ.filter fun z : Fin (2 ^ (s + 1)) => halfFin (thetaMinus z) ∈ A) =
      (Finset.univ.filter fun z : Fin (2 ^ (s + 1)) => halfFin z ∈ A).image thetaPlus := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hz; exact ⟨thetaMinus z, hz, thetaPlus_thetaMinus z⟩
    · rintro ⟨y, hy, rfl⟩; rwa [thetaMinus_thetaPlus]
  rw [heq, Finset.card_image_of_injective _ thetaPlus_bijective.1, card_filter_halfFin]

lemma card_filter_halfFin_thetaPlus {s : ℕ} (A : Finset (Fin (2 ^ s))) :
    (Finset.univ.filter fun w : Fin (2 ^ (s + 1)) => halfFin (thetaPlus w) ∈ A).card =
      2 * A.card := by
  have heq : (Finset.univ.filter fun w : Fin (2 ^ (s + 1)) => halfFin (thetaPlus w) ∈ A) =
      (Finset.univ.filter fun w : Fin (2 ^ (s + 1)) => halfFin w ∈ A).image thetaMinus := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hw; exact ⟨thetaPlus w, hw, thetaMinus_thetaPlus w⟩
    · rintro ⟨y, hy, rfl⟩; rwa [thetaPlus_thetaMinus]
  rw [heq, Finset.card_image_of_injective _ thetaMinus_bijective.1, card_filter_halfFin]

lemma image_halfFin_filter_halfFin {s : ℕ} (A : Finset (Fin (2 ^ s))) :
    (Finset.univ.filter fun x : Fin (2 ^ (s + 1)) => halfFin x ∈ A).image halfFin = A := by
  ext a
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hx
  · intro ha; exact ⟨embEven a, by rwa [halfFin_embEven], halfFin_embEven a⟩

lemma image_halfFin_thetaMinus_filter {s : ℕ} (A : Finset (Fin (2 ^ s))) :
    (Finset.univ.filter fun z : Fin (2 ^ (s + 1)) => halfFin (thetaMinus z) ∈ A).image
      (fun z => halfFin (thetaMinus z)) = A := by
  ext a
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨z, hz, rfl⟩; exact hz
  · intro ha
    refine ⟨thetaPlus (embEven a), ?_, ?_⟩
    · rwa [thetaMinus_thetaPlus, halfFin_embEven]
    · rw [thetaMinus_thetaPlus, halfFin_embEven]

lemma image_halfFin_thetaPlus_filter {s : ℕ} (A : Finset (Fin (2 ^ s))) :
    (Finset.univ.filter fun w : Fin (2 ^ (s + 1)) => halfFin (thetaPlus w) ∈ A).image
      (fun w => halfFin (thetaPlus w)) = A := by
  ext a
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨w, hw, rfl⟩; exact hw
  · intro ha
    refine ⟨thetaMinus (embEven a), ?_, ?_⟩
    · rwa [thetaPlus_thetaMinus, halfFin_embEven]
    · rw [thetaPlus_thetaMinus, halfFin_embEven]

/-! #### The Four Borrow Shift Identities -/

lemma borrowBit_case1a (k w z : ℕ) :
    borrowBit (k + 2) (2 * w) z = borrowBit (k + 1) w (z / 2) := by
  unfold borrowBit
  have h1 : (2 * w) % 2 ^ (k + 2) = 2 * (w % 2 ^ (k + 1)) := by
    rw [pow_succ', Nat.mul_mod_mul_left]
  have h2 : z % 2 ^ (k + 2) = 2 * ((z / 2) % 2 ^ (k + 1)) + z % 2 := by
    have hdiv := Nat.div_add_mod z 2
    have hm : z % 2 ^ (k + 2) / 2 = (z / 2) % 2 ^ (k + 1) := by
      rw [pow_succ', mul_comm 2 (2 ^ (k + 1)), Nat.mod_mul_left_div_self]
    have hrem : z % 2 ^ (k + 2) % 2 = z % 2 :=
      Nat.mod_mod_of_dvd z (dvd_pow_self 2 (by omega : k + 2 ≠ 0))
    have := Nat.div_add_mod (z % 2 ^ (k + 2)) 2
    omega
  have hz2 : z % 2 < 2 := Nat.mod_lt _ (by omega)
  rw [h1, h2]
  have hiff : 2 * ((z / 2) % 2 ^ (k + 1)) + z % 2 < 2 * (w % 2 ^ (k + 1)) ↔
      (z / 2) % 2 ^ (k + 1) < w % 2 ^ (k + 1) := by omega
  by_cases h : (z / 2) % 2 ^ (k + 1) < w % 2 ^ (k + 1)
  · simp [h, hiff.mpr h]
  · have hn : ¬ (2 * ((z / 2) % 2 ^ (k + 1)) + z % 2 < 2 * (w % 2 ^ (k + 1))) := by omega
    simp [h, hn]

lemma borrowBit_case2a (k w z : ℕ) :
    borrowBit (k + 2) w (2 * z + 1) = borrowBit (k + 1) (w / 2) z := by
  unfold borrowBit
  have h2 : (2 * z + 1) % 2 ^ (k + 2) = 2 * (z % 2 ^ (k + 1)) + 1 := by
    have hpow : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [pow_succ']
    have hmod_lt : z % 2 ^ (k + 1) < 2 ^ (k + 1) := Nat.mod_lt _ (by positivity)
    have hdiv := Nat.div_add_mod z (2 ^ (k + 1))
    have hrewrite : 2 * z + 1 = (2 * (z % 2 ^ (k + 1)) + 1) + (z / 2 ^ (k + 1)) * 2 ^ (k + 2) := by
      rw [hpow]; linarith
    rw [hrewrite, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  have h1 : w % 2 ^ (k + 2) = 2 * ((w / 2) % 2 ^ (k + 1)) + w % 2 := by
    have hm : w % 2 ^ (k + 2) / 2 = (w / 2) % 2 ^ (k + 1) := by
      rw [pow_succ', mul_comm 2 (2 ^ (k + 1)), Nat.mod_mul_left_div_self]
    have hrem : w % 2 ^ (k + 2) % 2 = w % 2 :=
      Nat.mod_mod_of_dvd w (dvd_pow_self 2 (by omega : k + 2 ≠ 0))
    have := Nat.div_add_mod (w % 2 ^ (k + 2)) 2
    omega
  have hw2 : w % 2 < 2 := Nat.mod_lt _ (by omega)
  rw [h1, h2]
  have hiff : 2 * (z % 2 ^ (k + 1)) + 1 < 2 * ((w / 2) % 2 ^ (k + 1)) + w % 2 ↔
      z % 2 ^ (k + 1) < (w / 2) % 2 ^ (k + 1) := by omega
  by_cases h : z % 2 ^ (k + 1) < (w / 2) % 2 ^ (k + 1)
  · simp [h, hiff.mpr h]
  · have hn : ¬ (2 * (z % 2 ^ (k + 1)) + 1 < 2 * ((w / 2) % 2 ^ (k + 1)) + w % 2) := by omega
    simp [h, hn]

lemma borrowBit_case1b {s k : ℕ} (hk : k < s) (w : Fin (2 ^ s)) (z : Fin (2 ^ (s + 1))) :
    borrowBit (k + 2) (embOdd w).val z.val =
      borrowBit (k + 1) w.val (halfFin (thetaMinus z)).val +
        if z.val % 2 ^ (k + 2) = 0 then (1 : ZMod 2) else 0 := by
  unfold borrowBit
  have hdvd : 2 ^ (k + 2) ∣ 2 ^ (s + 1) := Nat.pow_dvd_pow 2 (by omega)
  have hpow : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [pow_succ']
  have hw_mod : (embOdd w).val % 2 ^ (k + 2) = 2 * (w.val % 2 ^ (k + 1)) + 1 := by
    simp only [embOdd]
    have hmod_lt : w.val % 2 ^ (k + 1) < 2 ^ (k + 1) := Nat.mod_lt _ (by positivity)
    have hdiv := Nat.div_add_mod w.val (2 ^ (k + 1))
    have hrew : 2 * w.val + 1 = (2 * (w.val % 2 ^ (k + 1)) + 1) +
        (w.val / 2 ^ (k + 1)) * 2 ^ (k + 2) := by rw [hpow]; linarith
    rw [hrew, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  have htm_mod : (thetaMinus z).val % 2 ^ (k + 2) =
      (z.val + 2 ^ (s + 1) - 1) % 2 ^ (k + 2) := by
    simp only [thetaMinus]
    exact Nat.mod_mod_of_dvd _ hdvd
  have hhalf_mod : (halfFin (thetaMinus z)).val % 2 ^ (k + 1) =
      (thetaMinus z).val % 2 ^ (k + 2) / 2 := by
    simp only [halfFin]
    set m := (thetaMinus z).val
    rw [show 2 ^ (k + 2) = 2 ^ (k + 1) * 2 by ring, Nat.mod_mul_left_div_self]
  rw [hw_mod, hhalf_mod, htm_mod]
  have hpos_s : 1 ≤ 2 ^ (s + 1) := Nat.one_le_two_pow
  have hpos_k : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  have hw_lt : w.val % 2 ^ (k + 1) < 2 ^ (k + 1) := Nat.mod_lt _ (by positivity)
  by_cases hz0 : z.val % 2 ^ (k + 2) = 0
  · simp only [hz0, ↓reduceIte]
    have hlt1 : 0 < 2 * (w.val % 2 ^ (k + 1)) + 1 := by omega
    have htm_val : (z.val + 2 ^ (s + 1) - 1) % 2 ^ (k + 2) = 2 ^ (k + 2) - 1 := by
      rcases hdvd with ⟨q, hq⟩
      have hz_dvd : 2 ^ (k + 2) ∣ z.val := Nat.dvd_of_mod_eq_zero hz0
      rcases hz_dvd with ⟨r, hr⟩
      have hq1 : 1 ≤ q := by
        have : 0 < 2 ^ (s + 1) := by positivity
        rw [hq] at this; nlinarith
      have heq : z.val + 2 ^ (s + 1) - 1 = (2 ^ (k + 2) - 1) + (r + q - 1) * 2 ^ (k + 2) := by
        have h1 : 1 ≤ r + q := by omega
        have h2 : (r + q) * 2 ^ (k + 2) = 2 ^ (k + 2) + (r + q - 1) * 2 ^ (k + 2) := by
          calc (r + q) * 2 ^ (k + 2) = (1 + (r + q - 1)) * 2 ^ (k + 2) := by congr 1; omega
            _ = 2 ^ (k + 2) + (r + q - 1) * 2 ^ (k + 2) := by ring
        have hsum : z.val + 2 ^ (s + 1) = (r + q) * 2 ^ (k + 2) := by
          calc z.val + 2 ^ (s + 1) = 2 ^ (k + 2) * r + 2 ^ (k + 2) * q := by rw [hr, hq]
            _ = (r + q) * 2 ^ (k + 2) := by ring
        omega
      rw [heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    rw [htm_val]
    have hdiv_eq : (2 ^ (k + 2) - 1) / 2 = 2 ^ (k + 1) - 1 := by omega
    rw [hdiv_eq]
    have hnot : ¬ (2 ^ (k + 1) - 1 < w.val % 2 ^ (k + 1)) := by omega
    simp [hlt1, hnot]
  · simp only [hz0, ↓reduceIte, add_zero]
    have hz_pos : 1 ≤ z.val % 2 ^ (k + 2) := by omega
    have hz_lt : z.val % 2 ^ (k + 2) < 2 ^ (k + 2) := Nat.mod_lt _ (by positivity)
    have htm_val : (z.val + 2 ^ (s + 1) - 1) % 2 ^ (k + 2) = z.val % 2 ^ (k + 2) - 1 := by
      rcases hdvd with ⟨q, hq⟩
      have hdiv := Nat.div_add_mod z.val (2 ^ (k + 2))
      have heq : z.val + 2 ^ (s + 1) - 1 =
          (z.val % 2 ^ (k + 2) - 1) + (z.val / 2 ^ (k + 2) + q) * 2 ^ (k + 2) := by
        have hsum : 2 ^ (k + 2) * (z.val / 2 ^ (k + 2)) + 2 ^ (s + 1) =
            (z.val / 2 ^ (k + 2) + q) * 2 ^ (k + 2) := by
          calc 2 ^ (k + 2) * (z.val / 2 ^ (k + 2)) + 2 ^ (s + 1)
              = 2 ^ (k + 2) * (z.val / 2 ^ (k + 2)) + 2 ^ (k + 2) * q :=
                congrArg (2 ^ (k + 2) * (z.val / 2 ^ (k + 2)) + ·) hq
            _ = (z.val / 2 ^ (k + 2) + q) * 2 ^ (k + 2) := by ring
        omega
      rw [heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    rw [htm_val]
    have hiff : z.val % 2 ^ (k + 2) < 2 * (w.val % 2 ^ (k + 1)) + 1 ↔
        (z.val % 2 ^ (k + 2) - 1) / 2 < w.val % 2 ^ (k + 1) := by omega
    by_cases h : (z.val % 2 ^ (k + 2) - 1) / 2 < w.val % 2 ^ (k + 1)
    · simp [h, hiff.mpr h]
    · have hn : ¬ (z.val % 2 ^ (k + 2) < 2 * (w.val % 2 ^ (k + 1)) + 1) := by omega
      simp [h, hn]

lemma borrowBit_case2b {s k : ℕ} (hk : k < s) (w : Fin (2 ^ (s + 1))) (z : Fin (2 ^ s)) :
    borrowBit (k + 2) w.val (embEven z).val =
      borrowBit (k + 1) (halfFin (thetaPlus w)).val z.val +
        if w.val % 2 ^ (k + 2) = 2 ^ (k + 2) - 1 then (1 : ZMod 2) else 0 := by
  unfold borrowBit
  have hdvd : 2 ^ (k + 2) ∣ 2 ^ (s + 1) := Nat.pow_dvd_pow 2 (by omega)
  have hpow : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [pow_succ']
  have hz_mod : (embEven z).val % 2 ^ (k + 2) = 2 * (z.val % 2 ^ (k + 1)) := by
    simp only [embEven]; rw [hpow, Nat.mul_mod_mul_left]
  have htp_mod : (thetaPlus w).val % 2 ^ (k + 2) = (w.val + 1) % 2 ^ (k + 2) := by
    simp only [thetaPlus]; exact Nat.mod_mod_of_dvd _ hdvd
  have hhalf_mod : (halfFin (thetaPlus w)).val % 2 ^ (k + 1) =
      (thetaPlus w).val % 2 ^ (k + 2) / 2 := by
    simp only [halfFin]
    set m := (thetaPlus w).val
    rw [show 2 ^ (k + 2) = 2 ^ (k + 1) * 2 by ring, Nat.mod_mul_left_div_self]
  rw [hz_mod, hhalf_mod, htp_mod]
  have hpos_k : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  have hz_lt : z.val % 2 ^ (k + 1) < 2 ^ (k + 1) := Nat.mod_lt _ (by positivity)
  have hw_lt : w.val % 2 ^ (k + 2) < 2 ^ (k + 2) := Nat.mod_lt _ (by positivity)
  by_cases hw_max : w.val % 2 ^ (k + 2) = 2 ^ (k + 2) - 1
  · simp only [hw_max, ↓reduceIte]
    have hlt1 : 2 * (z.val % 2 ^ (k + 1)) < 2 ^ (k + 2) - 1 := by omega
    have htp_zero : (w.val + 1) % 2 ^ (k + 2) = 0 := by
      rw [Nat.add_mod, hw_max]
      have : 2 ^ (k + 2) - 1 + 1 % 2 ^ (k + 2) = 2 ^ (k + 2) := by
        rw [Nat.mod_eq_of_lt (by omega : 1 < 2 ^ (k + 2))]; omega
      rw [this, Nat.mod_self]
    rw [htp_zero]
    simp [hlt1]
  · simp only [hw_max, ↓reduceIte, add_zero]
    have htp_val : (w.val + 1) % 2 ^ (k + 2) = w.val % 2 ^ (k + 2) + 1 := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < 2 ^ (k + 2)),
          Nat.mod_eq_of_lt (by omega)]
    rw [htp_val]
    have hiff : 2 * (z.val % 2 ^ (k + 1)) < w.val % 2 ^ (k + 2) ↔
        z.val % 2 ^ (k + 1) < (w.val % 2 ^ (k + 2) + 1) / 2 := by omega
    by_cases h : z.val % 2 ^ (k + 1) < (w.val % 2 ^ (k + 2) + 1) / 2
    · simp [h, hiff.mpr h]
    · have hn : ¬ (2 * (z.val % 2 ^ (k + 1)) < w.val % 2 ^ (k + 2)) := by omega
      simp [h, hn]

/-! #### Cocycle Parity Dichotomy & 4-Way Equivalence -/

lemma zmod2_four_univariate_z {α : Type*} (f : α → ZMod 2) (z1 z2 : α) :
    f z1 + f z2 + f z1 + f z2 = 0 := by
  have h1 := zmod2_add_self (f z1)
  have h2 := zmod2_add_self (f z2)
  calc f z1 + f z2 + f z1 + f z2 = (f z1 + f z1) + (f z2 + f z2) := by abel
    _ = 0 := by rw [h1, h2, add_zero]

lemma zmod2_four_univariate_w {α : Type*} (f : α → ZMod 2) (w1 w2 : α) :
    f w1 + f w1 + f w2 + f w2 = 0 := by
  have h1 := zmod2_add_self (f w1)
  have h2 := zmod2_add_self (f w2)
  calc f w1 + f w1 + f w2 + f w2 = (f w1 + f w1) + (f w2 + f w2) := by abel
    _ = 0 := by rw [h1, h2, add_zero]

/-- On bit `0`, no cocycle-valid pair can have BOTH parities in `W` AND BOTH parities in `Z`. -/
lemma cocycle_parity_obstruction {s : ℕ} {W Z : Finset (Fin (2 ^ (s + 1)))}
    (hcoc : IsCocycleValid (s + 1) W Z)
    {we wo ze zo : Fin (2 ^ (s + 1))}
    (hwe : we ∈ W) (hwo : wo ∈ W) (hze : ze ∈ Z) (hzo : zo ∈ Z)
    (heW : we.val % 2 = 0) (hoW : wo.val % 2 = 1)
    (heZ : ze.val % 2 = 0) (hoZ : zo.val % 2 = 1) : False := by
  have h0 := congrFun (hcoc we hwe wo hwo ze hze zo hzo) 0
  simp only [Pi.add_apply, Pi.zero_apply, borrowVec, borrowBit, Fin.val_zero, zero_add,
    pow_one, heW, hoW, heZ, hoZ] at h0
  revert h0
  decide

lemma cocycle_case1a_iff {s : ℕ} {W Z : Finset (Fin (2 ^ (s + 1)))}
    (hW : ∀ w ∈ W, w.val % 2 = 0) :
    IsCocycleValid (s + 1) W Z ↔ IsCocycleValid s (W.image halfFin) (Z.image halfFin) := by
  have hstep : ∀ w1 ∈ W, ∀ w2 ∈ W, ∀ z1 ∈ Z, ∀ z2 ∈ Z,
      (borrowVec (s + 1) w1 z1 + borrowVec (s + 1) w1 z2 +
       borrowVec (s + 1) w2 z1 + borrowVec (s + 1) w2 z2 = 0) ↔
      (borrowVec s (halfFin w1) (halfFin z1) + borrowVec s (halfFin w1) (halfFin z2) +
       borrowVec s (halfFin w2) (halfFin z1) + borrowVec s (halfFin w2) (halfFin z2) = 0) := by
    intro w1 hw1 w2 hw2 z1 _ z2 _
    have ew1 : w1.val = 2 * (halfFin w1).val := by
      have := hW w1 hw1; simp [halfFin]; omega
    have ew2 : w2.val = 2 * (halfFin w2).val := by
      have := hW w2 hw2; simp [halfFin]; omega
    constructor
    · intro h
      funext k
      have hk := congrFun h k.succ
      simp only [Pi.add_apply, Pi.zero_apply, borrowVec, Fin.val_succ] at hk ⊢
      rw [ew1, ew2, borrowBit_case1a, borrowBit_case1a, borrowBit_case1a, borrowBit_case1a] at hk
      exact hk
    · intro h
      funext i
      refine Fin.cases ?_ (fun k => ?_) i
      · simp only [Pi.add_apply, Pi.zero_apply, borrowVec, borrowBit, Fin.val_zero, zero_add,
          pow_one, hW w1 hw1, hW w2 hw2, Nat.not_lt_zero, ↓reduceIte, add_zero]
      · have hk := congrFun h k
        simp only [Pi.add_apply, Pi.zero_apply, borrowVec, Fin.val_succ] at hk ⊢
        rw [ew1, ew2, borrowBit_case1a, borrowBit_case1a, borrowBit_case1a, borrowBit_case1a]
        exact hk
  constructor
  · intro h w1' hw1' w2' hw2' z1' hz1' z2' hz2'
    simp only [Finset.mem_image] at hw1' hw2' hz1' hz2'
    rcases hw1' with ⟨w1, hw1, rfl⟩; rcases hw2' with ⟨w2, hw2, rfl⟩
    rcases hz1' with ⟨z1, hz1, rfl⟩; rcases hz2' with ⟨z2, hz2, rfl⟩
    exact (hstep w1 hw1 w2 hw2 z1 hz1 z2 hz2).mp (h w1 hw1 w2 hw2 z1 hz1 z2 hz2)
  · intro h w1 hw1 w2 hw2 z1 hz1 z2 hz2
    exact (hstep w1 hw1 w2 hw2 z1 hz1 z2 hz2).mpr
      (h _ (Finset.mem_image_of_mem _ hw1) _ (Finset.mem_image_of_mem _ hw2)
         _ (Finset.mem_image_of_mem _ hz1) _ (Finset.mem_image_of_mem _ hz2))

lemma cocycle_case1b_iff {s : ℕ} {W Z : Finset (Fin (2 ^ (s + 1)))}
    (hW : ∀ w ∈ W, w.val % 2 = 1) :
    IsCocycleValid (s + 1) W Z ↔
      IsCocycleValid s (W.image halfFin) (Z.image fun z => halfFin (thetaMinus z)) := by
  have hstep : ∀ w1 ∈ W, ∀ w2 ∈ W, ∀ z1 ∈ Z, ∀ z2 ∈ Z,
      (borrowVec (s + 1) w1 z1 + borrowVec (s + 1) w1 z2 +
       borrowVec (s + 1) w2 z1 + borrowVec (s + 1) w2 z2 = 0) ↔
      (borrowVec s (halfFin w1) (halfFin (thetaMinus z1)) +
       borrowVec s (halfFin w1) (halfFin (thetaMinus z2)) +
       borrowVec s (halfFin w2) (halfFin (thetaMinus z1)) +
       borrowVec s (halfFin w2) (halfFin (thetaMinus z2)) = 0) := by
    intro w1 hw1 w2 hw2 z1 _ z2 _
    have ew1 : w1 = embOdd (halfFin w1) := (embOdd_halfFin (hW w1 hw1)).symm
    have ew2 : w2 = embOdd (halfFin w2) := (embOdd_halfFin (hW w2 hw2)).symm
    constructor
    · intro h
      funext k
      have hk := congrFun h k.succ
      simp only [Pi.add_apply, Pi.zero_apply, borrowVec, Fin.val_succ] at hk ⊢
      rw [ew1, ew2, borrowBit_case1b k.isLt, borrowBit_case1b k.isLt,
          borrowBit_case1b k.isLt, borrowBit_case1b k.isLt] at hk
      set g : Fin (2 ^ (s + 1)) → ZMod 2 := fun z => if z.val % 2 ^ (k.val + 2) = 0 then 1 else 0
      have hcancel : g z1 + g z2 + g z1 + g z2 = 0 := zmod2_four_univariate_z g z1 z2
      have hre : (borrowBit (k.val + 1) (halfFin w1).val (halfFin (thetaMinus z1)).val + g z1) +
          (borrowBit (k.val + 1) (halfFin w1).val (halfFin (thetaMinus z2)).val + g z2) +
          (borrowBit (k.val + 1) (halfFin w2).val (halfFin (thetaMinus z1)).val + g z1) +
          (borrowBit (k.val + 1) (halfFin w2).val (halfFin (thetaMinus z2)).val + g z2) =
          (borrowBit (k.val + 1) (halfFin w1).val (halfFin (thetaMinus z1)).val +
           borrowBit (k.val + 1) (halfFin w1).val (halfFin (thetaMinus z2)).val +
           borrowBit (k.val + 1) (halfFin w2).val (halfFin (thetaMinus z1)).val +
           borrowBit (k.val + 1) (halfFin w2).val (halfFin (thetaMinus z2)).val) +
          (g z1 + g z2 + g z1 + g z2) := by abel
      rw [hre, hcancel, add_zero] at hk
      exact hk
    · intro h
      funext i
      refine Fin.cases ?_ (fun k => ?_) i
      · simp only [Pi.add_apply, Pi.zero_apply, borrowVec, borrowBit, Fin.val_zero, zero_add,
          pow_one, hW w1 hw1, hW w2 hw2]
        exact zmod2_four_univariate_z (fun z : Fin (2 ^ (s + 1)) => if z.val % 2 < 1 then 1 else 0) z1 z2
      · have hk := congrFun h k
        simp only [Pi.add_apply, Pi.zero_apply, borrowVec, Fin.val_succ] at hk ⊢
        rw [ew1, ew2, borrowBit_case1b k.isLt, borrowBit_case1b k.isLt,
            borrowBit_case1b k.isLt, borrowBit_case1b k.isLt]
        set g : Fin (2 ^ (s + 1)) → ZMod 2 := fun z => if z.val % 2 ^ (k.val + 2) = 0 then 1 else 0
        have hcancel : g z1 + g z2 + g z1 + g z2 = 0 := zmod2_four_univariate_z g z1 z2
        calc (borrowBit (k.val + 1) (halfFin w1).val (halfFin (thetaMinus z1)).val + g z1) +
             (borrowBit (k.val + 1) (halfFin w1).val (halfFin (thetaMinus z2)).val + g z2) +
             (borrowBit (k.val + 1) (halfFin w2).val (halfFin (thetaMinus z1)).val + g z1) +
             (borrowBit (k.val + 1) (halfFin w2).val (halfFin (thetaMinus z2)).val + g z2)
            = (borrowBit (k.val + 1) (halfFin w1).val (halfFin (thetaMinus z1)).val +
               borrowBit (k.val + 1) (halfFin w1).val (halfFin (thetaMinus z2)).val +
               borrowBit (k.val + 1) (halfFin w2).val (halfFin (thetaMinus z1)).val +
               borrowBit (k.val + 1) (halfFin w2).val (halfFin (thetaMinus z2)).val) +
              (g z1 + g z2 + g z1 + g z2) := by abel
          _ = 0 := by rw [hk, hcancel, add_zero]
  constructor
  · intro h w1' hw1' w2' hw2' z1' hz1' z2' hz2'
    simp only [Finset.mem_image] at hw1' hw2' hz1' hz2'
    rcases hw1' with ⟨w1, hw1, rfl⟩; rcases hw2' with ⟨w2, hw2, rfl⟩
    rcases hz1' with ⟨z1, hz1, rfl⟩; rcases hz2' with ⟨z2, hz2, rfl⟩
    exact (hstep w1 hw1 w2 hw2 z1 hz1 z2 hz2).mp (h w1 hw1 w2 hw2 z1 hz1 z2 hz2)
  · intro h w1 hw1 w2 hw2 z1 hz1 z2 hz2
    exact (hstep w1 hw1 w2 hw2 z1 hz1 z2 hz2).mpr
      (h _ (Finset.mem_image_of_mem _ hw1) _ (Finset.mem_image_of_mem _ hw2)
         _ (Finset.mem_image_of_mem _ hz1) _ (Finset.mem_image_of_mem _ hz2))

lemma cocycle_case2a_iff {s : ℕ} {W Z : Finset (Fin (2 ^ (s + 1)))}
    (hZ : ∀ z ∈ Z, z.val % 2 = 1) :
    IsCocycleValid (s + 1) W Z ↔ IsCocycleValid s (W.image halfFin) (Z.image halfFin) := by
  have hstep : ∀ w1 ∈ W, ∀ w2 ∈ W, ∀ z1 ∈ Z, ∀ z2 ∈ Z,
      (borrowVec (s + 1) w1 z1 + borrowVec (s + 1) w1 z2 +
       borrowVec (s + 1) w2 z1 + borrowVec (s + 1) w2 z2 = 0) ↔
      (borrowVec s (halfFin w1) (halfFin z1) + borrowVec s (halfFin w1) (halfFin z2) +
       borrowVec s (halfFin w2) (halfFin z1) + borrowVec s (halfFin w2) (halfFin z2) = 0) := by
    intro w1 _ w2 _ z1 hz1 z2 hz2
    have ez1 : z1.val = 2 * (halfFin z1).val + 1 := by
      have := hZ z1 hz1; simp [halfFin]; omega
    have ez2 : z2.val = 2 * (halfFin z2).val + 1 := by
      have := hZ z2 hz2; simp [halfFin]; omega
    constructor
    · intro h
      funext k
      have hk := congrFun h k.succ
      simp only [Pi.add_apply, Pi.zero_apply, borrowVec, Fin.val_succ] at hk ⊢
      rw [ez1, ez2, borrowBit_case2a, borrowBit_case2a, borrowBit_case2a, borrowBit_case2a] at hk
      exact hk
    · intro h
      funext i
      refine Fin.cases ?_ (fun k => ?_) i
      · simp only [Pi.add_apply, Pi.zero_apply, borrowVec, borrowBit, Fin.val_zero, zero_add,
          pow_one, hZ z1 hz1, hZ z2 hz2]
        have h1 : ¬ (1 < w1.val % 2) := by have := Nat.mod_lt w1.val (by omega : 0 < 2); omega
        have h2 : ¬ (1 < w2.val % 2) := by have := Nat.mod_lt w2.val (by omega : 0 < 2); omega
        simp [h1, h2]
      · have hk := congrFun h k
        simp only [Pi.add_apply, Pi.zero_apply, borrowVec, Fin.val_succ] at hk ⊢
        rw [ez1, ez2, borrowBit_case2a, borrowBit_case2a, borrowBit_case2a, borrowBit_case2a]
        exact hk
  constructor
  · intro h w1' hw1' w2' hw2' z1' hz1' z2' hz2'
    simp only [Finset.mem_image] at hw1' hw2' hz1' hz2'
    rcases hw1' with ⟨w1, hw1, rfl⟩; rcases hw2' with ⟨w2, hw2, rfl⟩
    rcases hz1' with ⟨z1, hz1, rfl⟩; rcases hz2' with ⟨z2, hz2, rfl⟩
    exact (hstep w1 hw1 w2 hw2 z1 hz1 z2 hz2).mp (h w1 hw1 w2 hw2 z1 hz1 z2 hz2)
  · intro h w1 hw1 w2 hw2 z1 hz1 z2 hz2
    exact (hstep w1 hw1 w2 hw2 z1 hz1 z2 hz2).mpr
      (h _ (Finset.mem_image_of_mem _ hw1) _ (Finset.mem_image_of_mem _ hw2)
         _ (Finset.mem_image_of_mem _ hz1) _ (Finset.mem_image_of_mem _ hz2))

lemma cocycle_case2b_iff {s : ℕ} {W Z : Finset (Fin (2 ^ (s + 1)))}
    (hZ : ∀ z ∈ Z, z.val % 2 = 0) :
    IsCocycleValid (s + 1) W Z ↔
      IsCocycleValid s (W.image fun w => halfFin (thetaPlus w)) (Z.image halfFin) := by
  have hstep : ∀ w1 ∈ W, ∀ w2 ∈ W, ∀ z1 ∈ Z, ∀ z2 ∈ Z,
      (borrowVec (s + 1) w1 z1 + borrowVec (s + 1) w1 z2 +
       borrowVec (s + 1) w2 z1 + borrowVec (s + 1) w2 z2 = 0) ↔
      (borrowVec s (halfFin (thetaPlus w1)) (halfFin z1) +
       borrowVec s (halfFin (thetaPlus w1)) (halfFin z2) +
       borrowVec s (halfFin (thetaPlus w2)) (halfFin z1) +
       borrowVec s (halfFin (thetaPlus w2)) (halfFin z2) = 0) := by
    intro w1 _ w2 _ z1 hz1 z2 hz2
    have ez1 : z1 = embEven (halfFin z1) := (embEven_halfFin (hZ z1 hz1)).symm
    have ez2 : z2 = embEven (halfFin z2) := (embEven_halfFin (hZ z2 hz2)).symm
    constructor
    · intro h
      funext k
      have hk := congrFun h k.succ
      simp only [Pi.add_apply, Pi.zero_apply, borrowVec, Fin.val_succ] at hk ⊢
      rw [ez1, ez2, borrowBit_case2b k.isLt, borrowBit_case2b k.isLt,
          borrowBit_case2b k.isLt, borrowBit_case2b k.isLt] at hk
      set g : Fin (2 ^ (s + 1)) → ZMod 2 :=
        fun w => if w.val % 2 ^ (k.val + 2) = 2 ^ (k.val + 2) - 1 then 1 else 0
      have hcancel : g w1 + g w1 + g w2 + g w2 = 0 := zmod2_four_univariate_w g w1 w2
      have hre : (borrowBit (k.val + 1) (halfFin (thetaPlus w1)).val (halfFin z1).val + g w1) +
          (borrowBit (k.val + 1) (halfFin (thetaPlus w1)).val (halfFin z2).val + g w1) +
          (borrowBit (k.val + 1) (halfFin (thetaPlus w2)).val (halfFin z1).val + g w2) +
          (borrowBit (k.val + 1) (halfFin (thetaPlus w2)).val (halfFin z2).val + g w2) =
          (borrowBit (k.val + 1) (halfFin (thetaPlus w1)).val (halfFin z1).val +
           borrowBit (k.val + 1) (halfFin (thetaPlus w1)).val (halfFin z2).val +
           borrowBit (k.val + 1) (halfFin (thetaPlus w2)).val (halfFin z1).val +
           borrowBit (k.val + 1) (halfFin (thetaPlus w2)).val (halfFin z2).val) +
          (g w1 + g w1 + g w2 + g w2) := by abel
      rw [hre, hcancel, add_zero] at hk
      exact hk
    · intro h
      funext i
      refine Fin.cases ?_ (fun k => ?_) i
      · simp only [Pi.add_apply, Pi.zero_apply, borrowVec, borrowBit, Fin.val_zero, zero_add,
          pow_one, hZ z1 hz1, hZ z2 hz2]
        exact zmod2_four_univariate_w (fun w : Fin (2 ^ (s + 1)) => if 0 < w.val % 2 then 1 else 0) w1 w2
      · have hk := congrFun h k
        simp only [Pi.add_apply, Pi.zero_apply, borrowVec, Fin.val_succ] at hk ⊢
        rw [ez1, ez2, borrowBit_case2b k.isLt, borrowBit_case2b k.isLt,
            borrowBit_case2b k.isLt, borrowBit_case2b k.isLt]
        set g : Fin (2 ^ (s + 1)) → ZMod 2 :=
          fun w => if w.val % 2 ^ (k.val + 2) = 2 ^ (k.val + 2) - 1 then 1 else 0
        have hcancel : g w1 + g w1 + g w2 + g w2 = 0 := zmod2_four_univariate_w g w1 w2
        calc (borrowBit (k.val + 1) (halfFin (thetaPlus w1)).val (halfFin z1).val + g w1) +
             (borrowBit (k.val + 1) (halfFin (thetaPlus w1)).val (halfFin z2).val + g w1) +
             (borrowBit (k.val + 1) (halfFin (thetaPlus w2)).val (halfFin z1).val + g w2) +
             (borrowBit (k.val + 1) (halfFin (thetaPlus w2)).val (halfFin z2).val + g w2)
            = (borrowBit (k.val + 1) (halfFin (thetaPlus w1)).val (halfFin z1).val +
               borrowBit (k.val + 1) (halfFin (thetaPlus w1)).val (halfFin z2).val +
               borrowBit (k.val + 1) (halfFin (thetaPlus w2)).val (halfFin z1).val +
               borrowBit (k.val + 1) (halfFin (thetaPlus w2)).val (halfFin z2).val) +
              (g w1 + g w1 + g w2 + g w2) := by abel
          _ = 0 := by rw [hk, hcancel, add_zero]
  constructor
  · intro h w1' hw1' w2' hw2' z1' hz1' z2' hz2'
    simp only [Finset.mem_image] at hw1' hw2' hz1' hz2'
    rcases hw1' with ⟨w1, hw1, rfl⟩; rcases hw2' with ⟨w2, hw2, rfl⟩
    rcases hz1' with ⟨z1, hz1, rfl⟩; rcases hz2' with ⟨z2, hz2, rfl⟩
    exact (hstep w1 hw1 w2 hw2 z1 hz1 z2 hz2).mp (h w1 hw1 w2 hw2 z1 hz1 z2 hz2)
  · intro h w1 hw1 w2 hw2 z1 hz1 z2 hz2
    exact (hstep w1 hw1 w2 hw2 z1 hz1 z2 hz2).mpr
      (h _ (Finset.mem_image_of_mem _ hw1) _ (Finset.mem_image_of_mem _ hw2)
         _ (Finset.mem_image_of_mem _ hz1) _ (Finset.mem_image_of_mem _ hz2))

/-- The four inductive constructors lifting an `s`-bit pair `(W, Z)` to an `(s+1)`-bit pair. -/
def stepMaxPair (s : ℕ) :
    Fin 4 × (Finset (Fin (2 ^ s)) × Finset (Fin (2 ^ s))) →
      Finset (Fin (2 ^ (s + 1))) × Finset (Fin (2 ^ (s + 1)))
  | (⟨0, _⟩, (W, Z)) => (W.image embEven, Finset.univ.filter fun z => halfFin z ∈ Z)
  | (⟨1, _⟩, (W, Z)) => (W.image embOdd, Finset.univ.filter fun z => halfFin (thetaMinus z) ∈ Z)
  | (⟨2, _⟩, (W, Z)) => (Finset.univ.filter fun w => halfFin w ∈ W, Z.image embOdd)
  | (⟨3, _⟩, (W, Z)) => (Finset.univ.filter fun w => halfFin (thetaPlus w) ∈ W, Z.image embEven)

lemma stepMaxPair_hasBothParities_right {s : ℕ} {W Z : Finset (Fin (2 ^ s))}
    (hZ : Z.Nonempty) :
    (∃ ze ∈ (stepMaxPair s (0, (W, Z))).2, ze.val % 2 = 0) ∧
    (∃ zo ∈ (stepMaxPair s (0, (W, Z))).2, zo.val % 2 = 1) ∧
    (∃ ze ∈ (stepMaxPair s (1, (W, Z))).2, ze.val % 2 = 0) ∧
    (∃ zo ∈ (stepMaxPair s (1, (W, Z))).2, zo.val % 2 = 1) := by
  rcases hZ with ⟨z0, hz0⟩
  have h2dvd : 2 ∣ 2 ^ (s + 1) := dvd_pow_self 2 (by omega)
  refine ⟨⟨embEven z0, ?_, by simp [embEven]⟩,
          ⟨embOdd z0, ?_, by simp [embOdd]⟩,
          ⟨thetaPlus (embOdd z0), ?_, ?_⟩,
          ⟨thetaPlus (embEven z0), ?_, ?_⟩⟩
  · simp [stepMaxPair, halfFin_embEven, hz0]
  · simp [stepMaxPair, halfFin_embOdd, hz0]
  · simp [stepMaxPair, thetaMinus_thetaPlus, halfFin_embOdd, hz0]
  · simp only [thetaPlus, embOdd]
    rw [Nat.mod_mod_of_dvd _ h2dvd]; omega
  · simp [stepMaxPair, thetaMinus_thetaPlus, halfFin_embEven, hz0]
  · simp only [thetaPlus, embEven]
    rw [Nat.mod_mod_of_dvd _ h2dvd]; omega

lemma stepMaxPair_hasBothParities_left {s : ℕ} {W Z : Finset (Fin (2 ^ s))}
    (hW : W.Nonempty) :
    (∃ we ∈ (stepMaxPair s (2, (W, Z))).1, we.val % 2 = 0) ∧
    (∃ wo ∈ (stepMaxPair s (2, (W, Z))).1, wo.val % 2 = 1) ∧
    (∃ we ∈ (stepMaxPair s (3, (W, Z))).1, we.val % 2 = 0) ∧
    (∃ wo ∈ (stepMaxPair s (3, (W, Z))).1, wo.val % 2 = 1) := by
  rcases hW with ⟨w0, hw0⟩
  have h2dvd : 2 ∣ 2 ^ (s + 1) := dvd_pow_self 2 (by omega)
  have hpos : 2 ≤ 2 ^ (s + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (s + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  refine ⟨⟨embEven w0, ?_, by simp [embEven]⟩,
          ⟨embOdd w0, ?_, by simp [embOdd]⟩,
          ⟨thetaMinus (embOdd w0), ?_, ?_⟩,
          ⟨thetaMinus (embEven w0), ?_, ?_⟩⟩
  · simp [stepMaxPair, halfFin_embEven, hw0]
  · simp [stepMaxPair, halfFin_embOdd, hw0]
  · simp [stepMaxPair, thetaPlus_thetaMinus, halfFin_embOdd, hw0]
  · simp only [thetaMinus, embOdd]
    rw [Nat.mod_mod_of_dvd _ h2dvd]
    have hmod2 : 2 ^ (s + 1) % 2 = 0 := Nat.mod_eq_zero_of_dvd h2dvd
    omega
  · simp [stepMaxPair, thetaPlus_thetaMinus, halfFin_embEven, hw0]
  · simp only [thetaMinus, embEven]
    rw [Nat.mod_mod_of_dvd _ h2dvd]
    have hmod2 : 2 ^ (s + 1) % 2 = 0 := Nat.mod_eq_zero_of_dvd h2dvd
    omega

lemma stepMaxPair_isMaximal (s : ℕ) (c : Fin 4) {W Z : Finset (Fin (2 ^ s))}
    (hmax : IsMaximalCocyclePair s W Z) :
    IsMaximalCocyclePair (s + 1) (stepMaxPair s (c, (W, Z))).1 (stepMaxPair s (c, (W, Z))).2 := by
  rcases hmax with ⟨⟨hWne, hZne, hcoc⟩, hmaxim⟩
  fin_cases c
  · -- Case 1a (c = 0)
    dsimp only [stepMaxPair]
    have hWall : ∀ w ∈ W.image embEven, w.val % 2 = 0 := by
      intro w hw; rcases Finset.mem_image.mp hw with ⟨a, _, rfl⟩; simp [embEven]
    have hWimg : (W.image embEven).image halfFin = W := by
      ext a; simp [halfFin_embEven]
    have hZimg : (Finset.univ.filter fun z => halfFin z ∈ Z).image halfFin = Z :=
      image_halfFin_filter_halfFin Z
    have hcoc' : IsCocycleValid (s + 1) (W.image embEven)
        (Finset.univ.filter fun z => halfFin z ∈ Z) := by
      rw [cocycle_case1a_iff hWall, hWimg, hZimg]; exact hcoc
    have hpar := stepMaxPair_hasBothParities_right (W := W) hZne
    refine ⟨⟨hWne.image _, ⟨hpar.1.choose, hpar.1.choose_spec.1⟩, hcoc'⟩, ?_⟩
    intro W' Z' hcocW' hWW' hZZ'
    have hW'even : ∀ w ∈ W', w.val % 2 = 0 := by
      intro w hw
      by_contra hne
      have hodd : w.val % 2 = 1 := by omega
      rcases hWne with ⟨w0, hw0⟩
      exact cocycle_parity_obstruction hcocW'
        (hWW' (Finset.mem_image_of_mem _ hw0)) hw
        (hZZ' hpar.1.choose_spec.1) (hZZ' hpar.2.1.choose_spec.1)
        (by simp [embEven]) hodd hpar.1.choose_spec.2 hpar.2.1.choose_spec.2
    have hcoc_sub : IsCocycleValid s (W'.image halfFin) (Z'.image halfFin) :=
      (cocycle_case1a_iff hW'even).mp hcocW'
    have hWsub : W ⊆ W'.image halfFin := by rw [← hWimg]; exact Finset.image_subset_image hWW'
    have hZsub : Z ⊆ Z'.image halfFin := by rw [← hZimg]; exact Finset.image_subset_image hZZ'
    have ⟨hW'eq, hZ'eq⟩ := hmaxim _ _ hcoc_sub hWsub hZsub
    constructor
    · ext x
      constructor
      · intro hx
        have hmem : halfFin x ∈ W := by rw [← hW'eq]; exact Finset.mem_image_of_mem _ hx
        exact Finset.mem_image.mpr ⟨halfFin x, hmem, embEven_halfFin (hW'even x hx)⟩
      · exact fun hx => hWW' hx
    · ext z
      constructor
      · intro hz
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by rw [← hZ'eq]; exact Finset.mem_image_of_mem _ hz⟩
      · exact fun hz => hZZ' hz
  · -- Case 1b (c = 1)
    dsimp only [stepMaxPair]
    have hWall : ∀ w ∈ W.image embOdd, w.val % 2 = 1 := by
      intro w hw; rcases Finset.mem_image.mp hw with ⟨a, _, rfl⟩; simp [embOdd]
    have hWimg : (W.image embOdd).image halfFin = W := by
      ext a; simp [halfFin_embOdd]
    have hZimg : (Finset.univ.filter fun z => halfFin (thetaMinus z) ∈ Z).image
        (fun z => halfFin (thetaMinus z)) = Z := image_halfFin_thetaMinus_filter Z
    have hcoc' : IsCocycleValid (s + 1) (W.image embOdd)
        (Finset.univ.filter fun z => halfFin (thetaMinus z) ∈ Z) := by
      rw [cocycle_case1b_iff hWall, hWimg, hZimg]; exact hcoc
    have hpar := stepMaxPair_hasBothParities_right (W := W) hZne
    refine ⟨⟨hWne.image _, ⟨hpar.2.2.1.choose, hpar.2.2.1.choose_spec.1⟩, hcoc'⟩, ?_⟩
    intro W' Z' hcocW' hWW' hZZ'
    have hW'odd : ∀ w ∈ W', w.val % 2 = 1 := by
      intro w hw
      by_contra hne
      have heven : w.val % 2 = 0 := by omega
      rcases hWne with ⟨w0, hw0⟩
      exact cocycle_parity_obstruction hcocW'
        hw (hWW' (Finset.mem_image_of_mem _ hw0))
        (hZZ' hpar.2.2.1.choose_spec.1) (hZZ' hpar.2.2.2.choose_spec.1)
        heven (by simp [embOdd]) hpar.2.2.1.choose_spec.2 hpar.2.2.2.choose_spec.2
    have hcoc_sub : IsCocycleValid s (W'.image halfFin)
        (Z'.image fun z => halfFin (thetaMinus z)) :=
      (cocycle_case1b_iff hW'odd).mp hcocW'
    have hWsub : W ⊆ W'.image halfFin := by rw [← hWimg]; exact Finset.image_subset_image hWW'
    have hZsub : Z ⊆ Z'.image fun z => halfFin (thetaMinus z) := by
      rw [← hZimg]; exact Finset.image_subset_image hZZ'
    have ⟨hW'eq, hZ'eq⟩ := hmaxim _ _ hcoc_sub hWsub hZsub
    constructor
    · ext x
      constructor
      · intro hx
        have hmem : halfFin x ∈ W := by rw [← hW'eq]; exact Finset.mem_image_of_mem _ hx
        exact Finset.mem_image.mpr ⟨halfFin x, hmem, embOdd_halfFin (hW'odd x hx)⟩
      · exact fun hx => hWW' hx
    · ext z
      constructor
      · intro hz
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by rw [← hZ'eq]; exact Finset.mem_image_of_mem _ hz⟩
      · exact fun hz => hZZ' hz
  · -- Case 2a (c = 2)
    dsimp only [stepMaxPair]
    have hZall : ∀ z ∈ Z.image embOdd, z.val % 2 = 1 := by
      intro z hz; rcases Finset.mem_image.mp hz with ⟨a, _, rfl⟩; simp [embOdd]
    have hZimg : (Z.image embOdd).image halfFin = Z := by
      ext a; simp [halfFin_embOdd]
    have hWimg : (Finset.univ.filter fun w => halfFin w ∈ W).image halfFin = W :=
      image_halfFin_filter_halfFin W
    have hcoc' : IsCocycleValid (s + 1)
        (Finset.univ.filter fun w => halfFin w ∈ W) (Z.image embOdd) := by
      rw [cocycle_case2a_iff hZall, hWimg, hZimg]; exact hcoc
    have hpar := stepMaxPair_hasBothParities_left (Z := Z) hWne
    refine ⟨⟨⟨hpar.1.choose, hpar.1.choose_spec.1⟩, hZne.image _, hcoc'⟩, ?_⟩
    intro W' Z' hcocW' hWW' hZZ'
    have hZ'odd : ∀ z ∈ Z', z.val % 2 = 1 := by
      intro z hz
      by_contra hne
      have heven : z.val % 2 = 0 := by omega
      rcases hZne with ⟨z0, hz0⟩
      exact cocycle_parity_obstruction hcocW'
        (hWW' hpar.1.choose_spec.1) (hWW' hpar.2.1.choose_spec.1)
        hz (hZZ' (Finset.mem_image_of_mem _ hz0))
        hpar.1.choose_spec.2 hpar.2.1.choose_spec.2 heven (by simp [embOdd])
    have hcoc_sub : IsCocycleValid s (W'.image halfFin) (Z'.image halfFin) :=
      (cocycle_case2a_iff hZ'odd).mp hcocW'
    have hWsub : W ⊆ W'.image halfFin := by rw [← hWimg]; exact Finset.image_subset_image hWW'
    have hZsub : Z ⊆ Z'.image halfFin := by rw [← hZimg]; exact Finset.image_subset_image hZZ'
    have ⟨hW'eq, hZ'eq⟩ := hmaxim _ _ hcoc_sub hWsub hZsub
    constructor
    · ext w
      constructor
      · intro hw
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by rw [← hW'eq]; exact Finset.mem_image_of_mem _ hw⟩
      · exact fun hw => hWW' hw
    · ext z
      constructor
      · intro hz
        have hmem : halfFin z ∈ Z := by rw [← hZ'eq]; exact Finset.mem_image_of_mem _ hz
        exact Finset.mem_image.mpr ⟨halfFin z, hmem, embOdd_halfFin (hZ'odd z hz)⟩
      · exact fun hz => hZZ' hz
  · -- Case 2b (c = 3)
    dsimp only [stepMaxPair]
    have hZall : ∀ z ∈ Z.image embEven, z.val % 2 = 0 := by
      intro z hz; rcases Finset.mem_image.mp hz with ⟨a, _, rfl⟩; simp [embEven]
    have hZimg : (Z.image embEven).image halfFin = Z := by
      ext a; simp [halfFin_embEven]
    have hWimg : (Finset.univ.filter fun w => halfFin (thetaPlus w) ∈ W).image
        (fun w => halfFin (thetaPlus w)) = W := image_halfFin_thetaPlus_filter W
    have hcoc' : IsCocycleValid (s + 1)
        (Finset.univ.filter fun w => halfFin (thetaPlus w) ∈ W) (Z.image embEven) := by
      rw [cocycle_case2b_iff hZall, hWimg, hZimg]; exact hcoc
    have hpar := stepMaxPair_hasBothParities_left (Z := Z) hWne
    refine ⟨⟨⟨hpar.2.2.1.choose, hpar.2.2.1.choose_spec.1⟩, hZne.image _, hcoc'⟩, ?_⟩
    intro W' Z' hcocW' hWW' hZZ'
    have hZ'even : ∀ z ∈ Z', z.val % 2 = 0 := by
      intro z hz
      by_contra hne
      have hodd : z.val % 2 = 1 := by omega
      rcases hZne with ⟨z0, hz0⟩
      exact cocycle_parity_obstruction hcocW'
        (hWW' hpar.2.2.1.choose_spec.1) (hWW' hpar.2.2.2.choose_spec.1)
        (hZZ' (Finset.mem_image_of_mem _ hz0)) hz
        hpar.2.2.1.choose_spec.2 hpar.2.2.2.choose_spec.2 (by simp [embEven]) hodd
    have hcoc_sub : IsCocycleValid s (W'.image fun w => halfFin (thetaPlus w))
        (Z'.image halfFin) :=
      (cocycle_case2b_iff hZ'even).mp hcocW'
    have hWsub : W ⊆ W'.image fun w => halfFin (thetaPlus w) := by
      rw [← hWimg]; exact Finset.image_subset_image hWW'
    have hZsub : Z ⊆ Z'.image halfFin := by rw [← hZimg]; exact Finset.image_subset_image hZZ'
    have ⟨hW'eq, hZ'eq⟩ := hmaxim _ _ hcoc_sub hWsub hZsub
    constructor
    · ext w
      constructor
      · intro hw
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by rw [← hW'eq]; exact Finset.mem_image_of_mem _ hw⟩
      · exact fun hw => hWW' hw
    · ext z
      constructor
      · intro hz
        have hmem : halfFin z ∈ Z := by rw [← hZ'eq]; exact Finset.mem_image_of_mem _ hz
        exact Finset.mem_image.mpr ⟨halfFin z, hmem, embEven_halfFin (hZ'even z hz)⟩
      · exact fun hz => hZZ' hz

lemma stepMaxPair_injective_on_max (s : ℕ) :
    ∀ c1 c2 : Fin 4, ∀ p1 p2 : Finset (Fin (2 ^ s)) × Finset (Fin (2 ^ s)),
      IsMaximalCocyclePair s p1.1 p1.2 → IsMaximalCocyclePair s p2.1 p2.2 →
      stepMaxPair s (c1, p1) = stepMaxPair s (c2, p2) → c1 = c2 ∧ p1 = p2 := by
  intro c1 c2 ⟨W1, Z1⟩ ⟨W2, Z2⟩ h1 h2 heq
  have hW1 := h1.1.1; have hZ1 := h1.1.2.1
  have hW2 := h2.1.1; have hZ2 := h2.1.2.1
  have heq1 := congrArg Prod.fst heq
  have heq2 := congrArg Prod.snd heq
  have h1a_e : ∀ w ∈ (stepMaxPair s (0, (W1, Z1))).1, w.val % 2 = 0 := by
    intro w hw; rcases Finset.mem_image.mp hw with ⟨a, _, rfl⟩; simp [embEven]
  have h1b_o : ∀ w ∈ (stepMaxPair s (1, (W1, Z1))).1, w.val % 2 = 1 := by
    intro w hw; rcases Finset.mem_image.mp hw with ⟨a, _, rfl⟩; simp [embOdd]
  have h2a_o : ∀ z ∈ (stepMaxPair s (2, (W1, Z1))).2, z.val % 2 = 1 := by
    intro z hz; rcases Finset.mem_image.mp hz with ⟨a, _, rfl⟩; simp [embOdd]
  have h2b_e : ∀ z ∈ (stepMaxPair s (3, (W1, Z1))).2, z.val % 2 = 0 := by
    intro z hz; rcases Finset.mem_image.mp hz with ⟨a, _, rfl⟩; simp [embEven]
  have hpR2 := stepMaxPair_hasBothParities_right (W := W2) hZ2
  have hpL2 := stepMaxPair_hasBothParities_left (Z := Z2) hW2
  fin_cases c1 <;> fin_cases c2
  · refine ⟨rfl, Prod.ext ?_ ?_⟩
    · have h := congrArg (Finset.image halfFin) heq1
      simpa [stepMaxPair, Finset.image_image, Function.comp_def, halfFin_embEven] using h
    · have h := congrArg (Finset.image halfFin) heq2
      simpa [stepMaxPair, image_halfFin_filter_halfFin] using h
  · exfalso; rcases hW1 with ⟨a, ha⟩
    have heq1' : W1.image embEven = W2.image embOdd := heq1
    have hmem : embEven a ∈ W2.image embOdd := by rw [← heq1']; exact Finset.mem_image_of_mem _ ha
    rcases Finset.mem_image.mp hmem with ⟨b, _, h⟩
    have := congrArg Fin.val h; simp [embEven, embOdd] at this; omega
  · exfalso; rcases hpL2.2.1 with ⟨wo, hwo, hodd⟩
    have heq1' : (stepMaxPair s (0, (W1, Z1))).1 = (stepMaxPair s (2, (W2, Z2))).1 := heq1
    rw [← heq1'] at hwo
    have := h1a_e wo hwo; omega
  · exfalso; rcases hpL2.2.2.2 with ⟨wo, hwo, hodd⟩
    have heq1' : (stepMaxPair s (0, (W1, Z1))).1 = (stepMaxPair s (3, (W2, Z2))).1 := heq1
    rw [← heq1'] at hwo
    have := h1a_e wo hwo; omega
  · exfalso; rcases hW2 with ⟨a, ha⟩
    have heq1' : (stepMaxPair s (1, (W1, Z1))).1 = W2.image embEven := heq1
    have hmem : embEven a ∈ (stepMaxPair s (1, (W1, Z1))).1 := by
      rw [heq1']; exact Finset.mem_image_of_mem _ ha
    have := h1b_o (embEven a) hmem; simp [embEven] at this
  · refine ⟨rfl, Prod.ext ?_ ?_⟩
    · have h := congrArg (Finset.image halfFin) heq1
      simpa [stepMaxPair, Finset.image_image, Function.comp_def, halfFin_embOdd] using h
    · have h := congrArg (Finset.image fun z => halfFin (thetaMinus z)) heq2
      simpa [stepMaxPair, image_halfFin_thetaMinus_filter] using h
  · exfalso; rcases hpL2.1 with ⟨we, hwe, hev⟩
    have heq1' : (stepMaxPair s (1, (W1, Z1))).1 = (stepMaxPair s (2, (W2, Z2))).1 := heq1
    rw [← heq1'] at hwe
    have := h1b_o we hwe; omega
  · exfalso; rcases hpL2.2.2.1 with ⟨we, hwe, hev⟩
    have heq1' : (stepMaxPair s (1, (W1, Z1))).1 = (stepMaxPair s (3, (W2, Z2))).1 := heq1
    rw [← heq1'] at hwe
    have := h1b_o we hwe; omega
  · exfalso; rcases hpR2.1 with ⟨ze, hze, hev⟩
    have heq2' : (stepMaxPair s (2, (W1, Z1))).2 = (stepMaxPair s (0, (W2, Z2))).2 := heq2
    rw [← heq2'] at hze
    have := h2a_o ze hze; omega
  · exfalso; rcases hpR2.2.2.1 with ⟨ze, hze, hev⟩
    have heq2' : (stepMaxPair s (2, (W1, Z1))).2 = (stepMaxPair s (1, (W2, Z2))).2 := heq2
    rw [← heq2'] at hze
    have := h2a_o ze hze; omega
  · refine ⟨rfl, Prod.ext ?_ ?_⟩
    · have h := congrArg (Finset.image halfFin) heq1
      simpa [stepMaxPair, image_halfFin_filter_halfFin] using h
    · have h := congrArg (Finset.image halfFin) heq2
      simpa [stepMaxPair, Finset.image_image, Function.comp_def, halfFin_embOdd] using h
  · exfalso; rcases hZ2 with ⟨a, ha⟩
    have heq2' : (stepMaxPair s (2, (W1, Z1))).2 = Z2.image embEven := heq2
    have hmem : embEven a ∈ (stepMaxPair s (2, (W1, Z1))).2 := by
      rw [heq2']; exact Finset.mem_image_of_mem _ ha
    have := h2a_o (embEven a) hmem; simp [embEven] at this
  · exfalso; rcases hpR2.2.1 with ⟨zo, hzo, hodd⟩
    have heq2' : (stepMaxPair s (3, (W1, Z1))).2 = (stepMaxPair s (0, (W2, Z2))).2 := heq2
    rw [← heq2'] at hzo
    have := h2b_e zo hzo; omega
  · exfalso; rcases hpR2.2.2.2 with ⟨zo, hzo, hodd⟩
    have heq2' : (stepMaxPair s (3, (W1, Z1))).2 = (stepMaxPair s (1, (W2, Z2))).2 := heq2
    rw [← heq2'] at hzo
    have := h2b_e zo hzo; omega
  · exfalso; rcases hZ1 with ⟨a, ha⟩
    have heq2' : Z1.image embEven = Z2.image embOdd := heq2
    have hmem : embEven a ∈ Z2.image embOdd := by rw [← heq2']; exact Finset.mem_image_of_mem _ ha
    rcases Finset.mem_image.mp hmem with ⟨b, _, h⟩
    have := congrArg Fin.val h; simp [embEven, embOdd] at this; omega
  · refine ⟨rfl, Prod.ext ?_ ?_⟩
    · have h := congrArg (Finset.image fun w => halfFin (thetaPlus w)) heq1
      simpa [stepMaxPair, image_halfFin_thetaPlus_filter] using h
    · have h := congrArg (Finset.image halfFin) heq2
      simpa [stepMaxPair, Finset.image_image, Function.comp_def, halfFin_embEven] using h

lemma stepMaxPair_surjective_on_max (s : ℕ) {W' Z' : Finset (Fin (2 ^ (s + 1)))}
    (hmax : IsMaximalCocyclePair (s + 1) W' Z') :
    ∃ (c : Fin 4) (p : Finset (Fin (2 ^ s)) × Finset (Fin (2 ^ s))),
      IsMaximalCocyclePair s p.1 p.2 ∧ stepMaxPair s (c, p) = (W', Z') := by
  rcases hmax with ⟨⟨hWne, hZne, hcoc⟩, hmaxim⟩
  have hcase : (∀ w ∈ W', w.val % 2 = 0) ∨ (∀ w ∈ W', w.val % 2 = 1) ∨
      (∀ z ∈ Z', z.val % 2 = 1) ∨ (∀ z ∈ Z', z.val % 2 = 0) := by
    by_contra h
    push Not at h
    rcases h with ⟨⟨wo, hwo, hwo_ne⟩, ⟨we, hwe, hwe_ne⟩, ⟨ze, hze, hze_ne⟩, ⟨zo, hzo, hzo_ne⟩⟩
    exact cocycle_parity_obstruction hcoc hwe hwo hze hzo
      (by omega) (by omega) (by omega) (by omega)
  rcases hcase with hWe | hWo | hZo | hZe
  · -- Case 1a
    let W := W'.image halfFin
    let Z := Z'.image halfFin
    have hW'eq : W' = W.image embEven := by
      ext x; simp only [W, Finset.mem_image]
      constructor
      · intro hx; exact ⟨halfFin x, ⟨x, hx, rfl⟩, embEven_halfFin (hWe x hx)⟩
      · rintro ⟨a, ⟨y, hy, rfl⟩, rfl⟩; rwa [embEven_halfFin (hWe y hy)]
    have hcoc_sub : IsCocycleValid s W Z := (cocycle_case1a_iff hWe).mp hcoc
    have hZ'sub : Z' ⊆ Finset.univ.filter fun z => halfFin z ∈ Z := by
      intro z hz; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, Finset.mem_image_of_mem _ hz⟩
    have hcoc_ext : IsCocycleValid (s + 1) W' (Finset.univ.filter fun z => halfFin z ∈ Z) := by
      rw [cocycle_case1a_iff hWe, image_halfFin_filter_halfFin]; exact hcoc_sub
    have hZ'eq := (hmaxim W' _ hcoc_ext (Finset.Subset.refl _) hZ'sub).2
    have hmax_sub : IsMaximalCocyclePair s W Z := by
      refine ⟨⟨hWne.image _, hZne.image _, hcoc_sub⟩, ?_⟩
      intro W1 Z1 hcoc1 hWW1 hZZ1
      have hWe1 : ∀ w ∈ W1.image embEven, w.val % 2 = 0 := by
        intro w hw; rcases Finset.mem_image.mp hw with ⟨a, _, rfl⟩; simp [embEven]
      have hcoc1' : IsCocycleValid (s + 1) (W1.image embEven)
          (Finset.univ.filter fun z => halfFin z ∈ Z1) := by
        rw [cocycle_case1a_iff hWe1]
        have h1 : (W1.image embEven).image halfFin = W1 := by ext a; simp [halfFin_embEven]
        rw [h1, image_halfFin_filter_halfFin]; exact hcoc1
      have h1sub : W' ⊆ W1.image embEven := by rw [hW'eq]; exact Finset.image_subset_image hWW1
      have h2sub : Z' ⊆ Finset.univ.filter fun z => halfFin z ∈ Z1 := by
        rw [← hZ'eq]; intro z hz; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        exact hZZ1 hz
      have ⟨e1, e2⟩ := hmaxim _ _ hcoc1' h1sub h2sub
      constructor
      · have := congrArg (Finset.image halfFin) e1
        simpa [W, Finset.image_image, Function.comp_def, halfFin_embEven] using this
      · have := congrArg (Finset.image halfFin) e2
        simpa [Z, image_halfFin_filter_halfFin] using this
    exact ⟨0, (W, Z), hmax_sub, Prod.ext hW'eq.symm hZ'eq⟩
  · -- Case 1b
    let W := W'.image halfFin
    let Z := Z'.image fun z => halfFin (thetaMinus z)
    have hW'eq : W' = W.image embOdd := by
      ext x; simp only [W, Finset.mem_image]
      constructor
      · intro hx; exact ⟨halfFin x, ⟨x, hx, rfl⟩, embOdd_halfFin (hWo x hx)⟩
      · rintro ⟨a, ⟨y, hy, rfl⟩, rfl⟩; rwa [embOdd_halfFin (hWo y hy)]
    have hcoc_sub : IsCocycleValid s W Z := (cocycle_case1b_iff hWo).mp hcoc
    have hZ'sub : Z' ⊆ Finset.univ.filter fun z => halfFin (thetaMinus z) ∈ Z := by
      intro z hz; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, Finset.mem_image_of_mem _ hz⟩
    have hcoc_ext : IsCocycleValid (s + 1) W'
        (Finset.univ.filter fun z => halfFin (thetaMinus z) ∈ Z) := by
      rw [cocycle_case1b_iff hWo, image_halfFin_thetaMinus_filter]; exact hcoc_sub
    have hZ'eq := (hmaxim W' _ hcoc_ext (Finset.Subset.refl _) hZ'sub).2
    have hmax_sub : IsMaximalCocyclePair s W Z := by
      refine ⟨⟨hWne.image _, hZne.image _, hcoc_sub⟩, ?_⟩
      intro W1 Z1 hcoc1 hWW1 hZZ1
      have hWo1 : ∀ w ∈ W1.image embOdd, w.val % 2 = 1 := by
        intro w hw; rcases Finset.mem_image.mp hw with ⟨a, _, rfl⟩; simp [embOdd]
      have hcoc1' : IsCocycleValid (s + 1) (W1.image embOdd)
          (Finset.univ.filter fun z => halfFin (thetaMinus z) ∈ Z1) := by
        rw [cocycle_case1b_iff hWo1]
        have h1 : (W1.image embOdd).image halfFin = W1 := by ext a; simp [halfFin_embOdd]
        rw [h1, image_halfFin_thetaMinus_filter]; exact hcoc1
      have h1sub : W' ⊆ W1.image embOdd := by rw [hW'eq]; exact Finset.image_subset_image hWW1
      have h2sub : Z' ⊆ Finset.univ.filter fun z => halfFin (thetaMinus z) ∈ Z1 := by
        rw [← hZ'eq]; intro z hz; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        exact hZZ1 hz
      have ⟨e1, e2⟩ := hmaxim _ _ hcoc1' h1sub h2sub
      constructor
      · have := congrArg (Finset.image halfFin) e1
        simpa [W, Finset.image_image, Function.comp_def, halfFin_embOdd] using this
      · have := congrArg (Finset.image fun z => halfFin (thetaMinus z)) e2
        simpa [Z, image_halfFin_thetaMinus_filter] using this
    exact ⟨1, (W, Z), hmax_sub, Prod.ext hW'eq.symm hZ'eq⟩
  · -- Case 2a
    let W := W'.image halfFin
    let Z := Z'.image halfFin
    have hZ'eq : Z' = Z.image embOdd := by
      ext z; simp only [Z, Finset.mem_image]
      constructor
      · intro hz; exact ⟨halfFin z, ⟨z, hz, rfl⟩, embOdd_halfFin (hZo z hz)⟩
      · rintro ⟨a, ⟨y, hy, rfl⟩, rfl⟩; rwa [embOdd_halfFin (hZo y hy)]
    have hcoc_sub : IsCocycleValid s W Z := (cocycle_case2a_iff hZo).mp hcoc
    have hW'sub : W' ⊆ Finset.univ.filter fun w => halfFin w ∈ W := by
      intro w hw; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, Finset.mem_image_of_mem _ hw⟩
    have hcoc_ext : IsCocycleValid (s + 1) (Finset.univ.filter fun w => halfFin w ∈ W) Z' := by
      rw [cocycle_case2a_iff hZo, image_halfFin_filter_halfFin]; exact hcoc_sub
    have hW'eq := (hmaxim _ Z' hcoc_ext hW'sub (Finset.Subset.refl _)).1
    have hmax_sub : IsMaximalCocyclePair s W Z := by
      refine ⟨⟨hWne.image _, hZne.image _, hcoc_sub⟩, ?_⟩
      intro W1 Z1 hcoc1 hWW1 hZZ1
      have hZo1 : ∀ z ∈ Z1.image embOdd, z.val % 2 = 1 := by
        intro z hz; rcases Finset.mem_image.mp hz with ⟨a, _, rfl⟩; simp [embOdd]
      have hcoc1' : IsCocycleValid (s + 1)
          (Finset.univ.filter fun w => halfFin w ∈ W1) (Z1.image embOdd) := by
        rw [cocycle_case2a_iff hZo1]
        have h2 : (Z1.image embOdd).image halfFin = Z1 := by ext a; simp [halfFin_embOdd]
        rw [h2, image_halfFin_filter_halfFin]; exact hcoc1
      have h1sub : W' ⊆ Finset.univ.filter fun w => halfFin w ∈ W1 := by
        rw [← hW'eq]; intro w hw; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        exact hWW1 hw
      have h2sub : Z' ⊆ Z1.image embOdd := by rw [hZ'eq]; exact Finset.image_subset_image hZZ1
      have ⟨e1, e2⟩ := hmaxim _ _ hcoc1' h1sub h2sub
      constructor
      · have := congrArg (Finset.image halfFin) e1
        simpa [W, image_halfFin_filter_halfFin] using this
      · have := congrArg (Finset.image halfFin) e2
        simpa [Z, Finset.image_image, Function.comp_def, halfFin_embOdd] using this
    exact ⟨2, (W, Z), hmax_sub, Prod.ext hW'eq hZ'eq.symm⟩
  · -- Case 2b
    let W := W'.image fun w => halfFin (thetaPlus w)
    let Z := Z'.image halfFin
    have hZ'eq : Z' = Z.image embEven := by
      ext z; simp only [Z, Finset.mem_image]
      constructor
      · intro hz; exact ⟨halfFin z, ⟨z, hz, rfl⟩, embEven_halfFin (hZe z hz)⟩
      · rintro ⟨a, ⟨y, hy, rfl⟩, rfl⟩; rwa [embEven_halfFin (hZe y hy)]
    have hcoc_sub : IsCocycleValid s W Z := (cocycle_case2b_iff hZe).mp hcoc
    have hW'sub : W' ⊆ Finset.univ.filter fun w => halfFin (thetaPlus w) ∈ W := by
      intro w hw; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, Finset.mem_image_of_mem _ hw⟩
    have hcoc_ext : IsCocycleValid (s + 1)
        (Finset.univ.filter fun w => halfFin (thetaPlus w) ∈ W) Z' := by
      rw [cocycle_case2b_iff hZe, image_halfFin_thetaPlus_filter]; exact hcoc_sub
    have hW'eq := (hmaxim _ Z' hcoc_ext hW'sub (Finset.Subset.refl _)).1
    have hmax_sub : IsMaximalCocyclePair s W Z := by
      refine ⟨⟨hWne.image _, hZne.image _, hcoc_sub⟩, ?_⟩
      intro W1 Z1 hcoc1 hWW1 hZZ1
      have hZe1 : ∀ z ∈ Z1.image embEven, z.val % 2 = 0 := by
        intro z hz; rcases Finset.mem_image.mp hz with ⟨a, _, rfl⟩; simp [embEven]
      have hcoc1' : IsCocycleValid (s + 1)
          (Finset.univ.filter fun w => halfFin (thetaPlus w) ∈ W1) (Z1.image embEven) := by
        rw [cocycle_case2b_iff hZe1]
        have h2 : (Z1.image embEven).image halfFin = Z1 := by ext a; simp [halfFin_embEven]
        rw [h2, image_halfFin_thetaPlus_filter]; exact hcoc1
      have h1sub : W' ⊆ Finset.univ.filter fun w => halfFin (thetaPlus w) ∈ W1 := by
        rw [← hW'eq]; intro w hw; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        exact hWW1 hw
      have h2sub : Z' ⊆ Z1.image embEven := by rw [hZ'eq]; exact Finset.image_subset_image hZZ1
      have ⟨e1, e2⟩ := hmaxim _ _ hcoc1' h1sub h2sub
      constructor
      · have := congrArg (Finset.image fun w => halfFin (thetaPlus w)) e1
        simpa [W, image_halfFin_thetaPlus_filter] using this
      · have := congrArg (Finset.image halfFin) e2
        simpa [Z, Finset.image_image, Function.comp_def, halfFin_embEven] using this
    exact ⟨3, (W, Z), hmax_sub, Prod.ext hW'eq hZ'eq.symm⟩

/-- Exact inductive bijection `Fin 4 × MaxPairs(s) ≃ MaxPairs(s + 1)`. -/
noncomputable def maxCocyclePairsStepEquiv (s : ℕ) :
    Fin 4 × { p : Finset (Fin (2 ^ s)) × Finset (Fin (2 ^ s)) // IsMaximalCocyclePair s p.1 p.2 } ≃
      { p : Finset (Fin (2 ^ (s + 1))) × Finset (Fin (2 ^ (s + 1))) //
        IsMaximalCocyclePair (s + 1) p.1 p.2 } :=
  Equiv.ofBijective
    (fun ⟨c, ⟨p, hp⟩⟩ => ⟨stepMaxPair s (c, p), stepMaxPair_isMaximal s c hp⟩)
    ⟨fun ⟨c1, ⟨p1, hp1⟩⟩ ⟨c2, ⟨p2, hp2⟩⟩ h => by
        have hv : stepMaxPair s (c1, p1) = stepMaxPair s (c2, p2) := congrArg Subtype.val h
        have ⟨hc, hp⟩ := stepMaxPair_injective_on_max s c1 c2 p1 p2 hp1 hp2 hv
        exact Prod.ext hc (Subtype.ext hp),
     fun ⟨⟨W', Z'⟩, hmax⟩ => by
        rcases stepMaxPair_surjective_on_max s hmax with ⟨c, p, hp, heq⟩
        exact ⟨⟨c, ⟨p, hp⟩⟩, Subtype.ext heq⟩⟩

lemma stepMaxPair_cards (s : ℕ) (c : Fin 4) (p : Finset (Fin (2 ^ s)) × Finset (Fin (2 ^ s))) :
    ((c = 0 ∨ c = 1) → (stepMaxPair s (c, p)).1.card = p.1.card ∧
                        (stepMaxPair s (c, p)).2.card = 2 * p.2.card) ∧
    ((c = 2 ∨ c = 3) → (stepMaxPair s (c, p)).1.card = 2 * p.1.card ∧
                        (stepMaxPair s (c, p)).2.card = p.2.card) := by
  fin_cases c <;> simp [stepMaxPair, Finset.card_image_of_injective, embEven_injective,
    embOdd_injective, card_filter_halfFin, card_filter_halfFin_thetaMinus,
    card_filter_halfFin_thetaPlus]

/-- Base case `s = 0`: the unique maximal cocycle-valid pair on `Fin 1 × Fin 1` is `({0}, {0})`. -/
lemma maxCocyclePair_zero_iff (W Z : Finset (Fin (2 ^ 0))) :
    IsMaximalCocyclePair 0 W Z ↔ W = Finset.univ ∧ Z = Finset.univ := by
  constructor
  · intro h
    have hWne := h.1.1; have hZne := h.1.2.1
    constructor
    · ext x; simp only [Finset.mem_univ, iff_true]
      rcases hWne with ⟨w0, hw0⟩
      have : x = w0 := Fin.ext (by have := x.isLt; have := w0.isLt; omega)
      rwa [this]
    · ext z; simp only [Finset.mem_univ, iff_true]
      rcases hZne with ⟨z0, hz0⟩
      have : z = z0 := Fin.ext (by have := z.isLt; have := z0.isLt; omega)
      rwa [this]
  · rintro ⟨rfl, rfl⟩
    refine ⟨⟨⟨⟨0, by decide⟩, Finset.mem_univ _⟩, ⟨⟨0, by decide⟩, Finset.mem_univ _⟩, ?_⟩, ?_⟩
    · intro _ _ _ _ _ _ _ _; funext i; exact Fin.elim0 i
    · intro W' Z' _ hW hZ
      exact ⟨Finset.Subset.antisymm (Finset.subset_univ _) hW,
             Finset.Subset.antisymm (Finset.subset_univ _) hZ⟩

/-- Theorem 2.1(c): Exact count of maximal cocycle-valid pairs equals `4^s`. -/
theorem maxCocyclePairs_card (s : ℕ) :
    letI := Classical.decPred (fun p : Finset (Fin (2 ^ s)) × Finset (Fin (2 ^ s)) =>
      IsMaximalCocyclePair s p.1 p.2)
    Fintype.card { p : Finset (Fin (2 ^ s)) × Finset (Fin (2 ^ s)) //
      IsMaximalCocyclePair s p.1 p.2 } = 4 ^ s := by
  classical
  induction s with
  | zero =>
    have huniq : Unique { p : Finset (Fin (2 ^ 0)) × Finset (Fin (2 ^ 0)) //
        IsMaximalCocyclePair 0 p.1 p.2 } :=
      { default := ⟨(Finset.univ, Finset.univ), (maxCocyclePair_zero_iff _ _).mpr ⟨rfl, rfl⟩⟩
        uniq := fun ⟨⟨W, Z⟩, h⟩ => by
          have ⟨hW, hZ⟩ := (maxCocyclePair_zero_iff W Z).mp h
          exact Subtype.ext (Prod.ext hW hZ) }
    rw [Fintype.card_unique]
    simp
  | succ s ih =>
    rw [← Fintype.card_congr (maxCocyclePairsStepEquiv s), Fintype.card_prod, Fintype.card_fin]
    convert congrArg (4 * ·) ih using 1
    rw [pow_succ']

/-- Theorem 2.1(c): Every maximal cocycle-valid pair has dyadic shape `(2^a, 2^(s - a))`
with exact area `|W| * |Z| = 2^s`. -/
theorem maxCocyclePair_dyadic (s : ℕ) {W Z : Finset (Fin (2 ^ s))}
    (hmax : IsMaximalCocyclePair s W Z) :
    ∃ a ≤ s, W.card = 2 ^ a ∧ Z.card = 2 ^ (s - a) := by
  induction s with
  | zero =>
    have ⟨hW, hZ⟩ := (maxCocyclePair_zero_iff W Z).mp hmax
    subst hW; subst hZ
    exact ⟨0, le_rfl, by simp, by simp⟩
  | succ s ih =>
    rcases stepMaxPair_surjective_on_max s hmax with ⟨c, ⟨W0, Z0⟩, hmax0, heq⟩
    rcases ih hmax0 with ⟨a, ha, hWc, hZc⟩
    have h1 : (stepMaxPair s (c, (W0, Z0))).1 = W := congrArg Prod.fst heq
    have h2 : (stepMaxPair s (c, (W0, Z0))).2 = Z := congrArg Prod.snd heq
    have hc := stepMaxPair_cards s c (W0, Z0)
    fin_cases c
    · refine ⟨a, by omega, ?_, ?_⟩
      · rw [← h1, (hc.1 (Or.inl rfl)).1, hWc]
      · rw [← h2, (hc.1 (Or.inl rfl)).2, hZc, show s + 1 - a = (s - a) + 1 by omega, pow_succ']
    · refine ⟨a, by omega, ?_, ?_⟩
      · rw [← h1, (hc.1 (Or.inr rfl)).1, hWc]
      · rw [← h2, (hc.1 (Or.inr rfl)).2, hZc, show s + 1 - a = (s - a) + 1 by omega, pow_succ']
    · refine ⟨a + 1, by omega, ?_, ?_⟩
      · rw [← h1, (hc.2 (Or.inl rfl)).1, hWc, pow_succ']
      · rw [← h2, (hc.2 (Or.inl rfl)).2, hZc, show s + 1 - (a + 1) = s - a by omega]
    · refine ⟨a + 1, by omega, ?_, ?_⟩
      · rw [← h1, (hc.2 (Or.inr rfl)).1, hWc, pow_succ']
      · rw [← h2, (hc.2 (Or.inr rfl)).2, hZc, show s + 1 - (a + 1) = s - a by omega]

theorem maxCocyclePair_area (s : ℕ) {W Z : Finset (Fin (2 ^ s))}
    (hmax : IsMaximalCocyclePair s W Z) :
    W.card * Z.card = 2 ^ s := by
  rcases maxCocyclePair_dyadic s hmax with ⟨a, ha, hW, hZ⟩
  rw [hW, hZ, ← pow_add, Nat.add_sub_cancel' ha]

/-- Theorem 2.1(c): Shape generating function `(2X + 2Y)^s` over any `CommSemiring R`. -/
theorem maxCocyclePairs_shape_gf {R : Type*} [CommSemiring R] (s : ℕ) (X Y : R) :
    letI := Classical.decPred (fun p : Finset (Fin (2 ^ s)) × Finset (Fin (2 ^ s)) =>
      IsMaximalCocyclePair s p.1 p.2)
    ∑ p : { p : Finset (Fin (2 ^ s)) × Finset (Fin (2 ^ s)) // IsMaximalCocyclePair s p.1 p.2 },
      X ^ (Nat.log 2 p.1.1.card) * Y ^ (Nat.log 2 p.1.2.card) = (2 * X + 2 * Y) ^ s := by
  classical
  induction s with
  | zero =>
    let p0 : { p : Finset (Fin (2 ^ 0)) × Finset (Fin (2 ^ 0)) //
        IsMaximalCocyclePair 0 p.1 p.2 } :=
      ⟨(Finset.univ, Finset.univ), (maxCocyclePair_zero_iff _ _).mpr ⟨rfl, rfl⟩⟩
    have huniv : (Finset.univ : Finset { p : Finset (Fin (2 ^ 0)) × Finset (Fin (2 ^ 0)) //
        IsMaximalCocyclePair 0 p.1 p.2 }) = {p0} := by
      ext ⟨⟨W, Z⟩, h⟩
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      have ⟨hW, hZ⟩ := (maxCocyclePair_zero_iff W Z).mp h
      exact Subtype.ext (Prod.ext hW hZ)
    rw [huniv, Finset.sum_singleton]
    simp [p0]
  | succ s ih =>
    rw [← Equiv.sum_comp (maxCocyclePairsStepEquiv s)]
    rw [Fintype.sum_prod_type, Fin.sum_univ_four]
    have hterm0 : ∀ q : { p : Finset (Fin (2 ^ s)) × Finset (Fin (2 ^ s)) //
        IsMaximalCocyclePair s p.1 p.2 },
        X ^ Nat.log 2 (maxCocyclePairsStepEquiv s (0, q)).1.1.card *
        Y ^ Nat.log 2 (maxCocyclePairsStepEquiv s (0, q)).1.2.card =
        Y * (X ^ Nat.log 2 q.1.1.card * Y ^ Nat.log 2 q.1.2.card) := by
      intro ⟨⟨W, Z⟩, hq⟩
      rcases maxCocyclePair_dyadic s hq with ⟨a, ha, hW, hZ⟩
      have hc := (stepMaxPair_cards s 0 (W, Z)).1 (Or.inl rfl)
      change X ^ Nat.log 2 (stepMaxPair s (0, (W, Z))).1.card *
        Y ^ Nat.log 2 (stepMaxPair s (0, (W, Z))).2.card = _
      rw [hc.1, hc.2, hW, hZ, ← pow_succ',
          Nat.log_pow (by omega : 1 < 2), Nat.log_pow (by omega : 1 < 2),
          Nat.log_pow (by omega : 1 < 2), pow_succ']
      ring
    have hterm1 : ∀ q : { p : Finset (Fin (2 ^ s)) × Finset (Fin (2 ^ s)) //
        IsMaximalCocyclePair s p.1 p.2 },
        X ^ Nat.log 2 (maxCocyclePairsStepEquiv s (1, q)).1.1.card *
        Y ^ Nat.log 2 (maxCocyclePairsStepEquiv s (1, q)).1.2.card =
        Y * (X ^ Nat.log 2 q.1.1.card * Y ^ Nat.log 2 q.1.2.card) := by
      intro ⟨⟨W, Z⟩, hq⟩
      rcases maxCocyclePair_dyadic s hq with ⟨a, ha, hW, hZ⟩
      have hc := (stepMaxPair_cards s 1 (W, Z)).1 (Or.inr rfl)
      change X ^ Nat.log 2 (stepMaxPair s (1, (W, Z))).1.card *
        Y ^ Nat.log 2 (stepMaxPair s (1, (W, Z))).2.card = _
      rw [hc.1, hc.2, hW, hZ, ← pow_succ',
          Nat.log_pow (by omega : 1 < 2), Nat.log_pow (by omega : 1 < 2),
          Nat.log_pow (by omega : 1 < 2), pow_succ']
      ring
    have hterm2 : ∀ q : { p : Finset (Fin (2 ^ s)) × Finset (Fin (2 ^ s)) //
        IsMaximalCocyclePair s p.1 p.2 },
        X ^ Nat.log 2 (maxCocyclePairsStepEquiv s (2, q)).1.1.card *
        Y ^ Nat.log 2 (maxCocyclePairsStepEquiv s (2, q)).1.2.card =
        X * (X ^ Nat.log 2 q.1.1.card * Y ^ Nat.log 2 q.1.2.card) := by
      intro ⟨⟨W, Z⟩, hq⟩
      rcases maxCocyclePair_dyadic s hq with ⟨a, ha, hW, hZ⟩
      have hc := (stepMaxPair_cards s 2 (W, Z)).2 (Or.inl rfl)
      change X ^ Nat.log 2 (stepMaxPair s (2, (W, Z))).1.card *
        Y ^ Nat.log 2 (stepMaxPair s (2, (W, Z))).2.card = _
      rw [hc.1, hc.2, hW, hZ, ← pow_succ',
          Nat.log_pow (by omega : 1 < 2), Nat.log_pow (by omega : 1 < 2),
          Nat.log_pow (by omega : 1 < 2), pow_succ']
      ring
    have hterm3 : ∀ q : { p : Finset (Fin (2 ^ s)) × Finset (Fin (2 ^ s)) //
        IsMaximalCocyclePair s p.1 p.2 },
        X ^ Nat.log 2 (maxCocyclePairsStepEquiv s (3, q)).1.1.card *
        Y ^ Nat.log 2 (maxCocyclePairsStepEquiv s (3, q)).1.2.card =
        X * (X ^ Nat.log 2 q.1.1.card * Y ^ Nat.log 2 q.1.2.card) := by
      intro ⟨⟨W, Z⟩, hq⟩
      rcases maxCocyclePair_dyadic s hq with ⟨a, ha, hW, hZ⟩
      have hc := (stepMaxPair_cards s 3 (W, Z)).2 (Or.inr rfl)
      change X ^ Nat.log 2 (stepMaxPair s (3, (W, Z))).1.card *
        Y ^ Nat.log 2 (stepMaxPair s (3, (W, Z))).2.card = _
      rw [hc.1, hc.2, hW, hZ, ← pow_succ',
          Nat.log_pow (by omega : 1 < 2), Nat.log_pow (by omega : 1 < 2),
          Nat.log_pow (by omega : 1 < 2), pow_succ']
      ring
    simp only [hterm0, hterm1, hterm2, hterm3, ← Finset.mul_sum, ih]
    rw [pow_succ']
    ring

/-- Theorem 2.1(c): Exact count of maximal cocycle-valid pairs of shape `(2^a, 2^(s - a))`
equals `2^s * Nat.choose s a` (for `a ≤ s`, and `0` otherwise). -/
theorem maxCocyclePairs_shape_card (s a : ℕ) :
    letI := Classical.decPred (fun p : Finset (Fin (2 ^ s)) × Finset (Fin (2 ^ s)) =>
      IsMaximalCocyclePair s p.1 p.2 ∧ p.1.card = 2 ^ a ∧ p.2.card = 2 ^ (s - a))
    Fintype.card { p : Finset (Fin (2 ^ s)) × Finset (Fin (2 ^ s)) //
      IsMaximalCocyclePair s p.1 p.2 ∧ p.1.card = 2 ^ a ∧ p.2.card = 2 ^ (s - a) } =
      2 ^ s * Nat.choose s a := by
  classical
  have hcast : ∀ n m : ℕ,
      Fintype.card { p : Finset (Fin (2 ^ n)) × Finset (Fin (2 ^ n)) //
        IsMaximalCocyclePair n p.1 p.2 ∧ p.1.card = 2 ^ m ∧ p.2.card = 2 ^ (n - m) } =
      ∑ p : { p : Finset (Fin (2 ^ n)) × Finset (Fin (2 ^ n)) // IsMaximalCocyclePair n p.1 p.2 },
        if p.1.1.card = 2 ^ m ∧ p.1.2.card = 2 ^ (n - m) then 1 else 0 := by
    intro n m
    have heq : { p : Finset (Fin (2 ^ n)) × Finset (Fin (2 ^ n)) //
        IsMaximalCocyclePair n p.1 p.2 ∧ p.1.card = 2 ^ m ∧ p.2.card = 2 ^ (n - m) } ≃
        { p : { p : Finset (Fin (2 ^ n)) × Finset (Fin (2 ^ n)) // IsMaximalCocyclePair n p.1 p.2 } //
          p.1.1.card = 2 ^ m ∧ p.1.2.card = 2 ^ (n - m) } :=
      { toFun := fun ⟨p, h1, h2, h3⟩ => ⟨⟨p, h1⟩, h2, h3⟩
        invFun := fun ⟨⟨p, h1⟩, h2, h3⟩ => ⟨p, h1, h2, h3⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr heq, Fintype.card_subtype, Finset.card_filter]
  trans ∑ p : { p : Finset (Fin (2 ^ s)) × Finset (Fin (2 ^ s)) // IsMaximalCocyclePair s p.1 p.2 },
      if p.1.1.card = 2 ^ a ∧ p.1.2.card = 2 ^ (s - a) then 1 else 0
  · convert hcast s a
  induction s generalizing a with
  | zero =>
    let p0 : { p : Finset (Fin (2 ^ 0)) × Finset (Fin (2 ^ 0)) //
        IsMaximalCocyclePair 0 p.1 p.2 } :=
      ⟨(Finset.univ, Finset.univ), (maxCocyclePair_zero_iff _ _).mpr ⟨rfl, rfl⟩⟩
    have huniv : (Finset.univ : Finset { p : Finset (Fin (2 ^ 0)) × Finset (Fin (2 ^ 0)) //
        IsMaximalCocyclePair 0 p.1 p.2 }) = {p0} := by
      ext ⟨⟨W, Z⟩, h⟩
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      have ⟨hW, hZ⟩ := (maxCocyclePair_zero_iff W Z).mp h
      exact Subtype.ext (Prod.ext hW hZ)
    rw [huniv, Finset.sum_singleton]
    cases a with
    | zero => simp [p0]
    | succ a' =>
      have hne : (1 : ℕ) ≠ 2 ^ (a' + 1) := by
        have : 2 ≤ 2 ^ (a' + 1) := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (a' + 1) := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      simp [p0, hne]
  | succ s ih =>
    rw [← Equiv.sum_comp (maxCocyclePairsStepEquiv s), Fintype.sum_prod_type, Fin.sum_univ_four]
    have h01 : ∀ c : Fin 4, (c = 0 ∨ c = 1) →
        ∑ q : { p : Finset (Fin (2 ^ s)) × Finset (Fin (2 ^ s)) // IsMaximalCocyclePair s p.1 p.2 },
          (if (maxCocyclePairsStepEquiv s (c, q)).1.1.card = 2 ^ a ∧
              (maxCocyclePairsStepEquiv s (c, q)).1.2.card = 2 ^ (s + 1 - a) then 1 else 0) =
        2 ^ s * Nat.choose s a := by
      intro c hc01
      rw [← ih a]
      refine Finset.sum_congr rfl fun ⟨⟨W, Z⟩, hq⟩ _ => ?_
      have hcard := (stepMaxPair_cards s c (W, Z)).1 hc01
      change (if (stepMaxPair s (c, (W, Z))).1.card = 2 ^ a ∧
          (stepMaxPair s (c, (W, Z))).2.card = 2 ^ (s + 1 - a) then 1 else 0) = _
      rw [hcard.1, hcard.2]
      rcases maxCocyclePair_dyadic s hq with ⟨k, hk, hWk, hZk⟩
      rw [hWk, hZk]
      have hiff : (2 ^ k = 2 ^ a ∧ 2 * 2 ^ (s - k) = 2 ^ (s + 1 - a)) ↔
          (2 ^ k = 2 ^ a ∧ 2 ^ (s - k) = 2 ^ (s - a)) := by
        constructor
        · rintro ⟨e1, _⟩
          have hka : k = a := Nat.pow_right_injective (by omega : 2 ≤ 2) e1
          exact ⟨e1, by rw [hka]⟩
        · rintro ⟨e1, _⟩
          have hka : k = a := Nat.pow_right_injective (by omega : 2 ≤ 2) e1
          refine ⟨e1, ?_⟩
          rw [hka, ← pow_succ', show s - a + 1 = s + 1 - a by omega]
      simp only [hiff]
    have h23 : ∀ c : Fin 4, (c = 2 ∨ c = 3) →
        ∑ q : { p : Finset (Fin (2 ^ s)) × Finset (Fin (2 ^ s)) // IsMaximalCocyclePair s p.1 p.2 },
          (if (maxCocyclePairsStepEquiv s (c, q)).1.1.card = 2 ^ a ∧
              (maxCocyclePairsStepEquiv s (c, q)).1.2.card = 2 ^ (s + 1 - a) then 1 else 0) =
        match a with | 0 => 0 | a' + 1 => 2 ^ s * Nat.choose s a' := by
      intro c hc23
      cases a with
      | zero =>
        refine Finset.sum_eq_zero fun ⟨⟨W, Z⟩, hq⟩ _ => ?_
        have hcard := (stepMaxPair_cards s c (W, Z)).2 hc23
        change (if (stepMaxPair s (c, (W, Z))).1.card = 2 ^ 0 ∧
            (stepMaxPair s (c, (W, Z))).2.card = 2 ^ (s + 1 - 0) then 1 else 0) = 0
        rw [hcard.1]
        have hWpos : 1 ≤ W.card := Finset.card_pos.mpr hq.1.1
        have hne : ¬ (2 * W.card = 2 ^ 0 ∧ (stepMaxPair s (c, (W, Z))).2.card = 2 ^ (s + 1 - 0)) := by
          intro h; have := h.1; omega
        simp only [hne, ↓reduceIte]
      | succ a' =>
        dsimp only
        rw [← ih a']
        refine Finset.sum_congr rfl fun ⟨⟨W, Z⟩, hq⟩ _ => ?_
        have hcard := (stepMaxPair_cards s c (W, Z)).2 hc23
        change (if (stepMaxPair s (c, (W, Z))).1.card = 2 ^ (a' + 1) ∧
            (stepMaxPair s (c, (W, Z))).2.card = 2 ^ (s + 1 - (a' + 1)) then 1 else 0) = _
        rw [hcard.1, hcard.2]
        have hsub : s + 1 - (a' + 1) = s - a' := by omega
        rw [hsub, pow_succ']
        have hiff : (2 * W.card = 2 * 2 ^ a' ∧ Z.card = 2 ^ (s - a')) ↔
            (W.card = 2 ^ a' ∧ Z.card = 2 ^ (s - a')) := by omega
        simp only [hiff]
    rw [h01 0 (Or.inl rfl), h01 1 (Or.inr rfl), h23 2 (Or.inl rfl), h23 3 (Or.inr rfl)]
    cases a with
    | zero => simp [pow_succ']; ring
    | succ a' =>
      rw [Nat.choose_succ_succ, pow_succ']
      ring

/-- Every nonempty cocycle-valid pair `(W, Z)` is contained in a maximal cocycle-valid pair. -/
theorem exists_maximalCocyclePair_superset (s : ℕ) {W Z : Finset (Fin (2 ^ s))}
    (hWZ : IsNonemptyCocycleValid s W Z) :
    ∃ W' Z', IsMaximalCocyclePair s W' Z' ∧ W ⊆ W' ∧ Z ⊆ Z' := by
  suffices ∀ k : ℕ, ∀ W Z : Finset (Fin (2 ^ s)),
      IsNonemptyCocycleValid s W Z → 2 * 2 ^ s - (W.card + Z.card) ≤ k →
      ∃ W' Z', IsMaximalCocyclePair s W' Z' ∧ W ⊆ W' ∧ Z ⊆ Z' by
    exact this (2 * 2 ^ s - (W.card + Z.card)) W Z hWZ le_rfl
  intro k
  induction k with
  | zero =>
    intro W Z h hle
    have hWle : W.card ≤ 2 ^ s := by simpa using Finset.card_le_univ W
    have hZle : Z.card ≤ 2 ^ s := by simpa using Finset.card_le_univ Z
    refine ⟨W, Z, ⟨h, fun W' Z' _ hWW' hZZ' => ?_⟩, Finset.Subset.refl _, Finset.Subset.refl _⟩
    have hW'le : W'.card ≤ 2 ^ s := by simpa using Finset.card_le_univ W'
    have hZ'le : Z'.card ≤ 2 ^ s := by simpa using Finset.card_le_univ Z'
    exact ⟨(Finset.eq_of_subset_of_card_le hWW' (by omega)).symm,
           (Finset.eq_of_subset_of_card_le hZZ' (by omega)).symm⟩
  | succ k ih =>
    intro W Z h hle
    by_cases hmax : IsMaximalCocyclePair s W Z
    · exact ⟨W, Z, hmax, Finset.Subset.refl _, Finset.Subset.refl _⟩
    · unfold IsMaximalCocyclePair at hmax
      push Not at hmax
      rcases hmax h with ⟨W1, Z1, hcoc1, hWW1, hZZ1, hne⟩
      have hcard_lt : W.card + Z.card < W1.card + Z1.card := by
        have hleW := Finset.card_le_card hWW1
        have hleZ := Finset.card_le_card hZZ1
        by_contra hnot
        have eW : W1 = W := (Finset.eq_of_subset_of_card_le hWW1 (by omega)).symm
        have eZ : Z1 = Z := (Finset.eq_of_subset_of_card_le hZZ1 (by omega)).symm
        exact hne eW eZ
      have hW1le : W1.card ≤ 2 ^ s := by simpa using Finset.card_le_univ W1
      have hZ1le : Z1.card ≤ 2 ^ s := by simpa using Finset.card_le_univ Z1
      rcases ih W1 Z1 ⟨h.1.mono hWW1, h.2.1.mono hZZ1, hcoc1⟩ (by omega) with
        ⟨W', Z', hmax', hW1', hZ1'⟩
      exact ⟨W', Z', hmax', hWW1.trans hW1', hZZ1.trans hZ1'⟩

/-- Dyadic containment for EVERY cocycle-valid pair `(W, Z)` (possibly empty or non-maximal). -/
theorem cocycleValid_dyadic_bound (s : ℕ) {W Z : Finset (Fin (2 ^ s))}
    (hcoc : IsCocycleValid s W Z) :
    ∃ a ≤ s, W.card ≤ 2 ^ a ∧ Z.card ≤ 2 ^ (s - a) := by
  by_cases hW : W.Nonempty
  · by_cases hZ : Z.Nonempty
    · rcases exists_maximalCocyclePair_superset s ⟨hW, hZ, hcoc⟩ with ⟨W', Z', hmax', hWW', hZZ'⟩
      rcases maxCocyclePair_dyadic s hmax' with ⟨a, ha, hW'c, hZ'c⟩
      exact ⟨a, ha, hW'c ▸ Finset.card_le_card hWW', hZ'c ▸ Finset.card_le_card hZZ'⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at hZ
      exact ⟨s, le_rfl, by simpa using Finset.card_le_univ W, by simp [hZ]⟩
  · rw [Finset.not_nonempty_iff_eq_empty] at hW
    exact ⟨0, Nat.zero_le _, by simp [hW], by simpa using Finset.card_le_univ Z⟩

/-- Theorem 2.1(c): Dyadic shape containment for EVERY nonempty biclique `U × V` of `K_coreRel s`. -/
theorem K_coreRel_nonempty_biclique_dyadic_bound (s : ℕ)
    {U V : Finset ((Fin s → ZMod 2) × Fin (2 ^ s))}
    (hU : U.Nonempty) (hV : V.Nonempty)
    (hbic : IsBiclique (K_coreRel s) U V) :
    ∃ a ≤ s, U.card ≤ 2 ^ a ∧ V.card ≤ 2 ^ (s - a) := by
  have h3 := (K_coreRel_biclique_iff_three_conds s hU hV).mp hbic
  rcases cocycleValid_dyadic_bound s h3.2.1 with ⟨a, ha, hW, hZ⟩
  exact ⟨a, ha, h3.1.1 ▸ hW, h3.1.2 ▸ hZ⟩

/-- Theorem 2.1(c): Exact maximum biclique area `A_max(K_t) = 2^s` (upper bound). -/
theorem K_coreRel_biclique_area_le (s : ℕ)
    {U V : Finset ((Fin s → ZMod 2) × Fin (2 ^ s))}
    (hbic : IsBiclique (K_coreRel s) U V) :
    U.card * V.card ≤ 2 ^ s := by
  by_cases hU : U.Nonempty
  · by_cases hV : V.Nonempty
    · have h3 := (K_coreRel_biclique_iff_three_conds s hU hV).mp hbic
      rcases cocycleValid_dyadic_bound s h3.2.1 with ⟨a, ha, hW, hZ⟩
      calc U.card * V.card = (projW U).card * (projZ V).card := by rw [h3.1.1, h3.1.2]
        _ ≤ 2 ^ a * 2 ^ (s - a) := Nat.mul_le_mul hW hZ
        _ = 2 ^ s := by rw [← pow_add, Nat.add_sub_cancel' ha]
    · rw [Finset.not_nonempty_iff_eq_empty] at hV; simp [hV]
  · rw [Finset.not_nonempty_iff_eq_empty] at hU; simp [hU]

/-- Theorem 2.1(c): Exact maximum biclique area `A_max(K_t) = 2^s` is attained. -/
theorem K_coreRel_maxBiclique_area_attained (s : ℕ) :
    ∃ U V : Finset ((Fin s → ZMod 2) × Fin (2 ^ s)),
      IsMaximalBiclique (K_coreRel s) U V ∧ U.card * V.card = 2 ^ s := by
  have h1 : IsNonemptyCocycleValid s {⟨0, by positivity⟩} {⟨0, by positivity⟩} := by
    refine ⟨by simp, by simp, ?_⟩
    intro w1 hw1 w2 hw2 z1 hz1 z2 hz2
    simp only [Finset.mem_singleton] at hw1 hw2 hz1 hz2
    subst hw1; subst hw2; subst hz1; subst hz2
    exact zmod2_vec_four_cancel (borrowVec s ⟨0, by positivity⟩ ⟨0, by positivity⟩) 0
      (borrowVec s ⟨0, by positivity⟩ ⟨0, by positivity⟩) 0 |> fun _ => by
        funext i; simp only [Pi.add_apply, Pi.zero_apply]
        exact zmod2_four_univariate_w (fun _ : Unit => borrowVec s ⟨0, by positivity⟩ ⟨0, by positivity⟩ i) () ()
  rcases exists_maximalCocyclePair_superset s h1 with ⟨W, Z, hmax, _, _⟩
  rcases hmax.1.1 with ⟨w0, hw0⟩
  rcases hmax.1.2.1 with ⟨z0, hz0⟩
  refine ⟨liftU s W w0 z0 0, liftV s Z w0 0, ?_, ?_⟩
  · have hne : IsNonemptyBiclique (K_coreRel s) (liftU s W w0 z0 0) (liftV s Z w0 0) :=
      ⟨hmax.1.1.image _, hmax.1.2.1.image _, lift_isBiclique s hmax.1.2.2 hw0 hz0 0⟩
    rw [lift_isMaximalBiclique_iff s hne, projW_liftU, projZ_liftV]
    exact hmax
  · rw [card_liftU, card_liftV]
    exact maxCocyclePair_area s hmax

/-- Theorem 2.1(c): Exact count of maximal bicliques of `K_coreRel s` equals `8^s`. -/
theorem K_coreRel_maxBicliques_card (s : ℕ) :
    letI := Classical.decPred (fun p :
      Finset ((Fin s → ZMod 2) × Fin (2 ^ s)) × Finset ((Fin s → ZMod 2) × Fin (2 ^ s)) =>
      IsMaximalBiclique (K_coreRel s) p.1 p.2)
    Fintype.card { p :
      Finset ((Fin s → ZMod 2) × Fin (2 ^ s)) × Finset ((Fin s → ZMod 2) × Fin (2 ^ s)) //
      IsMaximalBiclique (K_coreRel s) p.1 p.2 } = 8 ^ s := by
  classical
  let MaxP := { q : Finset (Fin (2 ^ s)) × Finset (Fin (2 ^ s)) // IsMaximalCocyclePair s q.1 q.2 }
  let MaxB := { p :
    Finset ((Fin s → ZMod 2) × Fin (2 ^ s)) × Finset ((Fin s → ZMod 2) × Fin (2 ^ s)) //
    IsMaximalBiclique (K_coreRel s) p.1 p.2 }
  have heq : MaxB ≃ Σ q : MaxP,
      { p : Finset ((Fin s → ZMod 2) × Fin (2 ^ s)) × Finset ((Fin s → ZMod 2) × Fin (2 ^ s)) //
        IsBiclique (K_coreRel s) p.1 p.2 ∧ projW p.1 = q.1.1 ∧ projZ p.2 = q.1.2 } :=
    { toFun := fun ⟨⟨U, V⟩, hmax⟩ =>
        ⟨⟨(projW U, projZ V), (lift_isMaximalBiclique_iff s hmax.1).mp hmax⟩,
         ⟨(U, V), hmax.1.2.2, rfl, rfl⟩⟩
      invFun := fun ⟨⟨⟨W, Z⟩, hmaxP⟩, ⟨⟨U, V⟩, hbic, hW, hZ⟩⟩ =>
        have hUne : U.Nonempty := by
          rcases hmaxP.1.1 with ⟨w, hw⟩
          rw [← hW] at hw
          rcases Finset.mem_image.mp hw with ⟨r, hr, _⟩
          exact ⟨r, hr⟩
        have hVne : V.Nonempty := by
          rcases hmaxP.1.2.1 with ⟨z, hz⟩
          rw [← hZ] at hz
          rcases Finset.mem_image.mp hz with ⟨c, hc, _⟩
          exact ⟨c, hc⟩
        ⟨(U, V), (lift_isMaximalBiclique_iff s ⟨hUne, hVne, hbic⟩).mpr (by rw [hW, hZ]; exact hmaxP)⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨⟨⟨W, Z⟩, hmaxP⟩, ⟨⟨U, V⟩, hbic, hW, hZ⟩⟩ => by
        dsimp only at hW hZ ⊢
        subst hW; subst hZ; rfl }
  rw [Fintype.card_congr heq, Fintype.card_sigma]
  have hfiber : ∀ q : MaxP,
      Fintype.card { p :
        Finset ((Fin s → ZMod 2) × Fin (2 ^ s)) × Finset ((Fin s → ZMod 2) × Fin (2 ^ s)) //
        IsBiclique (K_coreRel s) p.1 p.2 ∧ projW p.1 = q.1.1 ∧ projZ p.2 = q.1.2 } = 2 ^ s := by
    intro ⟨⟨W, Z⟩, hmaxP⟩
    rcases hmaxP.1.1 with ⟨w0, hw0⟩
    rcases hmaxP.1.2.1 with ⟨z0, hz0⟩
    rw [← Fintype.card_congr (cocycleLiftsEquiv s hmaxP.1 w0 hw0 z0 hz0)]
    simp [ZMod.card]
  have hMaxP : Fintype.card MaxP = 4 ^ s := by convert maxCocyclePairs_card s
  simp only [hfiber, Finset.sum_const, Finset.card_univ, smul_eq_mul, hMaxP]
  calc 4 ^ s * 2 ^ s = (4 * 2) ^ s := (Nat.mul_pow 4 2 s).symm
    _ = 8 ^ s := by norm_num

/-! #### Lifting Maximal Bicliques and `A_max` from `K_t` to `M_t` -/

/-- Lift a row set `U_core` of `K_coreRel s` to `M_rel (s + 1)` on component `b : Fin 2`
by taking the full `J_2` preimage. -/
def liftM_U (s : ℕ) (b : Fin 2) (U_core : Finset ((Fin s → ZMod 2) × Fin (2 ^ s))) :
    Finset (Fin (2 ^ (s + 1)) × Fin (2 ^ (s + 1))) :=
  Finset.univ.filter fun r => (phi_row s r).1 = b ∧ (phi_row s r).2.1 ∈ U_core

/-- Lift a column set `V_core` of `K_coreRel s` to `M_rel (s + 1)` on component `b : Fin 2`
by taking the full `J_2` preimage. -/
def liftM_V (s : ℕ) (b : Fin 2) (V_core : Finset ((Fin s → ZMod 2) × Fin (2 ^ s))) :
    Finset (Fin (2 ^ (s + 1)) × Fin (2 ^ (s + 1))) :=
  Finset.univ.filter fun c => (phi_col s c).1 = b ∧ (phi_col s c).2.1 ∈ V_core

lemma card_liftM_U (s : ℕ) (b : Fin 2) (U_core : Finset ((Fin s → ZMod 2) × Fin (2 ^ s))) :
    (liftM_U s b U_core).card = 2 * U_core.card := by
  have hbij : (liftM_U s b U_core).card = (U_core ×ˢ (Finset.univ : Finset (Fin 2))).card := by
    refine Finset.card_bij
      (fun r _ => ((phi_row s r).2.1, (phi_row s r).2.2))
      (fun r hr => ?_)
      (fun r1 hr1 r2 hr2 h => ?_)
      (fun p hp => ?_)
    · rw [liftM_U, Finset.mem_filter] at hr
      exact Finset.mem_product.mpr ⟨hr.2.2, Finset.mem_univ _⟩
    · rw [liftM_U, Finset.mem_filter] at hr1 hr2
      apply (phi_row s).injective
      exact Prod.ext (hr1.2.1.trans hr2.2.1.symm)
        (Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
    · rw [Finset.mem_product] at hp
      refine ⟨(phi_row s).symm (b, p.1, p.2), ?_, ?_⟩
      · rw [liftM_U, Finset.mem_filter]
        simp [hp.1]
      · simp
  rw [hbij, Finset.card_product, Finset.card_univ, Fintype.card_fin, mul_comm]

lemma card_liftM_V (s : ℕ) (b : Fin 2) (V_core : Finset ((Fin s → ZMod 2) × Fin (2 ^ s))) :
    (liftM_V s b V_core).card = 2 * V_core.card :=
  card_liftM_U s b V_core

lemma image_liftM_U (s : ℕ) (b : Fin 2) (U_core : Finset ((Fin s → ZMod 2) × Fin (2 ^ s))) :
    (liftM_U s b U_core).image (fun r => (phi_row s r).2.1) = U_core := by
  ext u
  simp only [liftM_U, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨r, ⟨_, hr⟩, rfl⟩; exact hr
  · intro hu
    refine ⟨(phi_row s).symm (b, u, 0), ?_, by simp⟩
    simp [hu]

lemma image_liftM_V (s : ℕ) (b : Fin 2) (V_core : Finset ((Fin s → ZMod 2) × Fin (2 ^ s))) :
    (liftM_V s b V_core).image (fun c => (phi_col s c).2.1) = V_core :=
  image_liftM_U s b V_core

/-- Theorem 2.1(c): Dyadic shape containment for every nonempty biclique `U × V` of `M_rel (s + 1)`.
Matches `(|U|, |V|) ≤ (2^(s - m + 1), 2^(m + 1))` for some `0 ≤ m ≤ s`. -/
theorem M_rel_nonempty_biclique_dyadic_bound (s : ℕ)
    {U V : Finset (Fin (2 ^ (s + 1)) × Fin (2 ^ (s + 1)))}
    (hUne : U.Nonempty) (hVne : V.Nonempty)
    (hbic : IsBiclique (M_rel (s + 1)) U V) :
    ∃ m ≤ s, U.card ≤ 2 ^ (s - m + 1) ∧ V.card ≤ 2 ^ (m + 1) := by
  rcases hUne with ⟨r0, hr0⟩
  rcases hVne with ⟨c0, hc0⟩
  let b := (phi_row s r0).1
  have hU_b : ∀ r ∈ U, (phi_row s r).1 = b := by
    intro r hr
    have h1 := (M_rel_core_factorization s r c0).mp (hbic r hr c0 hc0)
    have h0 := (M_rel_core_factorization s r0 c0).mp (hbic r0 hr0 c0 hc0)
    exact h1.1.trans h0.1.symm
  have hV_b : ∀ c ∈ V, (phi_col s c).1 = b := by
    intro c hc
    have h1 := (M_rel_core_factorization s r0 c).mp (hbic r0 hr0 c hc)
    exact h1.1.symm
  let U_core := U.image (fun r => (phi_row s r).2.1)
  let V_core := V.image (fun c => (phi_col s c).2.1)
  have hbic_core : IsBiclique (K_coreRel s) U_core V_core := by
    intro u hu v hv
    rcases Finset.mem_image.mp hu with ⟨r, hr, rfl⟩
    rcases Finset.mem_image.mp hv with ⟨c, hc, rfl⟩
    exact ((M_rel_core_factorization s r c).mp (hbic r hr c hc)).2
  have hUsub : U ⊆ liftM_U s b U_core := by
    intro r hr; rw [liftM_U, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hU_b r hr, Finset.mem_image_of_mem _ hr⟩
  have hVsub : V ⊆ liftM_V s b V_core := by
    intro c hc; rw [liftM_V, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hV_b c hc, Finset.mem_image_of_mem _ hc⟩
  have hU_le : U.card ≤ 2 * U_core.card := by
    calc U.card ≤ (liftM_U s b U_core).card := Finset.card_le_card hUsub
      _ = 2 * U_core.card := card_liftM_U s b U_core
  have hV_le : V.card ≤ 2 * V_core.card := by
    calc V.card ≤ (liftM_V s b V_core).card := Finset.card_le_card hVsub
      _ = 2 * V_core.card := card_liftM_V s b V_core
  have h3 := (K_coreRel_biclique_iff_three_conds s ⟨_, Finset.mem_image_of_mem _ hr0⟩
    ⟨_, Finset.mem_image_of_mem _ hc0⟩).mp hbic_core
  rcases cocycleValid_dyadic_bound s h3.2.1 with ⟨a, ha, hWa, hZa⟩
  refine ⟨s - a, by omega, ?_, ?_⟩
  · have hsub : s - (s - a) + 1 = a + 1 := by omega
    rw [hsub]
    calc U.card ≤ 2 * U_core.card := hU_le
      _ = 2 * (projW U_core).card := by rw [h3.1.1]
      _ ≤ 2 * 2 ^ a := Nat.mul_le_mul_left 2 hWa
      _ = 2 ^ (a + 1) := (pow_succ' 2 a).symm
  · calc V.card ≤ 2 * V_core.card := hV_le
      _ = 2 * (projZ V_core).card := by rw [h3.1.2]
      _ ≤ 2 * 2 ^ (s - a) := Nat.mul_le_mul_left 2 hZa
      _ = 2 ^ (s - a + 1) := (pow_succ' 2 (s - a)).symm

/-- Theorem 2.1(c): Exact maximum biclique area `A_max(M_{s+1}) = 2^(s + 2)` (upper bound). -/
theorem M_rel_biclique_area_le (s : ℕ)
    {U V : Finset (Fin (2 ^ (s + 1)) × Fin (2 ^ (s + 1)))}
    (hbic : IsBiclique (M_rel (s + 1)) U V) :
    U.card * V.card ≤ 2 ^ (s + 2) := by
  by_cases hU : U.Nonempty
  · by_cases hV : V.Nonempty
    · rcases M_rel_nonempty_biclique_dyadic_bound s hU hV hbic with ⟨m, hm, hUm, hVm⟩
      calc U.card * V.card ≤ 2 ^ (s - m + 1) * 2 ^ (m + 1) := Nat.mul_le_mul hUm hVm
        _ = 2 ^ ((s - m + 1) + (m + 1)) := (pow_add 2 _ _).symm
        _ = 2 ^ (s + 2) := by congr 1; omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hV; simp [hV]
  · rw [Finset.not_nonempty_iff_eq_empty] at hU; simp [hU]

/-- Exact equivalence between maximal bicliques of `M_rel (s + 1)` and
`Fin 2 × (maximal bicliques of K_coreRel s)`. -/
noncomputable def M_rel_maxBicliques_equiv (s : ℕ) :
    Fin 2 × { q :
      Finset ((Fin s → ZMod 2) × Fin (2 ^ s)) × Finset ((Fin s → ZMod 2) × Fin (2 ^ s)) //
      IsMaximalBiclique (K_coreRel s) q.1 q.2 } ≃
    { p : Finset (Fin (2 ^ (s + 1)) × Fin (2 ^ (s + 1))) ×
          Finset (Fin (2 ^ (s + 1)) × Fin (2 ^ (s + 1))) //
      IsMaximalBiclique (M_rel (s + 1)) p.1 p.2 } :=
  Equiv.ofBijective
    (fun ⟨b, ⟨⟨Uc, Vc⟩, hmax⟩⟩ =>
      ⟨(liftM_U s b Uc, liftM_V s b Vc), by
        have hbic : IsBiclique (M_rel (s + 1)) (liftM_U s b Uc) (liftM_V s b Vc) := by
          intro r hr c hc
          rw [liftM_U, Finset.mem_filter] at hr
          rw [liftM_V, Finset.mem_filter] at hc
          exact (M_rel_core_factorization s r c).mpr
            ⟨hr.2.1.trans hc.2.1.symm, hmax.1.2.2 _ hr.2.2 _ hc.2.2⟩
        have hUne : (liftM_U s b Uc).Nonempty := by
          rcases hmax.1.1 with ⟨u, hu⟩
          exact ⟨(phi_row s).symm (b, u, 0), by rw [liftM_U, Finset.mem_filter]; simp [hu]⟩
        have hVne : (liftM_V s b Vc).Nonempty := by
          rcases hmax.1.2.1 with ⟨v, hv⟩
          exact ⟨(phi_col s).symm (b, v, 0), by rw [liftM_V, Finset.mem_filter]; simp [hv]⟩
        refine ⟨⟨hUne, hVne, hbic⟩, ?_⟩
        intro U' V' hbic' hUU' hVV'
        rcases hUne with ⟨r0, hr0⟩
        rcases hVne with ⟨c0, hc0⟩
        have hr0_b : (phi_row s r0).1 = b := ((Finset.mem_filter.mp hr0).2).1
        have hU'_b : ∀ r ∈ U', (phi_row s r).1 = b := by
          intro r hr
          have h1 := (M_rel_core_factorization s r c0).mp (hbic' r hr c0 (hVV' hc0))
          have h0 := (M_rel_core_factorization s r0 c0).mp (hbic' r0 (hUU' hr0) c0 (hVV' hc0))
          exact h1.1.trans (h0.1.symm.trans hr0_b)
        have hV'_b : ∀ c ∈ V', (phi_col s c).1 = b := by
          intro c hc
          have h1 := (M_rel_core_factorization s r0 c).mp (hbic' r0 (hUU' hr0) c hc)
          exact h1.1.symm.trans hr0_b
        let Uc' := U'.image (fun r => (phi_row s r).2.1)
        let Vc' := V'.image (fun c => (phi_col s c).2.1)
        have hbic_c' : IsBiclique (K_coreRel s) Uc' Vc' := by
          intro u hu v hv
          rcases Finset.mem_image.mp hu with ⟨r, hr, rfl⟩
          rcases Finset.mem_image.mp hv with ⟨c, hc, rfl⟩
          exact ((M_rel_core_factorization s r c).mp (hbic' r hr c hc)).2
        have hUc_sub : Uc ⊆ Uc' := by
          rw [← image_liftM_U s b Uc]; exact Finset.image_subset_image hUU'
        have hVc_sub : Vc ⊆ Vc' := by
          rw [← image_liftM_V s b Vc]; exact Finset.image_subset_image hVV'
        have ⟨eU, eV⟩ := hmax.2 Uc' Vc' hbic_c' hUc_sub hVc_sub
        dsimp only at eU eV
        constructor
        · ext r
          constructor
          · intro hr
            rw [liftM_U, Finset.mem_filter]
            exact ⟨Finset.mem_univ _, hU'_b r hr, by rw [← eU]; exact Finset.mem_image_of_mem _ hr⟩
          · exact fun hr => hUU' hr
        · ext c
          constructor
          · intro hc
            rw [liftM_V, Finset.mem_filter]
            exact ⟨Finset.mem_univ _, hV'_b c hc, by rw [← eV]; exact Finset.mem_image_of_mem _ hc⟩
          · exact fun hc => hVV' hc⟩)
    ⟨fun x1 x2 h => by
        rcases x1 with ⟨b1, ⟨⟨U1, V1⟩, h1⟩⟩
        rcases x2 with ⟨b2, ⟨⟨U2, V2⟩, h2⟩⟩
        have eU : liftM_U s b1 U1 = liftM_U s b2 U2 := congrArg (fun x => x.1.1) h
        have eV : liftM_V s b1 V1 = liftM_V s b2 V2 := congrArg (fun x => x.1.2) h
        rcases h1.1.1 with ⟨u0, hu0⟩
        have hr_mem : (phi_row s).symm (b1, u0, 0) ∈ liftM_U s b2 U2 := by
          rw [← eU, liftM_U, Finset.mem_filter]; simp [hu0]
        rw [liftM_U, Finset.mem_filter] at hr_mem
        have hb : b1 = b2 := by simpa using hr_mem.2.1
        subst hb
        have hUeq : U1 = U2 := by
          have := congrArg (Finset.image fun r => (phi_row s r).2.1) eU
          simpa [image_liftM_U] using this
        have hVeq : V1 = V2 := by
          have := congrArg (Finset.image fun c => (phi_col s c).2.1) eV
          simpa [image_liftM_V] using this
        exact Prod.ext rfl (Subtype.ext (Prod.ext hUeq hVeq)),
     fun ⟨⟨U, V⟩, hmax⟩ => by
        rcases hmax.1.1 with ⟨r0, hr0⟩
        rcases hmax.1.2.1 with ⟨c0, hc0⟩
        let b := (phi_row s r0).1
        have hU_b : ∀ r ∈ U, (phi_row s r).1 = b := by
          intro r hr
          have h1 := (M_rel_core_factorization s r c0).mp (hmax.1.2.2 r hr c0 hc0)
          have h0 := (M_rel_core_factorization s r0 c0).mp (hmax.1.2.2 r0 hr0 c0 hc0)
          exact h1.1.trans h0.1.symm
        have hV_b : ∀ c ∈ V, (phi_col s c).1 = b := by
          intro c hc
          exact ((M_rel_core_factorization s r0 c).mp (hmax.1.2.2 r0 hr0 c hc)).1.symm
        let Uc := U.image (fun r => (phi_row s r).2.1)
        let Vc := V.image (fun c => (phi_col s c).2.1)
        have hbic_c : IsBiclique (K_coreRel s) Uc Vc := by
          intro u hu v hv
          rcases Finset.mem_image.mp hu with ⟨r, hr, rfl⟩
          rcases Finset.mem_image.mp hv with ⟨c, hc, rfl⟩
          exact ((M_rel_core_factorization s r c).mp (hmax.1.2.2 r hr c hc)).2
        have hUsub : U ⊆ liftM_U s b Uc := by
          intro r hr; rw [liftM_U, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hU_b r hr, Finset.mem_image_of_mem _ hr⟩
        have hVsub : V ⊆ liftM_V s b Vc := by
          intro c hc; rw [liftM_V, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hV_b c hc, Finset.mem_image_of_mem _ hc⟩
        have hbic_lift : IsBiclique (M_rel (s + 1)) (liftM_U s b Uc) (liftM_V s b Vc) := by
          intro r hr c hc
          rw [liftM_U, Finset.mem_filter] at hr
          rw [liftM_V, Finset.mem_filter] at hc
          exact (M_rel_core_factorization s r c).mpr
            ⟨hr.2.1.trans hc.2.1.symm, hbic_c _ hr.2.2 _ hc.2.2⟩
        have ⟨eU, eV⟩ := hmax.2 _ _ hbic_lift hUsub hVsub
        dsimp only at eU eV
        have hmax_c : IsMaximalBiclique (K_coreRel s) Uc Vc := by
          refine ⟨⟨hmax.1.1.image _, hmax.1.2.1.image _, hbic_c⟩, ?_⟩
          intro Uc' Vc' hbic' hUc' hVc'
          have hbic_l' : IsBiclique (M_rel (s + 1)) (liftM_U s b Uc') (liftM_V s b Vc') := by
            intro r hr c hc
            rw [liftM_U, Finset.mem_filter] at hr
            rw [liftM_V, Finset.mem_filter] at hc
            exact (M_rel_core_factorization s r c).mpr
              ⟨hr.2.1.trans hc.2.1.symm, hbic' _ hr.2.2 _ hc.2.2⟩
          have hsubU' : U ⊆ liftM_U s b Uc' := by
            rw [← eU]; intro r hr
            simp only [liftM_U, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
            exact ⟨hr.1, hUc' hr.2⟩
          have hsubV' : V ⊆ liftM_V s b Vc' := by
            rw [← eV]; intro c hc
            simp only [liftM_V, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
            exact ⟨hc.1, hVc' hc.2⟩
          have ⟨eU', eV'⟩ := hmax.2 _ _ hbic_l' hsubU' hsubV'
          dsimp only at eU' eV'
          constructor
          · have := congrArg (Finset.image fun r => (phi_row s r).2.1) eU'
            simpa [Uc, image_liftM_U] using this
          · have := congrArg (Finset.image fun c => (phi_col s c).2.1) eV'
            simpa [Vc, image_liftM_V] using this
        exact ⟨⟨b, ⟨(Uc, Vc), hmax_c⟩⟩, Subtype.ext (Prod.ext eU eV)⟩⟩

/-- Theorem 2.1(c): Exact count of maximal bicliques of `M_rel (s + 1)` equals
`2 * 8^s = 2^(3*(s + 1) - 2)`. -/
theorem M_rel_maxBicliques_card (s : ℕ) :
    letI := Classical.decPred (fun p :
      Finset (Fin (2 ^ (s + 1)) × Fin (2 ^ (s + 1))) ×
      Finset (Fin (2 ^ (s + 1)) × Fin (2 ^ (s + 1))) =>
      IsMaximalBiclique (M_rel (s + 1)) p.1 p.2)
    Fintype.card { p :
      Finset (Fin (2 ^ (s + 1)) × Fin (2 ^ (s + 1))) ×
      Finset (Fin (2 ^ (s + 1)) × Fin (2 ^ (s + 1))) //
      IsMaximalBiclique (M_rel (s + 1)) p.1 p.2 } = 2 * 8 ^ s := by
  classical
  rw [← Fintype.card_congr (M_rel_maxBicliques_equiv s), Fintype.card_prod, Fintype.card_fin]
  convert congrArg (2 * ·) (K_coreRel_maxBicliques_card s)

theorem M_rel_maxBicliques_card_pow (s : ℕ) :
    letI := Classical.decPred (fun p :
      Finset (Fin (2 ^ (s + 1)) × Fin (2 ^ (s + 1))) ×
      Finset (Fin (2 ^ (s + 1)) × Fin (2 ^ (s + 1))) =>
      IsMaximalBiclique (M_rel (s + 1)) p.1 p.2)
    Fintype.card { p :
      Finset (Fin (2 ^ (s + 1)) × Fin (2 ^ (s + 1))) ×
      Finset (Fin (2 ^ (s + 1)) × Fin (2 ^ (s + 1))) //
      IsMaximalBiclique (M_rel (s + 1)) p.1 p.2 } = 2 ^ (3 * (s + 1) - 2) := by
  classical
  rw [show Fintype.card _ = 2 * 8 ^ s from M_rel_maxBicliques_card s]
  calc 2 * 8 ^ s = 2 * (2 ^ 3) ^ s := by norm_num
    _ = 2 * 2 ^ (3 * s) := by rw [← pow_mul]
    _ = 2 ^ (3 * s + 1) := (pow_succ' 2 (3 * s)).symm
    _ = 2 ^ (3 * (s + 1) - 2) := congrArg (2 ^ ·) (by omega)

/-- Theorem 2.1(c): Exact maximum biclique area `A_max(M_{s+1}) = 2^(s + 2)` is attained. -/
theorem M_rel_maxBiclique_area_attained (s : ℕ) :
    ∃ U V : Finset (Fin (2 ^ (s + 1)) × Fin (2 ^ (s + 1))),
      IsMaximalBiclique (M_rel (s + 1)) U V ∧ U.card * V.card = 2 ^ (s + 2) := by
  rcases K_coreRel_maxBiclique_area_attained s with ⟨Uc, Vc, hmax, harea⟩
  refine ⟨liftM_U s 0 Uc, liftM_V s 0 Vc,
    (M_rel_maxBicliques_equiv s (0, ⟨(Uc, Vc), hmax⟩)).2, ?_⟩
  rw [card_liftM_U, card_liftM_V]
  calc 2 * Uc.card * (2 * Vc.card) = 4 * (Uc.card * Vc.card) := by ring
    _ = 4 * 2 ^ s := by rw [harea]
    _ = 2 ^ (s + 2) := by ring

end CarryAutomaton
