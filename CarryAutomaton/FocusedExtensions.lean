module

public import CarryAutomaton.CoreBicliques
public import CarryAutomaton.NegacyclicSpectrum
public import CarryAutomaton.CyclicCutAndLocalCover
import Mathlib.Tactic

@[expose] public section

/-!
# Focused Extensions for `CarryAutomaton`

Formalization of:
1. Direct abelian group-circulant invariance of `M_rel` and `K_coreRel` (Section 4, Equation (4.1):
   `M_rel_group_circulant`, `K_coreRel_group_circulant`).
2. All-field exact ranks of `K_coreMat` (`C_t`) and `M_mat`, both for `char F ≠ 2` via the
   integer telescoping inverse of `G_α(T_neg)` (`rank_K_coreMat_char_ne_two`,
   `rank_M_mat_char_ne_two`; Theorem 4.1(b), Equations (4.5) and (4.8)) and for `CharP F 2` via
   involutory `2 × 2` block shears and nilpotent cyclic shifts (`rank_K_coreMat_char_two`,
   `rank_M_mat_char_two`; Theorem 4.1(b)).
3. Real-weighted universal lower bound and attainment for `M_rel` (Theorem 2.4(b), Equation (2.12):
   `weighted_sum_M_lower_real`, `weighted_sum_M_attained_real`).
4. Exact equality characterizations for `bc(M_t)` and `totalRowLoad * totalColLoad`
   (Theorem 2.4(b), Equations (2.10)–(2.11): `bc_M_eq_iff`, `prod_load_M_eq_iff`).
5. General reusable combinatorial balanced 4-star blowup lemma
   (Lemma 3.1: `abstract_balanced_star_blowup`).
6. Embedded `s`-bit Set Disjointness in `K_coreRel s`, linear all-zeros rectangle cover,
   and explicit signed margin witness (Proposition 4.2(c), Equation (4.10):
   `disj_embedded_in_K_coreRel`, `zero_cover_K_coreRel_card_le_eight_s`,
   `margin_witness_K_coreRel`).
-/

namespace CarryAutomaton

open Finset BigOperators Matrix

/-! ### 1. Abelian Group-Circulant Invariance (`M_rel_group_circulant`, `K_coreRel_group_circulant`) -/

/-- Bitwise XOR operation on `Fin (2 ^ t)`, making `Fin (2 ^ t)` an elementary abelian 2-group. -/
def xorFin (t : ℕ) (a b : Fin (2 ^ t)) : Fin (2 ^ t) :=
  ⟨a.val ^^^ b.val, Nat.xor_lt_two_pow a.isLt b.isLt⟩

/-- Modular addition `(a + b) mod 2^t` on `Fin (2 ^ t)`. -/
def addModFin (t : ℕ) (a b : Fin (2 ^ t)) : Fin (2 ^ t) :=
  ⟨(a.val + b.val) % 2 ^ t, Nat.mod_lt _ (by positivity)⟩

@[simp]
lemma xorFin_val (t : ℕ) (a b : Fin (2 ^ t)) : (xorFin t a b).val = a.val ^^^ b.val := rfl

@[simp]
lemma addModFin_val (t : ℕ) (a b : Fin (2 ^ t)) :
    (addModFin t a b).val = (a.val + b.val) % 2 ^ t := rfl

private lemma nat_xor_cancel_shift (u v a : ℕ) : (u ^^^ a) ^^^ (v ^^^ a) = u ^^^ v := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases u.testBit i <;> cases v.testBit i <;> cases a.testBit i <;> rfl

private lemma mod_sub_shift_inv {M w z b : ℕ} (hw : w < M) (hz : z < M) (hb : b < M) :
    ((z + b) % M + M - (w + b) % M) % M = (z + M - w) % M := by
  by_cases hwb : w + b < M <;> by_cases hzb : z + b < M
  · rw [Nat.mod_eq_of_lt hwb, Nat.mod_eq_of_lt hzb]
    have heq : z + b + M - (w + b) = z + M - w := by omega
    rw [heq]
  · rw [Nat.mod_eq_of_lt hwb]
    have hzm : (z + b) % M = z + b - M := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hzm]
    have heq1 : z + b - M + M - (w + b) = z - w := by omega
    have heq2 : z + M - w = (z - w) + M := by omega
    rw [heq1, heq2, Nat.add_mod_right]
  · have hwm : (w + b) % M = w + b - M := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hwm, Nat.mod_eq_of_lt hzb]
    have heq : z + b + M - (w + b - M) = (z + M - w) + M := by omega
    rw [heq, Nat.add_mod_right]
  · have hwm : (w + b) % M = w + b - M := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have hzm : (z + b) % M = z + b - M := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hwm, hzm]
    have heq : z + b - M + M - (w + b - M) = z + M - w := by omega
    rw [heq]

/-- Direct abelian group-circulant representation and `(𝔽₂^t × ℤ/2^tℤ)`-translation invariance
of `M_rel t`. -/
theorem M_rel_group_circulant (t : ℕ) (u v w z a b : Fin (2 ^ t)) :
    (M_rel t (u, w) (v, z) ↔ (xorFin t u v).val = (z.val + 2 ^ t - w.val) % 2 ^ t) ∧
    (M_rel t (xorFin t u a, addModFin t w b) (xorFin t v a, addModFin t z b) ↔
      M_rel t (u, w) (v, z)) := by
  have hbase : ∀ u' v' w' z' : Fin (2 ^ t),
      M_rel t (u', w') (v', z') ↔ (xorFin t u' v').val = (z'.val + 2 ^ t - w'.val) % 2 ^ t := by
    intro u' v' w' z'
    rw [M_rel_iff_eq_sub]
    have hw' : w'.val < 2 ^ t := w'.isLt
    have hsub : z'.val + (2 ^ t - w'.val) = z'.val + 2 ^ t - w'.val := by omega
    rw [hsub]
    rfl
  refine ⟨hbase u v w z, ?_⟩
  rw [hbase, hbase]
  simp only [xorFin_val, addModFin_val, nat_xor_cancel_shift,
    mod_sub_shift_inv w.isLt z.isLt b.isLt]

/-- Coordinate equivalence between `(x', w') ∈ 𝔽₂^s × Fin (2^s)` (`s ≥ 1`) and the abelian
group `(Fin (s - 1) → ZMod 2) × Fin (2 ^ (s + 1))` (`𝔽₂^{s-1} × ℤ/2^{s+1}ℤ`) on which
`K_coreRel s` is literally group-circulant. -/
def coreCirculantEquiv {s : ℕ} (hs : 1 ≤ s) :
    ((Fin s → ZMod 2) × Fin (2 ^ s)) ≃ (Fin (s - 1) → ZMod 2) × Fin (2 ^ (s + 1)) where
  toFun p :=
    ( fun i => p.1 ⟨i.val, by omega⟩ + natBit p.2.val (i.val + 1),
      ⟨p.2.val + (p.1 ⟨s - 1, by omega⟩).val * 2 ^ s, by
        have hw := p.2.isLt
        have hb : (p.1 ⟨s - 1, by omega⟩).val ≤ 1 := by
          have := (p.1 ⟨s - 1, by omega⟩).val_lt; omega
        have hmul : (p.1 ⟨s - 1, by omega⟩).val * 2 ^ s ≤ 2 ^ s := by
          calc (p.1 ⟨s - 1, by omega⟩).val * 2 ^ s ≤ 1 * 2 ^ s := Nat.mul_le_mul_right _ hb
            _ = 2 ^ s := one_mul _
        have hpow : 2 ^ (s + 1) = 2 ^ s + 2 ^ s := by ring
        omega⟩ )
  invFun q :=
    let w' : Fin (2 ^ s) := ⟨q.2.val % 2 ^ s, Nat.mod_lt _ (by positivity)⟩
    let x' : Fin s → ZMod 2 := fun i =>
      if hi : i.val < s - 1 then
        q.1 ⟨i.val, hi⟩ + natBit w'.val (i.val + 1)
      else
        ((q.2.val / 2 ^ s : ℕ) : ZMod 2)
    (x', w')
  left_inv p := by
    rcases p with ⟨x', w'⟩
    have hw_lt : w'.val < 2 ^ s := w'.isLt
    have hmod : (w'.val + (x' ⟨s - 1, by omega⟩).val * 2 ^ s) % 2 ^ s = w'.val := by
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hw_lt]
    have hdiv : (w'.val + (x' ⟨s - 1, by omega⟩).val * 2 ^ s) / 2 ^ s =
        (x' ⟨s - 1, by omega⟩).val := by
      rw [Nat.add_mul_div_right _ _ (by positivity : 0 < 2 ^ s), Nat.div_eq_of_lt hw_lt, zero_add]
    refine Prod.ext ?_ ?_
    · funext i
      dsimp only
      by_cases hi : i.val < s - 1
      · simp only [hi, ↓reduceDIte, hmod]
        rw [add_assoc, zmod2_add_self, add_zero]
      · simp only [hi, ↓reduceDIte, hdiv, ZMod.natCast_zmod_val]
        have hidx : (⟨s - 1, by omega⟩ : Fin s) = i := Fin.ext (by dsimp; omega)
        rw [hidx]
    · apply Fin.ext
      dsimp only
      exact hmod
  right_inv q := by
    rcases q with ⟨u_low, W⟩
    have hdiv_lt : W.val / 2 ^ s < 2 := by
      have hW : W.val < 2 ^ s * 2 := by simpa [pow_succ] using W.isLt
      exact Nat.div_lt_of_lt_mul (by linarith)
    have hcast_val : (((W.val / 2 ^ s : ℕ) : ZMod 2)).val = W.val / 2 ^ s := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hdiv_lt]
    refine Prod.ext ?_ ?_
    · funext i
      dsimp only
      simp only [i.isLt, ↓reduceDIte]
      rw [add_assoc, zmod2_add_self, add_zero]
    · apply Fin.ext
      dsimp only
      simp only [lt_irrefl, ↓reduceDIte, hcast_val]
      rw [mul_comm, add_comm]
      exact Nat.div_add_mod W.val (2 ^ s)

/-- Direct `𝔽₂^s`-shift invariance of `K_coreRel s` and full `(𝔽₂^{s-1} × ℤ/2^{s+1}ℤ)`
abelian group-circulant characterization & translation invariance for `s ≥ 1`. -/
theorem K_coreRel_group_circulant (s : ℕ) :
    (∀ (r c : (Fin s → ZMod 2) × Fin (2 ^ s)) (a : Fin s → ZMod 2),
      K_coreRel s (r.1 + a, r.2) (c.1 + a, c.2) ↔ K_coreRel s r c) ∧
    (∀ (hs : 1 ≤ s) (r c : (Fin s → ZMod 2) × Fin (2 ^ s)),
      let rG := coreCirculantEquiv hs r
      let cG := coreCirculantEquiv hs c
      let D := (cG.2.val + 2 ^ (s + 1) - rG.2.val) % 2 ^ (s + 1)
      (K_coreRel s r c ↔
        D < 2 ^ s ∧ ∀ i : Fin (s - 1), rG.1 i + cG.1 i = natBit D (i.val + 1)) ∧
      ∀ (a : Fin (s - 1) → ZMod 2) (b : Fin (2 ^ (s + 1))),
        K_coreRel s ((coreCirculantEquiv hs).symm (rG.1 + a, addModFin (s + 1) rG.2 b))
          ((coreCirculantEquiv hs).symm (cG.1 + a, addModFin (s + 1) cG.2 b)) ↔
          K_coreRel s r c) := by
  refine ⟨?_, ?_⟩
  · intro r c a
    simp only [K_coreRel]
    have hcancel : (r.1 + a) + (c.1 + a) = r.1 + c.1 := by
      ext i
      simp only [Pi.add_apply]
      calc r.1 i + a i + (c.1 i + a i)
          = r.1 i + c.1 i + (a i + a i) := by ring
        _ = r.1 i + c.1 i := by rw [zmod2_add_self, add_zero]
    rw [hcancel]
  · intro hs r c
    dsimp only
    set rG := coreCirculantEquiv hs r
    set cG := coreCirculantEquiv hs c
    have hchar : ∀ r' c' : (Fin s → ZMod 2) × Fin (2 ^ s),
        let rG' := coreCirculantEquiv hs r'
        let cG' := coreCirculantEquiv hs c'
        let D' := (cG'.2.val + 2 ^ (s + 1) - rG'.2.val) % 2 ^ (s + 1)
        K_coreRel s r' c' ↔
          D' < 2 ^ s ∧ ∀ i : Fin (s - 1), rG'.1 i + cG'.1 i = natBit D' (i.val + 1) := by
      intro r' c'
      dsimp only
      set W := (coreCirculantEquiv hs r').2.val
      set Z := (coreCirculantEquiv hs c').2.val
      set D' := (Z + 2 ^ (s + 1) - W) % 2 ^ (s + 1)
      have hW_eq : W = r'.2.val + (r'.1 ⟨s - 1, by omega⟩).val * 2 ^ s := rfl
      have hZ_eq : Z = c'.2.val + (c'.1 ⟨s - 1, by omega⟩).val * 2 ^ s := rfl
      have hW_lt : W < 2 ^ (s + 1) := (coreCirculantEquiv hs r').2.isLt
      have hZ_lt : Z < 2 ^ (s + 1) := (coreCirculantEquiv hs c').2.isLt
      have hr2_lt : r'.2.val < 2 ^ s := r'.2.isLt
      have hc2_lt : c'.2.val < 2 ^ s := c'.2.isLt
      have hrx_lt : (r'.1 ⟨s - 1, by omega⟩).val < 2 := (r'.1 _).val_lt
      have hcx_lt : (c'.1 ⟨s - 1, by omega⟩).val < 2 := (c'.1 _).val_lt
      have hpow_s1 : 2 ^ (s + 1) = 2 ^ s + 2 ^ s := by ring
      -- Relate D' % 2^s to (c'.2 - r'.2) mod 2^s and D' < 2^s to top bit of K_coreRel
      let d_lo := (c'.2.val + 2 ^ s - r'.2.val) % 2 ^ s
      have hd_lo_lt : d_lo < 2 ^ s := Nat.mod_lt _ (by positivity)
      have hadd_lo : (d_lo + r'.2.val) % 2 ^ s = c'.2.val := by
        dsimp only [d_lo]
        rw [Nat.mod_add_mod]
        have : c'.2.val + 2 ^ s - r'.2.val + r'.2.val = c'.2.val + 2 ^ s := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hc2_lt]
      have hD'_mod : D' % 2 ^ s = d_lo := by
        dsimp only [D', d_lo]
        rw [hW_eq, hZ_eq]
        have hdvd : 2 ^ s ∣ 2 ^ (s + 1) := ⟨2, by ring⟩
        rw [Nat.mod_mod_of_dvd _ hdvd]
        by_cases hrx : (r'.1 ⟨s - 1, by omega⟩).val = 0 <;>
          by_cases hcx : (c'.1 ⟨s - 1, by omega⟩).val = 0
        · simp only [hrx, hcx, zero_mul, add_zero]
          have : c'.2.val + 2 ^ (s + 1) - r'.2.val = (c'.2.val + 2 ^ s - r'.2.val) + 2 ^ s := by omega
          rw [this, Nat.add_mod_right]
        · have hcx1 : (c'.1 ⟨s - 1, by omega⟩).val = 1 := by omega
          simp only [hrx, hcx1, zero_mul, one_mul, add_zero]
          have : c'.2.val + 2 ^ s + 2 ^ (s + 1) - r'.2.val =
              (c'.2.val + 2 ^ s - r'.2.val) + 2 * 2 ^ s := by omega
          rw [this, Nat.add_mul_mod_self_right]
        · have hrx1 : (r'.1 ⟨s - 1, by omega⟩).val = 1 := by omega
          simp only [hrx1, hcx, zero_mul, one_mul, add_zero]
          have : c'.2.val + 2 ^ (s + 1) - (r'.2.val + 2 ^ s) = c'.2.val + 2 ^ s - r'.2.val := by omega
          rw [this]
        · have hrx1 : (r'.1 ⟨s - 1, by omega⟩).val = 1 := by omega
          have hcx1 : (c'.1 ⟨s - 1, by omega⟩).val = 1 := by omega
          simp only [hrx1, hcx1, one_mul]
          have : c'.2.val + 2 ^ s + 2 ^ (s + 1) - (r'.2.val + 2 ^ s) =
              (c'.2.val + 2 ^ s - r'.2.val) + 2 ^ s := by omega
          rw [this, Nat.add_mod_right]
      have htop_iff : D' < 2 ^ s ↔
          r'.1 ⟨s - 1, by omega⟩ + c'.1 ⟨s - 1, by omega⟩ =
            borrowBit s r'.2.val c'.2.val := by
        dsimp only [D']
        rw [hW_eq, hZ_eq]
        unfold borrowBit
        rw [Nat.mod_eq_of_lt hr2_lt, Nat.mod_eq_of_lt hc2_lt]
        generalize hb1 : r'.1 ⟨s - 1, by omega⟩ = b1
        generalize hb2 : c'.1 ⟨s - 1, by omega⟩ = b2
        by_cases hlt : c'.2.val < r'.2.val
        · simp only [hlt, ↓reduceIte]
          fin_cases b1 <;> fin_cases b2
          · change (c'.2.val + 0 * 2 ^ s + 2 ^ (s + 1) - (r'.2.val + 0 * 2 ^ s)) % 2 ^ (s + 1) < 2 ^ s ↔
              (0 : ZMod 2) + 0 = 1
            have hlt' : c'.2.val + 0 * 2 ^ s + 2 ^ (s + 1) - (r'.2.val + 0 * 2 ^ s) < 2 ^ (s + 1) := by
              omega
            have hval : (c'.2.val + 0 * 2 ^ s + 2 ^ (s + 1) - (r'.2.val + 0 * 2 ^ s)) % 2 ^ (s + 1) =
                c'.2.val + 2 ^ (s + 1) - r'.2.val := by
              rw [Nat.mod_eq_of_lt hlt']
              omega
            rw [hval]; simp [show ¬(c'.2.val + 2 ^ (s + 1) - r'.2.val < 2 ^ s) by omega]
          · change (c'.2.val + 1 * 2 ^ s + 2 ^ (s + 1) - (r'.2.val + 0 * 2 ^ s)) % 2 ^ (s + 1) < 2 ^ s ↔
              (0 : ZMod 2) + 1 = 1
            have heq : c'.2.val + 1 * 2 ^ s + 2 ^ (s + 1) - (r'.2.val + 0 * 2 ^ s) =
                (c'.2.val + 2 ^ s - r'.2.val) + 2 ^ (s + 1) := by omega
            rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            simp [show c'.2.val + 2 ^ s - r'.2.val < 2 ^ s by omega]
          · change (c'.2.val + 0 * 2 ^ s + 2 ^ (s + 1) - (r'.2.val + 1 * 2 ^ s)) % 2 ^ (s + 1) < 2 ^ s ↔
              (1 : ZMod 2) + 0 = 1
            have heq : c'.2.val + 0 * 2 ^ s + 2 ^ (s + 1) - (r'.2.val + 1 * 2 ^ s) =
                c'.2.val + 2 ^ s - r'.2.val := by omega
            rw [heq, Nat.mod_eq_of_lt (by omega)]
            simp [show c'.2.val + 2 ^ s - r'.2.val < 2 ^ s by omega]
          · change (c'.2.val + 1 * 2 ^ s + 2 ^ (s + 1) - (r'.2.val + 1 * 2 ^ s)) % 2 ^ (s + 1) < 2 ^ s ↔
              (1 : ZMod 2) + 1 = 1
            have heq : c'.2.val + 1 * 2 ^ s + 2 ^ (s + 1) - (r'.2.val + 1 * 2 ^ s) =
                c'.2.val + 2 ^ (s + 1) - r'.2.val := by omega
            rw [heq, Nat.mod_eq_of_lt (by omega)]
            have hfalse : (1 : ZMod 2) + 1 ≠ 1 := by decide
            simp [show ¬(c'.2.val + 2 ^ (s + 1) - r'.2.val < 2 ^ s) by omega, hfalse]
        · simp only [hlt, ↓reduceIte]
          fin_cases b1 <;> fin_cases b2
          · change (c'.2.val + 0 * 2 ^ s + 2 ^ (s + 1) - (r'.2.val + 0 * 2 ^ s)) % 2 ^ (s + 1) < 2 ^ s ↔
              (0 : ZMod 2) + 0 = 0
            have heq : c'.2.val + 0 * 2 ^ s + 2 ^ (s + 1) - (r'.2.val + 0 * 2 ^ s) =
                (c'.2.val - r'.2.val) + 2 ^ (s + 1) := by omega
            rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            simp [show c'.2.val - r'.2.val < 2 ^ s by omega]
          · change (c'.2.val + 1 * 2 ^ s + 2 ^ (s + 1) - (r'.2.val + 0 * 2 ^ s)) % 2 ^ (s + 1) < 2 ^ s ↔
              (0 : ZMod 2) + 1 = 0
            have heq : c'.2.val + 1 * 2 ^ s + 2 ^ (s + 1) - (r'.2.val + 0 * 2 ^ s) =
                (c'.2.val - r'.2.val + 2 ^ s) + 2 ^ (s + 1) := by omega
            rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            simp [show ¬(c'.2.val - r'.2.val + 2 ^ s < 2 ^ s) by omega]
          · change (c'.2.val + 0 * 2 ^ s + 2 ^ (s + 1) - (r'.2.val + 1 * 2 ^ s)) % 2 ^ (s + 1) < 2 ^ s ↔
              (1 : ZMod 2) + 0 = 0
            have heq : c'.2.val + 0 * 2 ^ s + 2 ^ (s + 1) - (r'.2.val + 1 * 2 ^ s) =
                c'.2.val - r'.2.val + 2 ^ s := by omega
            rw [heq, Nat.mod_eq_of_lt (by omega)]
            simp [show ¬(c'.2.val - r'.2.val + 2 ^ s < 2 ^ s) by omega]
          · change (c'.2.val + 1 * 2 ^ s + 2 ^ (s + 1) - (r'.2.val + 1 * 2 ^ s)) % 2 ^ (s + 1) < 2 ^ s ↔
              (1 : ZMod 2) + 1 = 0
            have heq : c'.2.val + 1 * 2 ^ s + 2 ^ (s + 1) - (r'.2.val + 1 * 2 ^ s) =
                (c'.2.val - r'.2.val) + 2 ^ (s + 1) := by omega
            rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            have htrue : (1 : ZMod 2) + 1 = 0 := by decide
            simp [show c'.2.val - r'.2.val < 2 ^ s by omega, htrue]
      have hlow_bits : ∀ i : Fin (s - 1),
          natBit d_lo (i.val + 1) =
            natBit r'.2.val (i.val + 1) + natBit c'.2.val (i.val + 1) +
              borrowBit (i.val + 1) r'.2.val c'.2.val := by
        intro i
        have htb := testBit_add_mod_two_pow hadd_lo (by omega : i.val + 1 < s)
        have h2z : ∀ n k : ℕ, natBit n k = if n.testBit k then 1 else 0 := by
          intro n k
          rw [natBit, Nat.testBit_eq_decide_div_mod_eq, ← ZMod.natCast_mod]
          rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ k) with h0 | h1
          · simp [h0]
          · simp [h1]
        rw [h2z, h2z, h2z]
        unfold borrowBit
        revert htb
        generalize d_lo.testBit (i.val + 1) = bd
        generalize r'.2.val.testBit (i.val + 1) = bw
        generalize c'.2.val.testBit (i.val + 1) = bz
        by_cases hlt : c'.2.val % 2 ^ (i.val + 1) < r'.2.val % 2 ^ (i.val + 1)
        · simp only [hlt, decide_true, ↓reduceIte]
          cases bd <;> cases bw <;> cases bz <;> decide
        · simp only [hlt, decide_false, ↓reduceIte]
          cases bd <;> cases bw <;> cases bz <;> decide
      constructor
      · intro hrel
        have htop_rel : r'.1 ⟨s - 1, by omega⟩ + c'.1 ⟨s - 1, by omega⟩ =
            borrowBit s r'.2.val c'.2.val := by
          have := congrFun hrel ⟨s - 1, by omega⟩
          simpa [Pi.add_apply, borrowVec, show s - 1 + 1 = s by omega] using this
        have hD'_lt : D' < 2 ^ s := htop_iff.mpr htop_rel
        have hD'_eq : D' = d_lo := by rw [← hD'_mod, Nat.mod_eq_of_lt hD'_lt]
        refine ⟨hD'_lt, fun i => ?_⟩
        rw [hD'_eq, hlow_bits i]
        have hi := congrFun hrel ⟨i.val, by omega⟩
        simp only [Pi.add_apply, borrowVec] at hi
        change (r'.1 ⟨i.val, by omega⟩ + natBit r'.2.val (i.val + 1)) +
          (c'.1 ⟨i.val, by omega⟩ + natBit c'.2.val (i.val + 1)) = _
        calc (r'.1 ⟨i.val, by omega⟩ + natBit r'.2.val (i.val + 1)) +
              (c'.1 ⟨i.val, by omega⟩ + natBit c'.2.val (i.val + 1))
            = (r'.1 ⟨i.val, by omega⟩ + c'.1 ⟨i.val, by omega⟩) +
              natBit r'.2.val (i.val + 1) + natBit c'.2.val (i.val + 1) := by ring
          _ = borrowBit (i.val + 1) r'.2.val c'.2.val +
              natBit r'.2.val (i.val + 1) + natBit c'.2.val (i.val + 1) := by rw [hi]
          _ = natBit r'.2.val (i.val + 1) + natBit c'.2.val (i.val + 1) +
              borrowBit (i.val + 1) r'.2.val c'.2.val := by ring
      · rintro ⟨hD'_lt, hlow⟩
        have hD'_eq : D' = d_lo := by rw [← hD'_mod, Nat.mod_eq_of_lt hD'_lt]
        unfold K_coreRel
        funext i
        simp only [Pi.add_apply, borrowVec]
        by_cases hi : i.val < s - 1
        · have hli := hlow ⟨i.val, hi⟩
          rw [hD'_eq, hlow_bits ⟨i.val, hi⟩] at hli
          change (r'.1 i + natBit r'.2.val (i.val + 1)) +
            (c'.1 i + natBit c'.2.val (i.val + 1)) = _ at hli
          calc r'.1 i + c'.1 i
              = ((r'.1 i + natBit r'.2.val (i.val + 1)) +
                  (c'.1 i + natBit c'.2.val (i.val + 1))) +
                natBit r'.2.val (i.val + 1) + natBit c'.2.val (i.val + 1) := by
                  have h1 := zmod2_add_self (natBit r'.2.val (i.val + 1))
                  have h2 := zmod2_add_self (natBit c'.2.val (i.val + 1))
                  calc r'.1 i + c'.1 i
                      = r'.1 i + c'.1 i +
                        (natBit r'.2.val (i.val + 1) + natBit r'.2.val (i.val + 1)) +
                        (natBit c'.2.val (i.val + 1) + natBit c'.2.val (i.val + 1)) := by
                          rw [h1, h2, add_zero, add_zero]
                    _ = _ := by ring
            _ = (natBit r'.2.val (i.val + 1) + natBit c'.2.val (i.val + 1) +
                  borrowBit (i.val + 1) r'.2.val c'.2.val) +
                natBit r'.2.val (i.val + 1) + natBit c'.2.val (i.val + 1) := by rw [hli]
            _ = (natBit r'.2.val (i.val + 1) + natBit r'.2.val (i.val + 1)) +
                (natBit c'.2.val (i.val + 1) + natBit c'.2.val (i.val + 1)) +
                borrowBit (i.val + 1) r'.2.val c'.2.val := by ring
            _ = borrowBit (i.val + 1) r'.2.val c'.2.val := by
                  rw [zmod2_add_self, zmod2_add_self, add_zero, zero_add]
        · have hidx : i = ⟨s - 1, by omega⟩ := Fin.ext (by dsimp; omega)
          rw [hidx]
          simpa [show s - 1 + 1 = s by omega] using htop_iff.mp hD'_lt
    refine ⟨hchar r c, fun a b => ?_⟩
    have h1 := hchar ((coreCirculantEquiv hs).symm (rG.1 + a, addModFin (s + 1) rG.2 b))
      ((coreCirculantEquiv hs).symm (cG.1 + a, addModFin (s + 1) cG.2 b))
    have h2 := hchar r c
    dsimp only at h1 h2
    rw [h1, h2]
    simp only [Equiv.apply_symm_apply, addModFin_val, mod_sub_shift_inv rG.2.isLt cG.2.isLt b.isLt]
    refine and_congr_right fun _ => forall_congr' fun i => ?_
    have hcancel : (rG.1 + a) i + (cG.1 + a) i = rG.1 i + cG.1 i := by
      simp only [Pi.add_apply]
      calc rG.1 i + a i + (cG.1 i + a i)
          = rG.1 i + cG.1 i + (a i + a i) := by ring
        _ = rG.1 i + cG.1 i := by rw [zmod2_add_self, add_zero]
    rw [hcancel]

/-! ### 2. All-Field Exact Ranks (`char F ≠ 2` and `CharP F 2`) -/

private lemma isUnit_det_of_right_inv {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (A B : Matrix n n R) (h : A * B = 1) : IsUnit A.det :=
  (Matrix.isUnit_iff_isUnit_det A).mp ⟨⟨A, B, h, mul_eq_one_comm.mp h⟩, rfl⟩

/-- Reindexing `M_mat R (s + 1)` by `phi_row s` and `phi_col s` gives `I_2 ⊗ K_coreMat R s ⊗ J_2`
over any commutative ring `R`. -/
theorem M_mat_reindex_phi_eq_kronecker (R : Type*) [CommRing R] (s : ℕ) :
    (M_mat R (s + 1)).reindex (phi_row s) (phi_col s) =
      Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) R)
        (Matrix.kroneckerMap (· * ·) (K_coreMat R s) (allOnesMat R 2)) := by
  ext r c
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, allOnesMat, mul_one, M_mat, K_coreMat]
  have hiff := M_rel_core_factorization s ((phi_row s).symm r) ((phi_col s).symm c)
  simp only [Equiv.apply_symm_apply] at hiff
  by_cases h1 : r.1 = c.1
  · by_cases h2 : K_coreRel s r.2.1 c.2.1
    · have hm : M_rel (s + 1) ((phi_row s).symm r) ((phi_col s).symm c) := hiff.mpr ⟨h1, h2⟩
      simp [h1, h2, hm]
    · have hm : ¬ M_rel (s + 1) ((phi_row s).symm r) ((phi_col s).symm c) :=
        fun h => h2 (hiff.mp h).2
      simp [h1, h2, hm]
  · have hm : ¬ M_rel (s + 1) ((phi_row s).symm r) ((phi_col s).symm c) :=
      fun h => h1 (hiff.mp h).1
    simp [h1, hm]

/-- Over EVERY field `F` (regardless of characteristic), `rank_F(M_{s+1}) = 2 * rank_F(K_{s+1})`. -/
theorem rank_M_mat_eq_two_mul_rank_K_coreMat (F : Type*) [Field F] (s : ℕ) :
    (M_mat F (s + 1)).rank = 2 * (K_coreMat F s).rank := by
  rw [← Matrix.rank_reindex (phi_row s) (phi_col s), M_mat_reindex_phi_eq_kronecker F s,
    rank_kronecker_field, rank_kronecker_field, Matrix.rank_one, Fintype.card_fin,
    rank_allOnesMat (by decide), mul_one]

/-! #### 2a. Characteristic `≠ 2`: Integer Telescoping Product for `G_α(T_neg)` -/

private def tailProdInt (r : ℕ) : ℕ → Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℤ
  | 0 => 1
  | d + 1 => (1 + (T_neg ℤ r) ^ (2 ^ (r - (d + 1)))) * tailProdInt r d

private lemma telescoping_T_neg_int (r : ℕ) :
    ∀ d ≤ r, (1 - (T_neg ℤ r) ^ (2 ^ (r - d))) * tailProdInt r d = (2 : ℤ) • 1 := by
  intro d
  induction d with
  | zero =>
    intro _
    simp only [Nat.sub_zero, tailProdInt, mul_one, T_neg_pow_two_pow]
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  | succ d ih =>
    intro hd
    simp only [tailProdInt]
    set X := (T_neg ℤ r) ^ (2 ^ (r - (d + 1)))
    have hsq : (1 - X) * (1 + X) = 1 - (T_neg ℤ r) ^ (2 ^ (r - d)) := by
      have h1 : (1 - X) * (1 + X) = 1 - X * X := by
        rw [mul_add, sub_mul, sub_mul]
        simp only [mul_one, one_mul]
        abel
      have h2 : X * X = (T_neg ℤ r) ^ (2 ^ (r - d)) := by
        dsimp only [X]
        rw [← pow_add, ← two_mul, ← pow_succ', show r - (d + 1) + 1 = r - d by omega]
      rw [h1, h2]
    rw [← Matrix.mul_assoc, hsq]
    exact ih (by omega)

private lemma G_alphaFactor_mul_adj_int (s r : ℕ) (α : Fin s → ZMod 2) {j : ℕ} (hj : j < r) :
    ∃ Qj : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℤ,
      G_alphaFactor ℤ s r α j * Qj = (2 : ℤ) • 1 := by
  let sgn : ℤ := (-1 : ℤ) ^ (alphaCoeff s α j).val
  let Y : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℤ := (T_neg ℤ r) ^ (2 ^ j)
  refine ⟨(1 - sgn • Y) * tailProdInt r (r - (j + 1)), ?_⟩
  have hfac : G_alphaFactor ℤ s r α j * (1 - sgn • Y) = 1 - (T_neg ℤ r) ^ (2 ^ (j + 1)) := by
    change (1 + sgn • Y) * (1 - sgn • Y) = _
    rw [mul_sub, add_mul, add_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]
    simp only [mul_one, one_mul]
    have hsgn : sgn * sgn = 1 := neg_one_pow_zmod2_mul_self (alphaCoeff s α j)
    have hYY : Y * Y = (T_neg ℤ r) ^ (2 ^ (j + 1)) := by
      dsimp only [Y]
      rw [← pow_add, ← two_mul, ← pow_succ']
    rw [hsgn, one_smul, hYY]
    abel
  rw [← Matrix.mul_assoc, hfac]
  have hsub : r - (r - (j + 1)) = j + 1 := by omega
  have htel := telescoping_T_neg_int r (r - (j + 1)) (by omega)
  rwa [hsub] at htel

/-- Over `ℤ`, `G_α(T_neg)` has an explicit integer polynomial inverse up to `2^r I_{2^r}`. -/
theorem G_alphaMat_mul_adj_int (s r : ℕ) (α : Fin s → ZMod 2) :
    ∃ Q : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℤ,
      G_alphaMat ℤ s r α * Q = ((2 : ℤ) ^ r) • 1 := by
  suffices ∀ m ≤ r, ∃ Q : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℤ,
      ((List.range m).map (G_alphaFactor ℤ s r α)).prod * Q = ((2 : ℤ) ^ m) • 1 by
    exact this r le_rfl
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨1, by simp⟩
  | succ m ih =>
    intro hm
    obtain ⟨Qm, hQm⟩ := ih (by omega)
    obtain ⟨Qfac, hQfac⟩ := G_alphaFactor_mul_adj_int s r α (by omega : m < r)
    refine ⟨Qfac * Qm, ?_⟩
    rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton]
    calc (((List.range m).map (G_alphaFactor ℤ s r α)).prod * G_alphaFactor ℤ s r α m) * (Qfac * Qm)
        = ((List.range m).map (G_alphaFactor ℤ s r α)).prod *
            (G_alphaFactor ℤ s r α m * Qfac) * Qm := by simp [Matrix.mul_assoc]
      _ = ((List.range m).map (G_alphaFactor ℤ s r α)).prod * ((2 : ℤ) • 1) * Qm := by rw [hQfac]
      _ = (2 : ℤ) • (((List.range m).map (G_alphaFactor ℤ s r α)).prod * Qm) := by
          rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
      _ = (2 : ℤ) • (((2 : ℤ) ^ m) • 1) := by rw [hQm]
      _ = ((2 : ℤ) ^ (m + 1)) • 1 := by rw [smul_smul, pow_succ']

/-- Over `ℤ`, every reduced block `H̃_α` (`HasHighestBit s α r`) satisfies
`H̃_α * Q = 2^r I_{2^r}` for an explicit integer matrix `Q`. -/
theorem Htilde_alpha_mul_adj_int {s r : ℕ} {α : Fin s → ZMod 2} (h : HasHighestBit s α r) :
    ∃ Q : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℤ,
      Htilde_alpha ℤ s r α * Q = ((2 : ℤ) ^ r) • 1 := by
  obtain ⟨Qg, hQg⟩ := G_alphaMat_mul_adj_int s r α
  let D := D_sign ℤ s r α
  have hDD : D * D = 1 := D_sign_mul_self ℤ s r α
  have hconj := D_sign_conj_Htilde_eq_G_alpha_int h
  refine ⟨D * Qg * D, ?_⟩
  calc Htilde_alpha ℤ s r α * (D * Qg * D)
      = (D * D) * Htilde_alpha ℤ s r α * D * Qg * D := by
          rw [hDD, Matrix.one_mul]; simp [Matrix.mul_assoc]
    _ = D * ((D * Htilde_alpha ℤ s r α * D) * Qg) * D := by simp [Matrix.mul_assoc]
    _ = D * (G_alphaMat ℤ s r α * Qg) * D := by rw [hconj]
    _ = D * (((2 : ℤ) ^ r) • 1) * D := by rw [hQg]
    _ = ((2 : ℤ) ^ r) • (D * D) := by rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    _ = ((2 : ℤ) ^ r) • 1 := by rw [hDD]

private lemma det_Htilde_alpha_char_ne_two_ne_zero {F : Type*} [Field F] (hchar : (2 : F) ≠ 0)
    {s r : ℕ} {α : Fin s → ZMod 2} (h : HasHighestBit s α r) :
    (Htilde_alpha F s r α).det ≠ 0 := by
  obtain ⟨Q, hQ⟩ := Htilde_alpha_mul_adj_int h
  have hmapMul : Htilde_alpha F s r α * (Int.castRingHom F).mapMatrix Q =
      (Int.castRingHom F).mapMatrix (Htilde_alpha ℤ s r α * Q) := by
    ext w z
    simp [Matrix.mul_apply, Htilde_alpha]
  have hmulF : Htilde_alpha F s r α *
      ((((2 : F) ^ r)⁻¹) • (Int.castRingHom F).mapMatrix Q) = 1 := by
    rw [Matrix.mul_smul, hmapMul, hQ]
    have h2r : (2 : F) ^ r ≠ 0 := pow_ne_zero r hchar
    ext w z
    simp only [Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply,
      smul_eq_mul]
    by_cases hwz : w = z
    · subst hwz
      simp [inv_mul_cancel₀ h2r]
    · simp [hwz]
  exact (isUnit_det_of_right_inv _ _ hmulF).ne_zero

private lemma rank_H_alpha_char_ne_two {F : Type*} [Field F] (hchar : (2 : F) ≠ 0)
    {s r : ℕ} {α : Fin s → ZMod 2} (h : HasHighestBit s α r) :
    (H_alpha F s α).rank = 2 ^ r := by
  rw [← Matrix.rank_reindex (divModPowTwoEquiv s r h.2.1) (divModPowTwoEquiv s r h.2.1),
    H_alpha_reindex_eq_kronecker F h, rank_kronecker_field,
    rank_allOnesMat (by positivity), one_mul,
    Matrix.rank_of_det_ne_zero (det_Htilde_alpha_char_ne_two_ne_zero hchar h), Fintype.card_fin]

private lemma rank_K_coreMat_eq_sum_char_ne_two (F : Type*) [Field F] (hchar : (2 : F) ≠ 0)
    (s : ℕ) :
    (K_coreMat F s).rank = ∑ α : Fin s → ZMod 2, (H_alpha F s α).rank := by
  classical
  let W_I := Matrix.kroneckerMap (· * ·) (W_unnorm F s) (1 : Matrix (Fin (2 ^ s)) (Fin (2 ^ s)) F)
  have h2ne : ((2 : F) ^ s) ≠ 0 := pow_ne_zero s hchar
  have hW_inv : W_I * ((((2 : F) ^ s)⁻¹) • W_I) = 1 := by
    rw [Matrix.mul_smul]
    have hmul : W_I * W_I = ((2 : F) ^ s) • 1 := by
      dsimp only [W_I]
      rw [← Matrix.mul_kronecker_mul, W_unnorm_mul_self, mul_one]
      ext ⟨α₁, w₁⟩ ⟨α₂, w₂⟩
      by_cases h1 : α₁ = α₂ <;> by_cases h2 : w₁ = w₂ <;>
        simp [Matrix.kroneckerMap_apply, h1, h2]
    rw [hmul, smul_smul, inv_mul_cancel₀ h2ne, one_smul]
  have hW_unit : IsUnit W_I.det := isUnit_det_of_right_inv W_I _ hW_inv
  have hconj :
      (W_I * K_coreMat F s * W_I).reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _) =
        Matrix.blockDiagonal (fun α : Fin s → ZMod 2 => ((2 : F) ^ s) • H_alpha F s α) := by
    ext ⟨w, α⟩ ⟨z, β⟩
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodComm_symm,
      Equiv.coe_prodComm, Prod.swap_prod_mk]
    dsimp only [W_I]
    rw [walsh_conj_K_coreMat_unnorm]
    by_cases hαβ : α = β
    · subst hαβ; simp
    · simp [Matrix.blockDiagonal_apply, hαβ]
  have hrk : (K_coreMat F s).rank =
      (Matrix.blockDiagonal (fun α : Fin s → ZMod 2 => ((2 : F) ^ s) • H_alpha F s α)).rank := by
    rw [← hconj, Matrix.rank_reindex, Matrix.rank_mul_eq_left_of_isUnit_det W_I _ hW_unit,
      Matrix.rank_mul_eq_right_of_isUnit_det W_I _ hW_unit]
  rw [hrk, rank_blockDiagonal_field]
  refine Finset.sum_congr rfl fun α _ => ?_
  exact Matrix.rank_smul_of_mem_nonZeroDivisors (H_alpha F s α)
    (mem_nonZeroDivisors_of_ne_zero h2ne)

/-- Exact rank of `K_coreMat F s` over EVERY field `F` with `(2 : F) ≠ 0`:
`3 * rank_F(K_{s+1}) = 2 * 4^s + 1`. -/
theorem rank_K_coreMat_char_ne_two (F : Type*) [Field F] (hchar : (2 : F) ≠ 0) (s : ℕ) :
    3 * (K_coreMat F s).rank = 2 * 4 ^ s + 1 := by
  classical
  rw [rank_K_coreMat_eq_sum_char_ne_two F hchar s]
  have heq : ∀ α : Fin s → ZMod 2, (H_alpha F s α).rank = (H_alpha ℚ s α).rank := by
    intro α
    by_cases hα : α = 0
    · subst hα
      rw [rank_H_alpha_zero F s, rank_H_alpha_zero ℚ s]
    · obtain ⟨r, hr, _⟩ := existsUnique_hasHighestBit s hα
      rw [rank_H_alpha_char_ne_two hchar hr, rank_H_alpha_Q hr]
  simp_rw [heq]
  have hQ := rank_K_coreMat_eq_sum_char_ne_two ℚ (by norm_num) s
  rw [← hQ]
  exact rank_K_coreMat_Q s

/-- Exact rank of `M_mat F (s + 1)` over EVERY field `F` with `(2 : F) ≠ 0`:
`3 * rank_F(M_{s+1}) = 4^{s+1} + 2`. -/
theorem rank_M_mat_char_ne_two (F : Type*) [Field F] (hchar : (2 : F) ≠ 0) (s : ℕ) :
    3 * (M_mat F (s + 1)).rank = 4 ^ (s + 1) + 2 := by
  rw [rank_M_mat_eq_two_mul_rank_K_coreMat F s]
  have hK := rank_K_coreMat_char_ne_two F hchar s
  rw [pow_succ 4 s]
  linarith

/-! #### 2b. Characteristic `2`: Involutory Block Shears and Nilpotent Cyclic Shifts -/

private lemma char_two_add_self {R : Type*} [Ring R] [CharP R 2] (x : R) : x + x = 0 := by
  have h2 : (2 : R) = 0 := by simpa using (CharP.cast_eq_zero R 2)
  calc x + x = (2 : R) * x := (two_mul x).symm
    _ = 0 := by rw [h2, zero_mul]

private lemma mat_char_two_add_self {n F : Type*} [Field F] [CharP F 2]
    (A : Matrix n n F) : A + A = 0 := by
  ext i j
  exact char_two_add_self (A i j)

private lemma mat_add_pow_two_pow_char_two {n F : Type*} [Fintype n] [DecidableEq n]
    [Field F] [CharP F 2] {A B : Matrix n n F} (hcomm : Commute A B) (k : ℕ) :
    (A + B) ^ (2 ^ k) = A ^ (2 ^ k) + B ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpow : (A + B) ^ (2 ^ (k + 1)) = ((A + B) ^ (2 ^ k)) * ((A + B) ^ (2 ^ k)) := by
      rw [pow_succ, pow_mul, sq]
    rw [hpow, ih]
    have hc : A ^ (2 ^ k) * B ^ (2 ^ k) = B ^ (2 ^ k) * A ^ (2 ^ k) := hcomm.pow_pow _ _
    calc (A ^ (2 ^ k) + B ^ (2 ^ k)) * (A ^ (2 ^ k) + B ^ (2 ^ k))
        = A ^ (2 ^ k) * A ^ (2 ^ k) +
            (A ^ (2 ^ k) * B ^ (2 ^ k) + B ^ (2 ^ k) * A ^ (2 ^ k)) +
            B ^ (2 ^ k) * B ^ (2 ^ k) := by
          rw [mul_add, add_mul, add_mul]; abel
      _ = A ^ (2 ^ (k + 1)) + B ^ (2 ^ (k + 1)) := by
          rw [← hc, mat_char_two_add_self, add_zero, ← pow_add, ← pow_add, ← two_mul,
            ← pow_succ']

/-- `2^t × 2^t` cyclic shift matrix `S_cyc[w, z] = 1[(w + 1) mod 2^t = z]`. -/
def S_cyc (R : Type*) [Zero R] [One R] (t : ℕ) : Matrix (Fin (2 ^ t)) (Fin (2 ^ t)) R :=
  fun w z => if (w.val + 1) % 2 ^ t = z.val then 1 else 0

private lemma S_cyc_pow_apply (R : Type*) [Semiring R] (t k : ℕ) (w z : Fin (2 ^ t)) :
    ((S_cyc R t) ^ k) w z = if (w.val + k) % 2 ^ t = z.val then 1 else 0 := by
  induction k generalizing z with
  | zero =>
    have hw : (w.val + 0) % 2 ^ t = w.val := by simp [Nat.mod_eq_of_lt w.isLt]
    rw [pow_zero, hw, Matrix.one_apply]
    by_cases hwz : w = z
    · subst hwz; simp
    · have hv : w.val ≠ z.val := fun h => hwz (Fin.ext h)
      simp [hwz, hv]
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    let u₀ : Fin (2 ^ t) := ⟨(w.val + k) % 2 ^ t, Nat.mod_lt _ (by positivity)⟩
    rw [Finset.sum_eq_single u₀]
    · rw [ih u₀]
      simp only [u₀, ↓reduceIte, S_cyc, one_mul]
      have hm : ((w.val + k) % 2 ^ t + 1) % 2 ^ t = (w.val + (k + 1)) % 2 ^ t := by
        rw [Nat.mod_add_mod, add_assoc]
      rw [hm]
    · intro u _ hu
      rw [ih u]
      have hv : (w.val + k) % 2 ^ t ≠ u.val := fun h => hu (Fin.ext h.symm)
      simp [hv]
    · intro hmem
      exact absurd (Finset.mem_univ u₀) hmem

private lemma S_cyc_pow_two_pow (R : Type*) [Semiring R] (t : ℕ) :
    (S_cyc R t) ^ (2 ^ t) = 1 := by
  ext w z
  rw [S_cyc_pow_apply, Nat.add_mod_right, Nat.mod_eq_of_lt w.isLt, Matrix.one_apply]
  by_cases hwz : w = z
  · subst hwz; simp
  · have hv : w.val ≠ z.val := fun h => hwz (Fin.ext h)
    simp [hwz, hv]

private lemma one_add_S_cyc_pow_two_pow {F : Type*} [Field F] [CharP F 2] (t : ℕ) :
    (1 + S_cyc F t) ^ (2 ^ t) = 0 := by
  rw [mat_add_pow_two_pow_char_two (Commute.one_left _) t, one_pow, S_cyc_pow_two_pow,
    mat_char_two_add_self]

private lemma one_add_S_cyc_pow_eq_zero_of_ge {F : Type*} [Field F] [CharP F 2] {t d : ℕ}
    (hd : 2 ^ t ≤ d) : (1 + S_cyc F t) ^ d = 0 := by
  have hsplit : d = 2 ^ t + (d - 2 ^ t) := by omega
  rw [hsplit, pow_add, one_add_S_cyc_pow_two_pow, zero_mul]

private lemma one_add_S_cyc_pow_row_zero_tri {F : Type*} [Field F] (t : ℕ) :
    ∀ (k : ℕ) (hk : k < 2 ^ t),
      (((1 + S_cyc F t) ^ k) ⟨0, by positivity⟩ ⟨k, hk⟩ = 1) ∧
      (∀ w : Fin (2 ^ t), k < w.val → ((1 + S_cyc F t) ^ k) ⟨0, by positivity⟩ w = 0) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨by simp, fun w hw => ?_⟩
    have hne : (⟨0, by positivity⟩ : Fin (2 ^ t)) ≠ w := fun h => by
      have hv : 0 = w.val := congrArg Fin.val h
      omega
    rw [pow_zero, Matrix.one_apply_ne hne]
  | succ k ih =>
    intro hk1
    obtain ⟨ih_diag, ih_zero⟩ := ih (by omega)
    have hstep : ∀ w : Fin (2 ^ t), 1 ≤ w.val →
        ((1 + S_cyc F t) ^ (k + 1)) ⟨0, by positivity⟩ w =
          ((1 + S_cyc F t) ^ k) ⟨0, by positivity⟩ w +
          ((1 + S_cyc F t) ^ k) ⟨0, by positivity⟩ ⟨w.val - 1, by omega⟩ := by
      intro w hw1
      rw [pow_succ, mul_add, mul_one, Matrix.add_apply, Matrix.mul_apply]
      congr 1
      let u₀ : Fin (2 ^ t) := ⟨w.val - 1, by omega⟩
      rw [Finset.sum_eq_single u₀]
      · have hm : (u₀.val + 1) % 2 ^ t = w.val := by
          dsimp only [u₀]
          rw [show w.val - 1 + 1 = w.val by omega, Nat.mod_eq_of_lt w.isLt]
        simp only [S_cyc, hm, ↓reduceIte, mul_one]
        rfl
      · intro u _ hu
        have hne : (u.val + 1) % 2 ^ t ≠ w.val := by
          intro hm
          apply hu
          apply Fin.ext
          dsimp only [u₀]
          by_cases hlt : u.val + 1 < 2 ^ t
          · rw [Nat.mod_eq_of_lt hlt] at hm; omega
          · have hu_max : u.val + 1 = 2 ^ t := by have := u.isLt; omega
            rw [hu_max, Nat.mod_self] at hm; omega
        simp [S_cyc, hne]
      · intro hmem
        exact absurd (Finset.mem_univ u₀) hmem
    refine ⟨?_, ?_⟩
    · rw [hstep ⟨k + 1, hk1⟩ (by dsimp; omega)]
      have h1 : ((1 + S_cyc F t) ^ k) ⟨0, by positivity⟩ ⟨k + 1, hk1⟩ = 0 :=
        ih_zero ⟨k + 1, hk1⟩ (by dsimp; omega)
      rw [h1, zero_add]
      congr 1
    · intro w hw
      rw [hstep w (by omega), ih_zero w (by omega),
        ih_zero ⟨w.val - 1, by omega⟩ (by dsimp; omega), add_zero]

private def V_pascal (F : Type*) [Field F] (t : ℕ) : Matrix (Fin (2 ^ t)) (Fin (2 ^ t)) F :=
  fun j w => ((1 + S_cyc F t) ^ j.val) ⟨0, by positivity⟩ w

private lemma det_V_pascal_eq_one (F : Type*) [Field F] (t : ℕ) :
    (V_pascal F t).det = 1 := by
  rw [← Matrix.det_transpose]
  have htri : (V_pascal F t)ᵀ.BlockTriangular id := by
    intro w j hlt
    change V_pascal F t j w = 0
    exact (one_add_S_cyc_pow_row_zero_tri t j.val j.isLt).2 w hlt
  rw [Matrix.det_of_isUpperTriangular htri]
  refine Finset.prod_eq_one fun j _ => ?_
  change ((1 + S_cyc F t) ^ j.val) ⟨0, by positivity⟩ j = 1
  exact (one_add_S_cyc_pow_row_zero_tri t j.val j.isLt).1

private def nilShift (F : Type*) [Zero F] [One F] (N d : ℕ) : Matrix (Fin N) (Fin N) F :=
  fun j k => if j.val + d = k.val then 1 else 0

private def rotEquiv (N : ℕ) (hN : 0 < N) (d : ℕ) : Fin N ≃ Fin N where
  toFun j := ⟨(j.val + d % N) % N, Nat.mod_lt _ hN⟩
  invFun k := ⟨(k.val + N - d % N) % N, Nat.mod_lt _ hN⟩
  left_inv j := by
    ext
    dsimp only
    have hd : d % N < N := Nat.mod_lt d hN
    have hj : j.val < N := j.isLt
    by_cases hlt : j.val + d % N < N
    · rw [Nat.mod_eq_of_lt hlt]
      have : j.val + d % N + N - d % N = j.val + N := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
    · have hm : (j.val + d % N) % N = j.val + d % N - N := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [hm]
      have : j.val + d % N - N + N - d % N = j.val := by omega
      rw [this, Nat.mod_eq_of_lt hj]
  right_inv k := by
    ext
    dsimp only
    have hd : d % N < N := Nat.mod_lt d hN
    have hk : k.val < N := k.isLt
    rw [Nat.mod_add_mod]
    have : k.val + N - d % N + d % N = k.val + N := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hk]

private lemma rank_nilShift {F : Type*} [Field F] {N : ℕ} (hN : 0 < N) (d : ℕ) :
    (nilShift F N d).rank = N - d := by
  classical
  let e := rotEquiv N hN d
  have hsub : (nilShift F N d).submatrix id e =
      Matrix.diagonal (fun j : Fin N => if j.val + d < N then (1 : F) else 0) := by
    ext j₁ j₂
    simp only [Matrix.submatrix_apply, id_eq, nilShift]
    have he_val : ∀ j : Fin N, (e j).val = (j.val + d) % N := by
      intro j
      change (j.val + d % N) % N = (j.val + d) % N
      rw [Nat.add_mod_mod]
    rw [he_val j₂]
    by_cases hj1 : j₁.val + d < N
    · by_cases h12 : j₁ = j₂
      · subst h12
        simp [hj1, Nat.mod_eq_of_lt hj1]
      · simp only [Matrix.diagonal_apply_ne _ h12]
        have hne : j₁.val + d ≠ (j₂.val + d) % N := by
          intro heq
          have heq' : (e j₁).val = (e j₂).val := by
            rw [he_val j₁, he_val j₂, Nat.mod_eq_of_lt hj1, heq]
          exact h12 (e.injective (Fin.ext heq'))
        simp [hne]
    · have hmod_lt : (j₂.val + d) % N < N := Nat.mod_lt _ hN
      have hne : j₁.val + d ≠ (j₂.val + d) % N := by omega
      by_cases h12 : j₁ = j₂
      · subst h12; simp [hj1, hne]
      · simp [Matrix.diagonal_apply_ne _ h12, hne]
  have hrk : (nilShift F N d).rank = ((nilShift F N d).submatrix id e).rank := by
    simpa [Matrix.reindex_apply] using (Matrix.rank_reindex (Equiv.refl (Fin N)) e.symm (nilShift F N d)).symm
  rw [hrk, hsub, Matrix.rank_diagonal]
  have hcard : Fintype.card { j : Fin N // (if j.val + d < N then (1 : F) else 0) ≠ 0 } =
      (Finset.univ.filter fun j : Fin N => j.val < N - d).card := by
    rw [Fintype.card_subtype]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hlt : j.val + d < N
    · simp [hlt, show j.val < N - d by omega]
    · simp [hlt, show ¬(j.val < N - d) by omega]
  rw [hcard]
  have hbij : (Finset.univ.filter fun j : Fin N => j.val < N - d).card =
      (Finset.range (N - d)).card := by
    refine Finset.card_bij
      (fun j _ => j.val)
      (fun j hj => Finset.mem_range.mpr (Finset.mem_filter.mp hj).2)
      (fun j₁ _ j₂ _ h => Fin.ext h)
      (fun m hm => ?_)
    have hmlt : m < N - d := Finset.mem_range.mp hm
    exact ⟨⟨m, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmlt⟩, rfl⟩
  rw [hbij, Finset.card_range]

private lemma rank_one_add_S_cyc_pow {F : Type*} [Field F] [CharP F 2] (t d : ℕ) :
    ((1 + S_cyc F t) ^ d).rank = 2 ^ t - d := by
  have hconj : V_pascal F t * ((1 + S_cyc F t) ^ d) =
      nilShift F (2 ^ t) d * V_pascal F t := by
    ext j w
    simp only [V_pascal, nilShift, Matrix.mul_apply]
    have hlhs : (∑ k : Fin (2 ^ t),
        ((1 + S_cyc F t) ^ j.val) ⟨0, by positivity⟩ k * ((1 + S_cyc F t) ^ d) k w) =
        ((1 + S_cyc F t) ^ (j.val + d)) ⟨0, by positivity⟩ w := by
      rw [pow_add]
      rfl
    rw [hlhs]
    by_cases hlt : j.val + d < 2 ^ t
    · let k₀ : Fin (2 ^ t) := ⟨j.val + d, hlt⟩
      rw [Finset.sum_eq_single k₀]
      · simp [k₀]
      · intro k _ hk
        have hv : j.val + d ≠ k.val := fun h => hk (Fin.ext h.symm)
        simp [hv]
      · intro hmem
        exact absurd (Finset.mem_univ k₀) hmem
    · rw [one_add_S_cyc_pow_eq_zero_of_ge (by omega : 2 ^ t ≤ j.val + d), Matrix.zero_apply]
      symm
      refine Finset.sum_eq_zero fun k _ => ?_
      have hv : j.val + d ≠ k.val := by have := k.isLt; omega
      simp [hv]
  have hunit : IsUnit (V_pascal F t).det := by
    rw [det_V_pascal_eq_one]; exact isUnit_one
  have hr1 : (V_pascal F t * ((1 + S_cyc F t) ^ d)).rank = ((1 + S_cyc F t) ^ d).rank :=
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hunit
  have hr2 : (nilShift F (2 ^ t) d * V_pascal F t).rank = (nilShift F (2 ^ t) d).rank :=
    Matrix.rank_mul_eq_left_of_isUnit_det _ _ hunit
  rw [← hr1, hconj, hr2, rank_nilShift (by positivity)]

private def xorShiftMul (F : Type*) [Field F] (t k : ℕ)
    (P : Matrix (Fin (2 ^ t)) (Fin (2 ^ t)) F) :
    Matrix (Fin (2 ^ k) × Fin (2 ^ t)) (Fin (2 ^ k) × Fin (2 ^ t)) F :=
  fun r c => (((S_cyc F t) ^ (r.1.val ^^^ c.1.val)) * P) r.2 c.2

private def splitPowTwoSumEquiv (k t : ℕ) :
    (Fin (2 ^ k) × Fin (2 ^ t)) ⊕ (Fin (2 ^ k) × Fin (2 ^ t)) ≃
      Fin (2 ^ (k + 1)) × Fin (2 ^ t) where
  toFun := Sum.elim
    (fun ⟨u, w⟩ => (⟨u.val, by have := u.isLt; rw [pow_succ]; omega⟩, w))
    (fun ⟨u, w⟩ => (⟨u.val + 2 ^ k, by have := u.isLt; rw [pow_succ]; omega⟩, w))
  invFun := fun ⟨u, w⟩ =>
    if hu : u.val < 2 ^ k then Sum.inl (⟨u.val, hu⟩, w)
    else Sum.inr (⟨u.val - 2 ^ k, by
      have hu_lt : u.val < 2 ^ (k + 1) := u.isLt
      have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
      omega⟩, w)
  left_inv := by
    rintro (⟨u, w⟩ | ⟨u, w⟩) <;> dsimp only
    · simp [u.isLt]
    · simp [show ¬(u.val + 2 ^ k < 2 ^ k) by omega]
  right_inv := by
    rintro ⟨u, w⟩
    dsimp only
    by_cases hu : u.val < 2 ^ k
    · simp [hu]
    · simp only [hu, ↓reduceDIte, Sum.elim_inr]
      exact Prod.ext (Fin.ext (by dsimp; omega)) rfl

private lemma xor_add_two_pow_same {k a b : ℕ} (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    (a + 2 ^ k) ^^^ (b + 2 ^ k) = a ^^^ b := by
  have hbit : ∀ x < 2 ^ k, ∀ i, (x + 2 ^ k).testBit i = (x.testBit i ^^ decide (i = k)) := by
    intro x hx i
    by_cases hik : i < k
    · have hdvd : 2 ^ (i + 1) ∣ 2 ^ k := Nat.pow_dvd_pow 2 hik
      obtain ⟨q, hq⟩ := hdvd
      have hpos : 0 < 2 ^ i := by positivity
      have heq : x + 2 ^ k = 2 ^ i * (2 * q) + x := by rw [hq, pow_succ]; ring
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, heq,
        Nat.mul_add_div hpos, Nat.mul_add_mod_self_left]
      simp [show i ≠ k by omega]
    · by_cases heq : i = k
      · subst heq
        have hpos : 0 < 2 ^ i := by positivity
        rw [Nat.testBit_lt_two_pow hx, Nat.testBit_eq_decide_div_mod_eq,
          Nat.add_div_right _ hpos, Nat.div_eq_of_lt hx, zero_add]
        simp
      · have hgt : k < i := by omega
        have hlt1 : x < 2 ^ i := lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hgt.le)
        have hlt2 : x + 2 ^ k < 2 ^ i := by
          calc x + 2 ^ k < 2 ^ k + 2 ^ k := by omega
            _ = 2 ^ (k + 1) := by ring
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) hgt
        rw [Nat.testBit_lt_two_pow hlt1, Nat.testBit_lt_two_pow hlt2]
        simp [heq]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_xor, hbit a ha i, hbit b hb i]
  cases a.testBit i <;> cases b.testBit i <;> cases decide (i = k) <;> rfl

private lemma xor_add_two_pow_right {k a b : ℕ} (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    a ^^^ (b + 2 ^ k) = (a ^^^ b) + 2 ^ k := by
  have hab : a ^^^ b < 2 ^ k := Nat.xor_lt_two_pow ha hb
  have h1 := xor_add_two_pow_same hab hb
  have hcancel : (a ^^^ b) ^^^ b = a := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_xor]
  -- (a ^^^ b + 2^k) ^^^ (b + 2^k) = a
  have h2 := congrArg (· ^^^ (b + 2 ^ k)) h1
  rw [hcancel] at h2
  have hcancel2 : (((a ^^^ b) + 2 ^ k) ^^^ (b + 2 ^ k)) ^^^ (b + 2 ^ k) = (a ^^^ b) + 2 ^ k := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_xor]
  rw [hcancel2] at h2
  exact h2.symm

private lemma rank_fromBlocks_diag {F α β : Type*} [Field F]
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (B : Matrix α α F) (C : Matrix β β F) :
    (Matrix.fromBlocks B 0 0 C).rank = B.rank + C.rank := by
  classical
  obtain ⟨VB, UB, eB, ⟨VB_u, rfl⟩, ⟨UB_u, rfl⟩, hEqB⟩ := Matrix.exists_rank_normal_form B
  obtain ⟨VC, UC, eC, ⟨VC_u, rfl⟩, ⟨UC_u, rfl⟩, hEqC⟩ := Matrix.exists_rank_normal_form C
  let L : Matrix (α ⊕ β) (α ⊕ β) F := Matrix.fromBlocks (VB_u : Matrix α α F) 0 0 (VC_u : Matrix β β F)
  let R : Matrix (α ⊕ β) (α ⊕ β) F := Matrix.fromBlocks (UB_u : Matrix α α F) 0 0 (UC_u : Matrix β β F)
  have hL_unit : IsUnit L.det := by
    refine isUnit_det_of_right_inv L
      (Matrix.fromBlocks (↑VB_u⁻¹ : Matrix α α F) 0 0 (↑VC_u⁻¹ : Matrix β β F)) ?_
    simp [L, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  have hR_unit : IsUnit R.det := by
    refine isUnit_det_of_right_inv R
      (Matrix.fromBlocks (↑UB_u⁻¹ : Matrix α α F) 0 0 (↑UC_u⁻¹ : Matrix β β F)) ?_
    simp [R, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  let dB : α → F := fun i => Sum.elim (fun _ => (1 : F)) (fun _ => (0 : F)) (eB i)
  let dC : β → F := fun j => Sum.elim (fun _ => (1 : F)) (fun _ => (0 : F)) (eC j)
  have hdiagB :
      (Matrix.fromBlocks (1 : Matrix (Fin B.rank) (Fin B.rank) F) 0 0
        (0 : Matrix (Fin (Fintype.card α - B.rank)) (Fin (Fintype.card α - B.rank)) F)).submatrix eB eB =
        Matrix.diagonal dB := by
    ext i j
    simp only [Matrix.submatrix_apply, dB]
    by_cases hij : i = j
    · subst hij; cases hc : eB i <;> simp [hc]
    · simp only [Matrix.diagonal_apply_ne _ hij]
      have hne : eB i ≠ eB j := fun h => hij (eB.injective h)
      cases hi : eB i <;> cases hj : eB j <;> simp_all
  have hdiagC :
      (Matrix.fromBlocks (1 : Matrix (Fin C.rank) (Fin C.rank) F) 0 0
        (0 : Matrix (Fin (Fintype.card β - C.rank)) (Fin (Fintype.card β - C.rank)) F)).submatrix eC eC =
        Matrix.diagonal dC := by
    ext i j
    simp only [Matrix.submatrix_apply, dC]
    by_cases hij : i = j
    · subst hij; cases hc : eC i <;> simp [hc]
    · simp only [Matrix.diagonal_apply_ne _ hij]
      have hne : eC i ≠ eC j := fun h => hij (eC.injective h)
      cases hi : eC i <;> cases hj : eC j <;> simp_all
  have hLMR : L * Matrix.fromBlocks B 0 0 C * R = Matrix.diagonal (Sum.elim dB dC) := by
    have hm : L * Matrix.fromBlocks B 0 0 C * R =
        Matrix.fromBlocks (Matrix.diagonal dB) 0 0 (Matrix.diagonal dC) := by
      dsimp only [L, R]
      rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
      simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
      rw [hEqB, hEqC, hdiagB, hdiagC]
    rw [hm]
    ext (i₁ | j₁) (i₂ | j₂) <;> simp [Matrix.diagonal_apply]
  have hrB : Fintype.card { i : α // dB i ≠ 0 } = B.rank := by
    have hVdet : IsUnit (VB_u : Matrix α α F).det := (Matrix.isUnit_iff_isUnit_det _).mp VB_u.isUnit
    have hUdet : IsUnit (UB_u : Matrix α α F).det := (Matrix.isUnit_iff_isUnit_det _).mp UB_u.isUnit
    have hr := Matrix.rank_diagonal dB
    rw [← hdiagB, ← hEqB, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hUdet,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hVdet] at hr
    exact hr.symm
  have hrC : Fintype.card { j : β // dC j ≠ 0 } = C.rank := by
    have hVdet : IsUnit (VC_u : Matrix β β F).det := (Matrix.isUnit_iff_isUnit_det _).mp VC_u.isUnit
    have hUdet : IsUnit (UC_u : Matrix β β F).det := (Matrix.isUnit_iff_isUnit_det _).mp UC_u.isUnit
    have hr := Matrix.rank_diagonal dC
    rw [← hdiagC, ← hEqC, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hUdet,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hVdet] at hr
    exact hr.symm
  rw [← Matrix.rank_mul_eq_right_of_isUnit_det L _ hL_unit,
    ← Matrix.rank_mul_eq_left_of_isUnit_det R _ hR_unit, hLMR, Matrix.rank_diagonal]
  have heq : { x : α ⊕ β // Sum.elim dB dC x ≠ 0 } ≃
      { i : α // dB i ≠ 0 } ⊕ { j : β // dC j ≠ 0 } :=
    { toFun := fun ⟨x, hx⟩ => match x with
        | Sum.inl i => Sum.inl ⟨i, hx⟩
        | Sum.inr j => Sum.inr ⟨j, hx⟩
      invFun := Sum.elim (fun ⟨i, hi⟩ => ⟨Sum.inl i, hi⟩) (fun ⟨j, hj⟩ => ⟨Sum.inr j, hj⟩)
      left_inv := fun ⟨x, _⟩ => by cases x <;> rfl
      right_inv := fun x => by cases x <;> rfl }
  rw [Fintype.card_congr heq, Fintype.card_sum, hrB, hrC]

private lemma rank_xorShiftMul {F : Type*} [Field F] [CharP F 2] (t k : ℕ) :
    ∀ (P : Matrix (Fin (2 ^ t)) (Fin (2 ^ t)) F), Commute P (S_cyc F t) →
      (xorShiftMul F t k P).rank =
        ∑ m ∈ Finset.range (2 ^ k), (((1 + S_cyc F t) ^ (2 * m)) * P).rank := by
  induction k with
  | zero =>
    intro P _
    let e0 : Fin (2 ^ 0) × Fin (2 ^ t) ≃ Fin (2 ^ t) :=
      { toFun := fun ⟨_, w⟩ => w
        invFun := fun w => (⟨0, by decide⟩, w)
        left_inv := fun ⟨u, w⟩ => Prod.ext (Fin.ext (by have := u.isLt; omega)) rfl
        right_inv := fun _ => rfl }
    have hre : (xorShiftMul F t 0 P).reindex e0 e0 = P := by
      ext w z
      simp [xorShiftMul, e0]
    rw [← Matrix.rank_reindex e0 e0, hre]
    simp
  | succ k ih =>
    intro P hcomm
    let B := xorShiftMul F t k P
    let A : Matrix (Fin (2 ^ k) × Fin (2 ^ t)) (Fin (2 ^ k) × Fin (2 ^ t)) F :=
      Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) F) ((S_cyc F t) ^ (2 ^ k))
    have hBA_eq : B * A = xorShiftMul F t k (((S_cyc F t) ^ (2 ^ k)) * P) := by
      ext ⟨u, w⟩ ⟨v, z⟩
      change (∑ p : Fin (2 ^ k) × Fin (2 ^ t), B (u, w) p * A p (v, z)) =
        (((S_cyc F t) ^ (u.val ^^^ v.val)) * (((S_cyc F t) ^ (2 ^ k)) * P)) w z
      rw [Fintype.sum_prod_type]
      have hinner : ∀ u' : Fin (2 ^ k),
          (∑ w' : Fin (2 ^ t), B (u, w) (u', w') * A (u', w') (v, z)) =
          if u' = v then
            (((S_cyc F t) ^ (u.val ^^^ v.val) * P) * ((S_cyc F t) ^ (2 ^ k))) w z
          else 0 := by
        intro u'
        by_cases huv : u' = v
        · subst huv
          simp only [↓reduceIte, B, A, xorShiftMul, Matrix.kroneckerMap_apply,
            Matrix.one_apply_eq, one_mul]
          rfl
        · simp [A, Matrix.kroneckerMap_apply, huv]
      simp_rw [hinner]
      rw [Finset.sum_eq_single v]
      · simp only [↓reduceIte]
        have hcomm_pow : P * (S_cyc F t) ^ (2 ^ k) = (S_cyc F t) ^ (2 ^ k) * P :=
          hcomm.pow_right (2 ^ k)
        have hmat : ((S_cyc F t) ^ (u.val ^^^ v.val) * P) * (S_cyc F t) ^ (2 ^ k) =
            (S_cyc F t) ^ (u.val ^^^ v.val) * ((S_cyc F t) ^ (2 ^ k) * P) := by
          rw [Matrix.mul_assoc, hcomm_pow]
        rw [hmat]
      · intro u' _ hu'
        simp [hu']
      · intro hmem
        exact absurd (Finset.mem_univ v) hmem
    have hAB_eq : A * B = B * A := by
      ext ⟨u, w⟩ ⟨v, z⟩
      rw [hBA_eq]
      change (∑ p : Fin (2 ^ k) × Fin (2 ^ t), A (u, w) p * B p (v, z)) =
        (((S_cyc F t) ^ (u.val ^^^ v.val)) * (((S_cyc F t) ^ (2 ^ k)) * P)) w z
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_eq_single u]
      · have hlhs : (∑ w' : Fin (2 ^ t), A (u, w) (u, w') * B (u, w') (v, z)) =
            (((S_cyc F t) ^ (2 ^ k)) * (((S_cyc F t) ^ (u.val ^^^ v.val)) * P)) w z := by
          simp only [A, B, xorShiftMul, Matrix.kroneckerMap_apply, Matrix.one_apply_eq, one_mul]
          rfl
        rw [hlhs]
        have hmat : (S_cyc F t) ^ (2 ^ k) * ((S_cyc F t) ^ (u.val ^^^ v.val) * P) =
            (S_cyc F t) ^ (u.val ^^^ v.val) * ((S_cyc F t) ^ (2 ^ k) * P) := by
          rw [← Matrix.mul_assoc, ← pow_add, add_comm (2 ^ k), pow_add, Matrix.mul_assoc]
        rw [hmat]
      · intro u' _ hu'
        simp [A, Matrix.kroneckerMap_apply, Ne.symm hu']
      · intro hmem
        exact absurd (Finset.mem_univ u) hmem
    have hblock :
        (xorShiftMul F t (k + 1) P).reindex (splitPowTwoSumEquiv k t).symm
            (splitPowTwoSumEquiv k t).symm =
          Matrix.fromBlocks B (B * A) (B * A) B := by
      ext r c
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
      rcases r with (⟨u, w⟩ | ⟨u, w⟩) <;> rcases c with (⟨v, z⟩ | ⟨v, z⟩)
      · simp only [Matrix.fromBlocks_apply₁₁, B]
        rfl
      · simp only [Matrix.fromBlocks_apply₁₂, hBA_eq]
        change (((S_cyc F t) ^ (u.val ^^^ (v.val + 2 ^ k))) * P) w z =
          (((S_cyc F t) ^ (u.val ^^^ v.val)) * (((S_cyc F t) ^ (2 ^ k)) * P)) w z
        rw [xor_add_two_pow_right u.isLt v.isLt, pow_add, Matrix.mul_assoc]
      · simp only [Matrix.fromBlocks_apply₂₁, hBA_eq]
        change (((S_cyc F t) ^ ((u.val + 2 ^ k) ^^^ v.val)) * P) w z =
          (((S_cyc F t) ^ (u.val ^^^ v.val)) * (((S_cyc F t) ^ (2 ^ k)) * P)) w z
        rw [Nat.xor_comm (u.val + 2 ^ k) v.val, xor_add_two_pow_right v.isLt u.isLt,
          Nat.xor_comm v.val u.val, pow_add, Matrix.mul_assoc]
      · simp only [Matrix.fromBlocks_apply₂₂, B]
        change (((S_cyc F t) ^ ((u.val + 2 ^ k) ^^^ (v.val + 2 ^ k))) * P) w z =
          (((S_cyc F t) ^ (u.val ^^^ v.val)) * P) w z
        rw [xor_add_two_pow_same u.isLt v.isLt]
    let I_kt : Matrix (Fin (2 ^ k) × Fin (2 ^ t)) (Fin (2 ^ k) × Fin (2 ^ t)) F := 1
    let L := Matrix.fromBlocks I_kt 0 A I_kt
    let R := Matrix.fromBlocks I_kt A 0 I_kt
    have hLL : L * L = 1 := by
      simp [L, I_kt, Matrix.fromBlocks_multiply, mat_char_two_add_self, Matrix.fromBlocks_one]
    have hRR : R * R = 1 := by
      simp [R, I_kt, Matrix.fromBlocks_multiply, mat_char_two_add_self, Matrix.fromBlocks_one]
    have hL_unit : IsUnit L.det := isUnit_det_of_right_inv L L hLL
    have hR_unit : IsUnit R.det := isUnit_det_of_right_inv R R hRR
    let P2 : Matrix (Fin (2 ^ t)) (Fin (2 ^ t)) F := ((1 + S_cyc F t) ^ (2 ^ (k + 1))) * P
    have hBRC : A * (B * A) + B = xorShiftMul F t k P2 := by
      have hABA : A * (B * A) = xorShiftMul F t k (((S_cyc F t) ^ (2 ^ (k + 1))) * P) := by
        ext ⟨u, w⟩ ⟨v, z⟩
        rw [hBA_eq]
        change (∑ p : Fin (2 ^ k) × Fin (2 ^ t), A (u, w) p *
            xorShiftMul F t k (((S_cyc F t) ^ (2 ^ k)) * P) p (v, z)) =
          (((S_cyc F t) ^ (u.val ^^^ v.val)) * (((S_cyc F t) ^ (2 ^ (k + 1))) * P)) w z
        rw [Fintype.sum_prod_type, Finset.sum_eq_single u]
        · have hlhs : (∑ w' : Fin (2 ^ t), A (u, w) (u, w') *
              xorShiftMul F t k (((S_cyc F t) ^ (2 ^ k)) * P) (u, w') (v, z)) =
              ((S_cyc F t) ^ (2 ^ k) *
                ((S_cyc F t) ^ (u.val ^^^ v.val) * ((S_cyc F t) ^ (2 ^ k) * P))) w z := by
            simp only [A, xorShiftMul, Matrix.kroneckerMap_apply, Matrix.one_apply_eq, one_mul]
            rfl
          rw [hlhs]
          have hmat : (S_cyc F t) ^ (2 ^ k) *
              ((S_cyc F t) ^ (u.val ^^^ v.val) * ((S_cyc F t) ^ (2 ^ k) * P)) =
              (S_cyc F t) ^ (u.val ^^^ v.val) * ((S_cyc F t) ^ (2 ^ (k + 1)) * P) := by
            rw [← Matrix.mul_assoc, ← pow_add, add_comm (2 ^ k), pow_add,
              Matrix.mul_assoc ((S_cyc F t) ^ (u.val ^^^ v.val)), ← Matrix.mul_assoc ((S_cyc F t) ^ (2 ^ k)),
              ← pow_add, ← two_mul, ← pow_succ']
          rw [hmat]
        · intro u' _ hu'; simp [A, Matrix.kroneckerMap_apply, Ne.symm hu']
        · intro hmem; exact absurd (Finset.mem_univ u) hmem
      rw [hABA]
      ext ⟨u, w⟩ ⟨v, z⟩
      simp only [Matrix.add_apply, B, xorShiftMul, P2]
      have h1S : (1 + S_cyc F t) ^ (2 ^ (k + 1)) = 1 + (S_cyc F t) ^ (2 ^ (k + 1)) := by
        rw [mat_add_pow_two_pow_char_two (Commute.one_left _) (k + 1), one_pow]
      rw [h1S]
      have hdist : (S_cyc F t) ^ (u.val ^^^ v.val) * ((1 + (S_cyc F t) ^ (2 ^ (k + 1))) * P) =
          (S_cyc F t) ^ (u.val ^^^ v.val) * ((S_cyc F t) ^ (2 ^ (k + 1)) * P) +
          (S_cyc F t) ^ (u.val ^^^ v.val) * P := by
        rw [add_mul, one_mul, mul_add, add_comm]
      rw [hdist, Matrix.add_apply]
    have hshear : L * Matrix.fromBlocks B (B * A) (B * A) B * R =
        Matrix.fromBlocks B 0 0 (xorShiftMul F t k P2) := by
      dsimp only [L, R, I_kt]
      simp only [Matrix.fromBlocks_multiply, one_mul, mul_one, zero_mul, mul_zero, add_zero,
        zero_add, hAB_eq, mat_char_two_add_self, hBRC]
    have hP2_comm : Commute P2 (S_cyc F t) :=
      ((Commute.one_left (S_cyc F t)).add_left (Commute.refl _)).pow_left _ |>.mul_left hcomm
    have hrk_step : (xorShiftMul F t (k + 1) P).rank =
        (xorShiftMul F t k P).rank + (xorShiftMul F t k P2).rank := by
      rw [← Matrix.rank_reindex (splitPowTwoSumEquiv k t).symm (splitPowTwoSumEquiv k t).symm,
        hblock, ← Matrix.rank_mul_eq_right_of_isUnit_det L _ hL_unit,
        ← Matrix.rank_mul_eq_left_of_isUnit_det R _ hR_unit, hshear, rank_fromBlocks_diag]
    rw [hrk_step, ih P hcomm, ih P2 hP2_comm]
    have h2pow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
    rw [h2pow, Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    dsimp only [P2]
    rw [← Matrix.mul_assoc, ← pow_add]
    congr 3
    rw [pow_succ]; ring

private lemma sum_two_mul_sub (N : ℕ) :
    ∑ m ∈ Finset.range N, (2 * N - 2 * m) = N * (N + 1) := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hsplit : ∑ m ∈ Finset.range (n + 1), (2 * (n + 1) - 2 * m) =
        2 * (n + 1) + ∑ m ∈ Finset.range n, (2 * (n + 1) - 2 * (m + 1)) := by
      rw [Finset.sum_range_succ', mul_zero, Nat.sub_zero, add_comm]
    rw [hsplit]
    have hcongr : ∑ m ∈ Finset.range n, (2 * (n + 1) - 2 * (m + 1)) =
        ∑ m ∈ Finset.range n, (2 * n - 2 * m) := by
      refine Finset.sum_congr rfl fun m _ => by omega
    rw [hcongr, ih]
    ring

/-- Exact characteristic-2 rank of `M_mat F (s + 1)` over EVERY field `F` with `[CharP F 2]`:
`rank_F(M_{s+1}) = 4^s + 2^s = 2^s * (2^s + 1)`. -/
theorem rank_M_mat_char_two (F : Type*) [Field F] [CharP F 2] (s : ℕ) :
    (M_mat F (s + 1)).rank = 4 ^ s + 2 ^ s := by
  have heq : M_mat F (s + 1) = xorShiftMul F (s + 1) (s + 1) 1 := by
    ext ⟨u, w⟩ ⟨v, z⟩
    simp only [M_mat, xorShiftMul, mul_one, S_cyc_pow_apply]
    have hiff : M_rel (s + 1) (u, w) (v, z) ↔ (w.val + (u.val ^^^ v.val)) % 2 ^ (s + 1) = z.val := by
      simp only [M_rel, add_comm (u.val ^^^ v.val) w.val]
    by_cases hm : M_rel (s + 1) (u, w) (v, z)
    · simp [hm, hiff.mp hm]
    · simp [hm, mt hiff.mpr hm]
  rw [heq, rank_xorShiftMul (s + 1) (s + 1) 1 (Commute.one_left _)]
  simp only [mul_one, rank_one_add_S_cyc_pow]
  have h2pow : 2 ^ (s + 1) = 2 ^ s + 2 ^ s := by rw [pow_succ]; ring
  rw [h2pow, Finset.sum_range_add]
  have htail : ∑ x ∈ Finset.range (2 ^ s), (2 ^ s + 2 ^ s - 2 * (2 ^ s + x)) = 0 :=
    Finset.sum_eq_zero fun x _ => by omega
  have hhead : ∑ m ∈ Finset.range (2 ^ s), (2 ^ s + 2 ^ s - 2 * m) =
      ∑ m ∈ Finset.range (2 ^ s), (2 * 2 ^ s - 2 * m) :=
    Finset.sum_congr rfl fun m _ => by omega
  rw [htail, add_zero, hhead, sum_two_mul_sub (2 ^ s)]
  have h4 : (4 : ℕ) ^ s = 2 ^ s * 2 ^ s := by
    calc (4 : ℕ) ^ s = (2 * 2) ^ s := by norm_num
      _ = 2 ^ s * 2 ^ s := mul_pow 2 2 s
  rw [h4]
  ring

/-- Exact characteristic-2 rank of `K_coreMat F s` over EVERY field `F` with `[CharP F 2]`:
`2 * rank_F(K_{s+1}) = 4^s + 2^s`. -/
theorem rank_K_coreMat_char_two (F : Type*) [Field F] [CharP F 2] (s : ℕ) :
    2 * (K_coreMat F s).rank = 4 ^ s + 2 ^ s := by
  rw [← rank_M_mat_eq_two_mul_rank_K_coreMat F s, rank_M_mat_char_two F s]

/-- Binomial-coefficient form `rank_F(K_{s+1}) = Nat.choose (2^s + 1) 2` in characteristic `2`. -/
theorem rank_K_coreMat_char_two_choose (F : Type*) [Field F] [CharP F 2] (s : ℕ) :
    (K_coreMat F s).rank = Nat.choose (2 ^ s + 1) 2 := by
  have h1 := rank_K_coreMat_char_two F s
  have h2 : 2 * Nat.choose (2 ^ s + 1) 2 = 4 ^ s + 2 ^ s := by
    rw [Nat.choose_two_right, Nat.add_sub_cancel]
    have heven : 2 ∣ (2 ^ s + 1) * 2 ^ s := by
      rcases s with _ | s'
      · decide
      · exact dvd_mul_of_dvd_right (dvd_pow_self 2 (by omega)) _
    rw [Nat.mul_div_cancel' heven]
    have h4 : (4 : ℕ) ^ s = 2 ^ s * 2 ^ s := by
      calc (4 : ℕ) ^ s = (2 * 2) ^ s := by norm_num
        _ = 2 ^ s * 2 ^ s := mul_pow 2 2 s
    rw [h4]
    ring
  omega

/-! ### Section 3: Real-Weighted Sum Lower Bound and Exact Attainment on `M_t` -/

/-- For every `t ≥ 1`, real weights `α, β : ℝ`, and cut `m : Fin t`, Mechanism `II-C*`
has exact real-weighted total load `(α * 2^(t - 1 - m) + β * 2^m) * 2^(2t)`. -/
theorem mechanismIICStar_weighted_sum_real {t : ℕ} (ht : 1 ≤ t) (α β : ℝ) (m : Fin t) :
    α * ((mechanismIICStar t m.val ht (by omega)).totalRowLoad : ℝ) +
      β * ((mechanismIICStar t m.val ht (by omega)).totalColLoad : ℝ) =
    (α * (2 : ℝ) ^ (t - 1 - m.val) + β * (2 : ℝ) ^ m.val) * (2 : ℝ) ^ (2 * t) := by
  rw [mechanismIICStar_totalRowLoad, mechanismIICStar_totalColLoad]
  push_cast
  ring

/-- Universal real-weighted attainment and optimality on `M_rel t`: for all `t ≥ 1` and all
positive real weights `α, β > 0`, there exists a cut `m : Fin t` such that `mechanismIICStar`
at cut `m` simultaneously equals `(α * 2^(t - 1 - m) + β * 2^m) * 2^(2t)` and lower-bounds
`α * C.totalRowLoad + β * C.totalColLoad` across EVERY exact biclique cover `C` of `M_rel t`. -/
theorem weighted_sum_M_attained_real {t : ℕ} (ht : 1 ≤ t) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∃ m : Fin t,
      α * ((mechanismIICStar t m.val ht (by omega)).totalRowLoad : ℝ) +
        β * ((mechanismIICStar t m.val ht (by omega)).totalColLoad : ℝ) =
          (α * (2 : ℝ) ^ (t - 1 - m.val) + β * (2 : ℝ) ^ m.val) * (2 : ℝ) ^ (2 * t) ∧
      ∀ C : ExactBicliqueCover (M_rel t),
        (α * (2 : ℝ) ^ (t - 1 - m.val) + β * (2 : ℝ) ^ m.val) * (2 : ℝ) ^ (2 * t) ≤
          α * (C.totalRowLoad : ℝ) + β * (C.totalColLoad : ℝ) := by
  cases t with
  | zero => omega
  | succ s =>
    let f : Fin (s + 1) → ℝ := fun m => α * (2 : ℝ) ^ (s - m.val) + β * (2 : ℝ) ^ m.val
    have hne : (Finset.univ : Finset (Fin (s + 1))).Nonempty := ⟨0, Finset.mem_univ _⟩
    obtain ⟨m₀, _, hm₀_min⟩ := Finset.exists_min_image Finset.univ f hne
    refine ⟨m₀, mechanismIICStar_weighted_sum_real ht α β m₀, ?_⟩
    intro C
    simp only [Nat.add_sub_cancel]
    change f m₀ * (2 : ℝ) ^ (2 * (s + 1)) ≤ α * (C.totalRowLoad : ℝ) + β * (C.totalColLoad : ℝ)
    have hf_nonneg : 0 ≤ f m₀ := by
      dsimp only [f]
      positivity
    have hterm : ∀ ℓ : C.L,
        f m₀ * (((C.U ℓ).card : ℝ) * ((C.V ℓ).card : ℝ)) ≤
          (2 : ℝ) ^ (s + 1) * (α * ((C.U ℓ).card : ℝ) + β * ((C.V ℓ).card : ℝ)) := by
      intro ℓ
      by_cases hU : (C.U ℓ).Nonempty
      · by_cases hV : (C.V ℓ).Nonempty
        · rcases M_rel_nonempty_biclique_dyadic_bound s hU hV (C.isBiclique ℓ) with
            ⟨m, hm, hUm, hVm⟩
          let mFin : Fin (s + 1) := ⟨m, by omega⟩
          have hmin : f m₀ ≤ α * (2 : ℝ) ^ (s - m) + β * (2 : ℝ) ^ m :=
            hm₀_min mFin (Finset.mem_univ _)
          have hVmul_nat : 2 ^ (s - m) * (C.V ℓ).card ≤ 2 ^ (s + 1) := by
            calc 2 ^ (s - m) * (C.V ℓ).card
                ≤ 2 ^ (s - m) * 2 ^ (m + 1) := Nat.mul_le_mul_left _ hVm
              _ = 2 ^ (s + 1) := by rw [← pow_add]; congr 1; omega
          have hUmul_nat : 2 ^ m * (C.U ℓ).card ≤ 2 ^ (s + 1) := by
            calc 2 ^ m * (C.U ℓ).card
                ≤ 2 ^ m * 2 ^ (s - m + 1) := Nat.mul_le_mul_left _ hUm
              _ = 2 ^ (s + 1) := by rw [← pow_add]; congr 1; omega
          have hVmul : (2 : ℝ) ^ (s - m) * ((C.V ℓ).card : ℝ) ≤ (2 : ℝ) ^ (s + 1) := by
            exact_mod_cast hVmul_nat
          have hUmul : (2 : ℝ) ^ m * ((C.U ℓ).card : ℝ) ≤ (2 : ℝ) ^ (s + 1) := by
            exact_mod_cast hUmul_nat
          have hU_nn : (0 : ℝ) ≤ ((C.U ℓ).card : ℝ) := Nat.cast_nonneg _
          have hV_nn : (0 : ℝ) ≤ ((C.V ℓ).card : ℝ) := Nat.cast_nonneg _
          have hUV_nn : (0 : ℝ) ≤ ((C.U ℓ).card : ℝ) * ((C.V ℓ).card : ℝ) :=
            mul_nonneg hU_nn hV_nn
          calc f m₀ * (((C.U ℓ).card : ℝ) * ((C.V ℓ).card : ℝ))
              ≤ (α * (2 : ℝ) ^ (s - m) + β * (2 : ℝ) ^ m) *
                  (((C.U ℓ).card : ℝ) * ((C.V ℓ).card : ℝ)) :=
                mul_le_mul_of_nonneg_right hmin hUV_nn
            _ = α * ((C.U ℓ).card : ℝ) * ((2 : ℝ) ^ (s - m) * ((C.V ℓ).card : ℝ)) +
                β * ((C.V ℓ).card : ℝ) * ((2 : ℝ) ^ m * ((C.U ℓ).card : ℝ)) := by ring
            _ ≤ α * ((C.U ℓ).card : ℝ) * (2 : ℝ) ^ (s + 1) +
                β * ((C.V ℓ).card : ℝ) * (2 : ℝ) ^ (s + 1) := by
              refine add_le_add ?_ ?_
              · exact mul_le_mul_of_nonneg_left hVmul (mul_nonneg hα.le hU_nn)
              · exact mul_le_mul_of_nonneg_left hUmul (mul_nonneg hβ.le hV_nn)
            _ = (2 : ℝ) ^ (s + 1) * (α * ((C.U ℓ).card : ℝ) + β * ((C.V ℓ).card : ℝ)) := by ring
        · rw [Finset.not_nonempty_iff_eq_empty] at hV
          simp only [hV, Finset.card_empty, Nat.cast_zero, mul_zero, add_zero]
          positivity
      · rw [Finset.not_nonempty_iff_eq_empty] at hU
        simp only [hU, Finset.card_empty, Nat.cast_zero, zero_mul, mul_zero, zero_add]
        positivity
    have hedges_nat : 2 ^ (3 * (s + 1)) ≤ ∑ ℓ : C.L, (C.U ℓ).card * (C.V ℓ).card := by
      rw [← M_rel_edge_card (s + 1)]
      exact exactBicliqueCover_edge_sum_ge C
    have hedges : (2 : ℝ) ^ (3 * (s + 1)) ≤
        ∑ ℓ : C.L, ((C.U ℓ).card : ℝ) * ((C.V ℓ).card : ℝ) := by
      exact_mod_cast hedges_nat
    have hpow_split : (2 : ℝ) ^ (3 * (s + 1)) =
        (2 : ℝ) ^ (2 * (s + 1)) * (2 : ℝ) ^ (s + 1) := by
      rw [← pow_add]; congr 1; omega
    have hsum : (2 : ℝ) ^ (s + 1) * (f m₀ * (2 : ℝ) ^ (2 * (s + 1))) ≤
        (2 : ℝ) ^ (s + 1) * (α * (C.totalRowLoad : ℝ) + β * (C.totalColLoad : ℝ)) := by
      calc (2 : ℝ) ^ (s + 1) * (f m₀ * (2 : ℝ) ^ (2 * (s + 1)))
          = f m₀ * (2 : ℝ) ^ (3 * (s + 1)) := by rw [hpow_split]; ring
        _ ≤ f m₀ * ∑ ℓ : C.L, ((C.U ℓ).card : ℝ) * ((C.V ℓ).card : ℝ) :=
            mul_le_mul_of_nonneg_left hedges hf_nonneg
        _ = ∑ ℓ : C.L, f m₀ * (((C.U ℓ).card : ℝ) * ((C.V ℓ).card : ℝ)) :=
            Finset.mul_sum _ _ _
        _ ≤ ∑ ℓ : C.L, (2 : ℝ) ^ (s + 1) *
              (α * ((C.U ℓ).card : ℝ) + β * ((C.V ℓ).card : ℝ)) :=
            Finset.sum_le_sum fun ℓ _ => hterm ℓ
        _ = (2 : ℝ) ^ (s + 1) * (α * (C.totalRowLoad : ℝ) + β * (C.totalColLoad : ℝ)) := by
            simp only [ExactBicliqueCover.totalRowLoad, ExactBicliqueCover.totalColLoad,
              Nat.cast_sum]
            rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (s + 1) := by positivity
    exact le_of_mul_le_mul_left hsum hpos

/-- Unconditional real-weighted sum lower bound across ALL exact covers of `M_rel t` (`t ≥ 1`)
for arbitrary positive real weights `α, β > 0`. -/
theorem weighted_sum_M_lower_real {t : ℕ} (ht : 1 ≤ t) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (C : ExactBicliqueCover (M_rel t)) :
    ∃ m : Fin t,
      (α * (2 : ℝ) ^ (t - 1 - m.val) + β * (2 : ℝ) ^ m.val) * (2 : ℝ) ^ (2 * t) ≤
        α * (C.totalRowLoad : ℝ) + β * (C.totalColLoad : ℝ) := by
  obtain ⟨m, _, hbound⟩ := weighted_sum_M_attained_real ht hα hβ
  exact ⟨m, hbound C⟩

/-! ### Section 4: Exact Equality Characterizations (`bc_M_eq_iff` & `prod_load_M_eq_iff`) -/

/-- An exact biclique cover `C` of a finite relation `R` is a zero-duplicate partition if and only if
the sum of rectangle areas `∑_ℓ |U_ℓ| * |V_ℓ|` equals `|E(R)|`. -/
theorem isPartition_iff_edge_sum_eq {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] {R : α → β → Prop} [∀ r c, Decidable (R r c)]
    (C : ExactBicliqueCover R) :
    C.IsPartition ↔
      ∑ ℓ : C.L, (C.U ℓ).card * (C.V ℓ).card =
        (Finset.univ.filter fun p : α × β => R p.1 p.2).card := by
  let E := Finset.univ.filter fun p : α × β => R p.1 p.2
  let mult : α × β → ℕ := fun p =>
    (Finset.univ.filter fun ℓ : C.L => p.1 ∈ C.U ℓ ∧ p.2 ∈ C.V ℓ).card
  have hmult_zero : ∀ p : α × β, ¬ R p.1 p.2 → mult p = 0 := by
    intro p hnot
    simp only [mult, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ,
      forall_true_left]
    rintro ℓ ⟨hr, hc⟩
    exact hnot (C.isBiclique ℓ p.1 hr p.2 hc)
  have hmult_ge : ∀ p ∈ E, 1 ≤ mult p := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rcases C.covers p.1 p.2 hp.2 with ⟨ℓ, hr, hc⟩
    exact Finset.card_pos.mpr ⟨ℓ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr, hc⟩⟩
  have hdouble : ∑ ℓ : C.L, (C.U ℓ).card * (C.V ℓ).card = ∑ p ∈ E, mult p := by
    have h1 : ∑ p : α × β, mult p = ∑ ℓ : C.L, (C.U ℓ).card * (C.V ℓ).card := by
      simp only [mult, Finset.card_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      rw [Fintype.sum_prod_type]
      have hV : ∀ r : α,
          (∑ c : β, if r ∈ C.U ℓ ∧ c ∈ C.V ℓ then 1 else 0) =
            if r ∈ C.U ℓ then (C.V ℓ).card else 0 := by
        intro r
        by_cases hr : r ∈ C.U ℓ
        · simp only [hr, true_and, ↓reduceIte, ← Finset.card_filter, Finset.filter_mem_eq_inter,
            Finset.univ_inter]
        · simp [hr]
      simp_rw [hV]
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const,
        smul_eq_mul]
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun p : α × β => R p.1 p.2) mult
    have h0 : ∑ p ∈ Finset.univ.filter (fun p : α × β => ¬ R p.1 p.2), mult p = 0 :=
      Finset.sum_eq_zero fun p hp => hmult_zero p (Finset.mem_filter.mp hp).2
    rw [h0, add_zero] at hsplit
    exact h1.symm.trans hsplit.symm
  have hE_ones : E.card = ∑ _p ∈ E, (1 : ℕ) := by simp
  rw [hdouble, hE_ones]
  have hsum_iff : (∑ p ∈ E, mult p = ∑ _p ∈ E, 1) ↔ ∀ p ∈ E, mult p = 1 := by
    constructor
    · intro heq
      have h := (Finset.sum_eq_sum_iff_of_le hmult_ge).mp heq.symm
      exact fun p hp => (h p hp).symm
    · intro hall
      exact Finset.sum_congr rfl hall
  rw [hsum_iff]
  constructor
  · intro hpart p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨ℓ, hℓ, huniq⟩ := hpart p.1 p.2 hp.2
    dsimp only [mult]
    rw [Finset.card_eq_one]
    refine ⟨ℓ, ?_⟩
    ext ℓ'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => huniq ℓ' h, fun h => h ▸ hℓ⟩
  · intro hall r c hR
    have hp : (r, c) ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hR⟩
    obtain ⟨ℓ, hℓ⟩ := Finset.card_eq_one.mp (hall (r, c) hp)
    refine ⟨ℓ, ?_, ?_⟩
    · have hm : ℓ ∈ Finset.univ.filter (fun ℓ' : C.L => r ∈ C.U ℓ' ∧ c ∈ C.V ℓ') := by
        rw [hℓ]; exact Finset.mem_singleton_self ℓ
      exact (Finset.mem_filter.mp hm).2
    · intro ℓ' hℓ'
      have hm : ℓ' ∈ ({ℓ} : Finset C.L) := by
        rw [← hℓ]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hℓ'⟩
      exact Finset.mem_singleton.mp hm

/-- Exact equality characterization for the biclique cover number `bc(M_t) = 2^(2t - 1)` (`t ≥ 1`):
an exact cover `C` of `M_rel t` has `|C.L| = 2^(2t - 1)` if and only if `C` is a zero-duplicate
partition of `M_rel t` and every rectangle `U_ℓ × V_ℓ` has maximum area `2^(t + 1)`. -/
theorem bc_M_eq_iff {t : ℕ} (ht : 1 ≤ t) (C : ExactBicliqueCover (M_rel t)) :
    Fintype.card C.L = 2 ^ (2 * t - 1) ↔
      C.IsPartition ∧ ∀ ℓ : C.L, (C.U ℓ).card * (C.V ℓ).card = 2 ^ (t + 1) := by
  cases t with
  | zero => omega
  | succ s =>
    have hpow : 2 ^ (2 * (s + 1) - 1) * 2 ^ (s + 2) = 2 ^ (3 * (s + 1)) := by
      rw [← pow_add]; congr 1; omega
    constructor
    · intro hcard
      have hedges : 2 ^ (3 * (s + 1)) ≤ ∑ ℓ : C.L, (C.U ℓ).card * (C.V ℓ).card := by
        rw [← M_rel_edge_card (s + 1)]
        exact exactBicliqueCover_edge_sum_ge C
      have hle : ∀ ℓ ∈ (Finset.univ : Finset C.L),
          (C.U ℓ).card * (C.V ℓ).card ≤ 2 ^ (s + 2) :=
        fun ℓ _ => M_rel_biclique_area_le s (C.isBiclique ℓ)
      have hsum_top : ∑ _ℓ : C.L, 2 ^ (s + 2) = 2 ^ (3 * (s + 1)) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, hcard, hpow]
      have hsum_le : ∑ ℓ : C.L, (C.U ℓ).card * (C.V ℓ).card ≤ 2 ^ (3 * (s + 1)) := by
        rw [← hsum_top]
        exact Finset.sum_le_sum hle
      have hsum_eq : ∑ ℓ : C.L, (C.U ℓ).card * (C.V ℓ).card = 2 ^ (3 * (s + 1)) :=
        le_antisymm hsum_le hedges
      have hpart : C.IsPartition := by
        rw [isPartition_iff_edge_sum_eq, M_rel_edge_card (s + 1)]
        exact hsum_eq
      have hall := (Finset.sum_eq_sum_iff_of_le hle).mp (hsum_eq.trans hsum_top.symm)
      exact ⟨hpart, fun ℓ => hall ℓ (Finset.mem_univ _)⟩
    · rintro ⟨hpart, harea⟩
      have hsum_eq : ∑ ℓ : C.L, (C.U ℓ).card * (C.V ℓ).card = 2 ^ (3 * (s + 1)) := by
        rw [← M_rel_edge_card (s + 1)]
        exact (isPartition_iff_edge_sum_eq C).mp hpart
      have hsum_const : ∑ ℓ : C.L, (C.U ℓ).card * (C.V ℓ).card =
          Fintype.card C.L * 2 ^ (s + 2) := by
        simp [harea]
      have hmul : Fintype.card C.L * 2 ^ (s + 2) = 2 ^ (2 * (s + 1) - 1) * 2 ^ (s + 2) := by
        rw [← hsum_const, hsum_eq, hpow]
      exact Nat.eq_of_mul_eq_mul_right (by positivity) hmul

private lemma partition_row_incident_sum {t : ℕ} (C : ExactBicliqueCover (M_rel t))
    (hpart : C.IsPartition) (r : Fin (2 ^ t) × Fin (2 ^ t)) :
    ∑ ℓ ∈ Finset.univ.filter (fun ℓ : C.L => r ∈ C.U ℓ), (C.V ℓ).card = 2 ^ t := by
  have h1 : (Finset.univ.filter fun c => M_rel t r c).card =
      ∑ c : Fin (2 ^ t) × Fin (2 ^ t),
        (Finset.univ.filter fun ℓ : C.L => r ∈ C.U ℓ ∧ c ∈ C.V ℓ).card := by
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hR : M_rel t r c
    · simp only [hR, ↓reduceIte]
      obtain ⟨ℓ, hℓ, huniq⟩ := hpart r c hR
      symm
      rw [Finset.card_eq_one]
      refine ⟨ℓ, ?_⟩
      ext ℓ'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => huniq ℓ' h, fun h => h ▸ hℓ⟩
    · simp only [hR, ↓reduceIte]
      symm
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro ℓ _ ⟨hr, hc⟩
      exact hR (C.isBiclique ℓ r hr c hc)
  rw [M_rel_row_card t r] at h1
  refine Eq.trans ?_ h1.symm
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun ℓ : C.L => r ∈ C.U ℓ)]
  have hzero : ∑ ℓ ∈ Finset.univ.filter (fun ℓ : C.L => ¬ r ∈ C.U ℓ),
      ∑ x : Fin (2 ^ t) × Fin (2 ^ t), (if r ∈ C.U ℓ ∧ x ∈ C.V ℓ then 1 else 0) = 0 := by
    refine Finset.sum_eq_zero fun ℓ hℓ => Finset.sum_eq_zero fun c _ => ?_
    have hnr := (Finset.mem_filter.mp hℓ).2
    simp [hnr]
  rw [hzero, add_zero]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  have hr := (Finset.mem_filter.mp hℓ).2
  simp [hr]

private lemma partition_col_incident_sum {t : ℕ} (C : ExactBicliqueCover (M_rel t))
    (hpart : C.IsPartition) (c : Fin (2 ^ t) × Fin (2 ^ t)) :
    ∑ ℓ ∈ Finset.univ.filter (fun ℓ : C.L => c ∈ C.V ℓ), (C.U ℓ).card = 2 ^ t := by
  have h1 : (Finset.univ.filter fun r => M_rel t r c).card =
      ∑ r : Fin (2 ^ t) × Fin (2 ^ t),
        (Finset.univ.filter fun ℓ : C.L => r ∈ C.U ℓ ∧ c ∈ C.V ℓ).card := by
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases hR : M_rel t r c
    · simp only [hR, ↓reduceIte]
      obtain ⟨ℓ, hℓ, huniq⟩ := hpart r c hR
      symm
      rw [Finset.card_eq_one]
      refine ⟨ℓ, ?_⟩
      ext ℓ'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => huniq ℓ' h, fun h => h ▸ hℓ⟩
    · simp only [hR, ↓reduceIte]
      symm
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro ℓ _ ⟨hr, hc⟩
      exact hR (C.isBiclique ℓ r hr c hc)
  rw [M_rel_col_card t c] at h1
  refine Eq.trans ?_ h1.symm
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun ℓ : C.L => c ∈ C.V ℓ)]
  have hzero : ∑ ℓ ∈ Finset.univ.filter (fun ℓ : C.L => ¬ c ∈ C.V ℓ),
      ∑ x : Fin (2 ^ t) × Fin (2 ^ t), (if x ∈ C.U ℓ ∧ c ∈ C.V ℓ then 1 else 0) = 0 := by
    refine Finset.sum_eq_zero fun ℓ hℓ => Finset.sum_eq_zero fun r _ => ?_
    have hnc := (Finset.mem_filter.mp hℓ).2
    simp [hnc]
  rw [hzero, add_zero]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  have hc := (Finset.mem_filter.mp hℓ).2
  simp [hc]

private lemma cauchy_schwarz_area_eq_uniform {ι : Type*} [Fintype ι]
    (u v : ι → ℕ) (A : ℕ) (hA_pos : 0 < A) (hA : ∀ i, u i * v i ≤ A)
    (i₀ : ι) (hui₀ : 0 < u i₀) (hvi₀ : 0 < v i₀)
    (heq : (∑ i : ι, u i * v i) ^ 2 = A * (∑ i : ι, u i) * (∑ i : ι, v i)) :
    u i₀ * v i₀ = A ∧ ∀ j : ι, (u j = 0 ∧ v j = 0) ∨ (u j = u i₀ ∧ v j = v i₀) := by
  have hpair_le : ∀ i j : ι, 2 * ((u i * v i) * (u j * v j)) ≤ A * (u i * v j + u j * v i) := by
    intro i j
    have hsq : (2 * ((u i * v i) * (u j * v j))) ^ 2 ≤ (A * (u i * v j + u j * v i)) ^ 2 := by
      have h1 : (u i * v i) * (u j * v j) ≤ A * A := Nat.mul_le_mul (hA i) (hA j)
      have h2 : 4 * (u i * v j * (u j * v i)) ≤ (u i * v j + u j * v i) ^ 2 := by
        zify; nlinarith [sq_nonneg ((u i : ℤ) * v j - (u j : ℤ) * v i)]
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
  have hlhs : ∑ p : ι × ι, 2 * ((u p.1 * v p.1) * (u p.2 * v p.2)) =
      2 * (∑ i : ι, u i * v i) ^ 2 := by
    rw [Fintype.sum_prod_type, sq, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  have hrhs : ∑ p : ι × ι, A * (u p.1 * v p.2 + u p.2 * v p.1) =
      2 * (A * (∑ i : ι, u i) * (∑ j : ι, v j)) := by
    rw [Fintype.sum_prod_type]
    have h1 : ∑ i : ι, ∑ j : ι, u i * v j = (∑ i : ι, u i) * (∑ j : ι, v j) := by
      rw [Finset.sum_mul]; simp_rw [Finset.mul_sum]
    have h2 : ∑ i : ι, ∑ j : ι, u j * v i = (∑ i : ι, u i) * (∑ j : ι, v j) := by
      rw [Finset.sum_comm, Finset.sum_mul]; simp_rw [Finset.mul_sum]
    calc ∑ i : ι, ∑ j : ι, A * (u i * v j + u j * v i)
        = A * ∑ i : ι, ∑ j : ι, (u i * v j + u j * v i) := by simp_rw [← Finset.mul_sum]
      _ = A * ((∑ i : ι, ∑ j : ι, u i * v j) + (∑ i : ι, ∑ j : ι, u j * v i)) := by
          simp_rw [Finset.sum_add_distrib]
      _ = A * ((∑ i : ι, u i) * (∑ j : ι, v j) + (∑ i : ι, u i) * (∑ j : ι, v j)) := by
          rw [h1, h2]
      _ = 2 * (A * (∑ i : ι, u i) * (∑ j : ι, v j)) := by ring
  have hsum_eq : ∑ p : ι × ι, 2 * ((u p.1 * v p.1) * (u p.2 * v p.2)) =
      ∑ p : ι × ι, A * (u p.1 * v p.2 + u p.2 * v p.1) := by
    rw [hlhs, hrhs, heq]
  have hpair_all := (Finset.sum_eq_sum_iff_of_le (fun p _ => hpair_le p.1 p.2)).mp hsum_eq
  have hpair : ∀ i j : ι, 2 * ((u i * v i) * (u j * v j)) = A * (u i * v j + u j * v i) :=
    fun i j => hpair_all (i, j) (Finset.mem_univ _)
  have harea0 : u i₀ * v i₀ = A := by
    have hself := hpair i₀ i₀
    have hpos0 : 0 < u i₀ * v i₀ := Nat.mul_pos hui₀ hvi₀
    nlinarith
  refine ⟨harea0, fun j => ?_⟩
  have hcross := hpair i₀ j
  rw [harea0] at hcross
  have hcross' : 2 * (u j * v j) = u i₀ * v j + u j * v i₀ := by nlinarith
  by_cases huj0 : u j = 0
  · left
    have hvj0 : v j = 0 := by nlinarith
    exact ⟨huj0, hvj0⟩
  · by_cases hvj0 : v j = 0
    · left
      have huj0' : u j = 0 := by nlinarith
      exact ⟨huj0', hvj0⟩
    · right
      have huj_pos : 0 < u j := Nat.pos_of_ne_zero huj0
      have hvj_pos : 0 < v j := Nat.pos_of_ne_zero hvj0
      have harea_j : u j * v j = A := by
        have hself := hpair j j
        have hpos_j : 0 < u j * v j := Nat.mul_pos huj_pos hvj_pos
        nlinarith
      have hsum_ij : u i₀ * v j + u j * v i₀ = 2 * A := by linarith
      have hprod_ij : (u i₀ * v j) * (u j * v i₀) = A * A := by
        calc (u i₀ * v j) * (u j * v i₀) = (u i₀ * v i₀) * (u j * v j) := by ring
          _ = A * A := by rw [harea0, harea_j]
      have hdiff_sq : ((u i₀ : ℤ) * (v j : ℤ) - (u j : ℤ) * (v i₀ : ℤ)) ^ 2 = 0 := by
        have hs_z : (u i₀ : ℤ) * (v j : ℤ) + (u j : ℤ) * (v i₀ : ℤ) = 2 * (A : ℤ) := by
          exact_mod_cast hsum_ij
        have hp_z : ((u i₀ : ℤ) * (v j : ℤ)) * ((u j : ℤ) * (v i₀ : ℤ)) =
            (A : ℤ) * (A : ℤ) := by
          exact_mod_cast hprod_ij
        nlinarith
      have heq_z : (u i₀ : ℤ) * (v j : ℤ) = (u j : ℤ) * (v i₀ : ℤ) := by
        have h0 := sq_eq_zero_iff.mp hdiff_sq
        linarith
      have heq_nat : u i₀ * v j = u j * v i₀ := by exact_mod_cast heq_z
      have hv_eq : v j = v i₀ := by
        have h1 : u i₀ * v j = u i₀ * v i₀ := by nlinarith
        exact Nat.eq_of_mul_eq_mul_left hui₀ h1
      have hu_eq : u j = u i₀ := by
        have h1 : u j * v i₀ = u i₀ * v i₀ := by
          calc u j * v i₀ = u j * v j := by rw [hv_eq]
            _ = A := harea_j
            _ = u i₀ * v i₀ := harea0.symm
        exact Nat.eq_of_mul_eq_mul_right hvi₀ h1
      exact ⟨hu_eq, hv_eq⟩

/-- Exact equality characterization for the degree-product lower bound
`C.totalRowLoad * C.totalColLoad = 2^(5t - 1)` (`t ≥ 1`):
equality holds if and only if `C` is a zero-duplicate partition of `M_rel t` and there exists
a cut `m : Fin t` such that every label `ℓ` is either `(∅, ∅)` or a maximal biclique of uniform
dyadic shape `(2^(t - m), 2^(m + 1))`, with constant vertex loads `rowLoad = 2^(t - 1 - m)`
and `colLoad = 2^m`. -/
theorem prod_load_M_eq_iff {t : ℕ} (ht : 1 ≤ t) (C : ExactBicliqueCover (M_rel t)) :
    C.totalRowLoad * C.totalColLoad = 2 ^ (5 * t - 1) ↔
      C.IsPartition ∧ ∃ m : Fin t,
        (∀ ℓ : C.L, (C.U ℓ = ∅ ∧ C.V ℓ = ∅) ∨
          ((C.U ℓ).card = 2 ^ (t - m.val) ∧ (C.V ℓ).card = 2 ^ (m.val + 1))) ∧
        (∀ r, C.rowLoad r = 2 ^ (t - 1 - m.val)) ∧
        (∀ c, C.colLoad c = 2 ^ m.val) := by
  cases t with
  | zero => omega
  | succ s =>
    constructor
    · intro hprod
      have hedges : 2 ^ (3 * (s + 1)) ≤ ∑ i : C.L, (C.U i).card * (C.V i).card := by
        rw [← M_rel_edge_card (s + 1)]
        exact exactBicliqueCover_edge_sum_ge C
      have hcs := cauchy_schwarz_area_bound (fun ℓ => (C.U ℓ).card) (fun ℓ => (C.V ℓ).card)
        (2 ^ (s + 2)) (fun ℓ => M_rel_biclique_area_le s (C.isBiclique ℓ))
      have htop_eq : 2 ^ (s + 2) * C.totalRowLoad * C.totalColLoad =
          (2 ^ (3 * (s + 1))) ^ 2 := by
        rw [mul_assoc, hprod, ← pow_add, ← pow_mul]
        congr 1; omega
      have hsq_eq : (∑ i : C.L, (C.U i).card * (C.V i).card) ^ 2 =
          (2 ^ (3 * (s + 1))) ^ 2 := by
        have hle1 : (2 ^ (3 * (s + 1))) ^ 2 ≤
            (∑ i : C.L, (C.U i).card * (C.V i).card) ^ 2 := Nat.pow_le_pow_left hedges 2
        have hle2 : (∑ i : C.L, (C.U i).card * (C.V i).card) ^ 2 ≤
            (2 ^ (3 * (s + 1))) ^ 2 := by
          rw [← htop_eq]; exact hcs
        exact le_antisymm hle2 hle1
      have hedges_eq : ∑ i : C.L, (C.U i).card * (C.V i).card = 2 ^ (3 * (s + 1)) := by
        by_contra hne
        have hlt : 2 ^ (3 * (s + 1)) < ∑ i : C.L, (C.U i).card * (C.V i).card := by omega
        have := Nat.pow_lt_pow_left hlt (by omega : 2 ≠ 0)
        omega
      have hpart : C.IsPartition := by
        rw [isPartition_iff_edge_sum_eq, M_rel_edge_card (s + 1)]
        exact hedges_eq
      let z0 : Fin (2 ^ (s + 1)) × Fin (2 ^ (s + 1)) := (⟨0, by positivity⟩, ⟨0, by positivity⟩)
      have hz0_edge : M_rel (s + 1) z0 z0 := by simp [M_rel, z0]
      obtain ⟨i₀, hi₀U, hi₀V⟩ := C.covers z0 z0 hz0_edge
      have hcs_eq : (∑ i : C.L, (C.U i).card * (C.V i).card) ^ 2 =
          2 ^ (s + 2) * (∑ i : C.L, (C.U i).card) * (∑ i : C.L, (C.V i).card) := by
        change _ = 2 ^ (s + 2) * C.totalRowLoad * C.totalColLoad
        rw [hsq_eq, htop_eq]
      obtain ⟨harea_i₀, hunif⟩ := cauchy_schwarz_area_eq_uniform
        (fun ℓ => (C.U ℓ).card) (fun ℓ => (C.V ℓ).card) (2 ^ (s + 2)) (by positivity)
        (fun ℓ => M_rel_biclique_area_le s (C.isBiclique ℓ)) i₀
        (Finset.card_pos.mpr ⟨z0, hi₀U⟩) (Finset.card_pos.mpr ⟨z0, hi₀V⟩) hcs_eq
      rcases M_rel_nonempty_biclique_dyadic_bound s ⟨z0, hi₀U⟩ ⟨z0, hi₀V⟩ (C.isBiclique i₀) with
        ⟨m₀, hm₀, hUm₀, hVm₀⟩
      have hdyad_prod : 2 ^ (s - m₀ + 1) * 2 ^ (m₀ + 1) = 2 ^ (s + 2) := by
        rw [← pow_add]; congr 1; omega
      have hui₀_eq : (C.U i₀).card = 2 ^ (s + 1 - m₀) := by
        have hsub : s + 1 - m₀ = s - m₀ + 1 := by omega
        rw [hsub]
        by_contra hne
        have hlt : (C.U i₀).card < 2 ^ (s - m₀ + 1) := by omega
        have hlt_prod : (C.U i₀).card * (C.V i₀).card < 2 ^ (s - m₀ + 1) * 2 ^ (m₀ + 1) := by
          calc (C.U i₀).card * (C.V i₀).card
              ≤ (C.U i₀).card * 2 ^ (m₀ + 1) := Nat.mul_le_mul_left _ hVm₀
            _ < 2 ^ (s - m₀ + 1) * 2 ^ (m₀ + 1) :=
                Nat.mul_lt_mul_of_pos_right hlt (by positivity)
        rw [harea_i₀, hdyad_prod] at hlt_prod
        exact lt_irrefl _ hlt_prod
      have hvi₀_eq : (C.V i₀).card = 2 ^ (m₀ + 1) := by
        have hsub : s + 1 - m₀ = s - m₀ + 1 := by omega
        have hmul : 2 ^ (s - m₀ + 1) * (C.V i₀).card = 2 ^ (s - m₀ + 1) * 2 ^ (m₀ + 1) := by
          calc 2 ^ (s - m₀ + 1) * (C.V i₀).card
              = (C.U i₀).card * (C.V i₀).card := by rw [hui₀_eq, hsub]
            _ = 2 ^ (s + 2) := harea_i₀
            _ = 2 ^ (s - m₀ + 1) * 2 ^ (m₀ + 1) := hdyad_prod.symm
        exact Nat.eq_of_mul_eq_mul_left (by positivity) hmul
      have hshape : ∀ j : C.L, (C.U j = ∅ ∧ C.V j = ∅) ∨
          ((C.U j).card = 2 ^ (s + 1 - m₀) ∧ (C.V j).card = 2 ^ (m₀ + 1)) := by
        intro j
        rcases hunif j with ⟨hU0, hV0⟩ | ⟨hUeq, hVeq⟩
        · exact Or.inl ⟨Finset.card_eq_zero.mp hU0, Finset.card_eq_zero.mp hV0⟩
        · exact Or.inr ⟨hUeq.trans hui₀_eq, hVeq.trans hvi₀_eq⟩
      refine ⟨hpart, ⟨m₀, by omega⟩, hshape, ?_, ?_⟩
      · intro r
        simp only [Nat.add_sub_cancel]
        have hinc := partition_row_incident_sum C hpart r
        have hconst : ∑ ℓ ∈ Finset.univ.filter (fun ℓ : C.L => r ∈ C.U ℓ), (C.V ℓ).card =
            C.rowLoad r * 2 ^ (m₀ + 1) := by
          unfold ExactBicliqueCover.rowLoad
          calc ∑ ℓ ∈ Finset.univ.filter (fun ℓ : C.L => r ∈ C.U ℓ), (C.V ℓ).card
              = ∑ _ℓ ∈ Finset.univ.filter (fun ℓ : C.L => r ∈ C.U ℓ), 2 ^ (m₀ + 1) := by
                refine Finset.sum_congr rfl fun ℓ hℓ => ?_
                have hrU : r ∈ C.U ℓ := (Finset.mem_filter.mp hℓ).2
                rcases hshape ℓ with ⟨hUe, _⟩ | ⟨_, hVc⟩
                · rw [hUe] at hrU; exact absurd hrU (Finset.notMem_empty r)
                · exact hVc
            _ = (Finset.univ.filter (fun ℓ : C.L => r ∈ C.U ℓ)).card * 2 ^ (m₀ + 1) := by simp
        have hpow_r : 2 ^ (s + 1) = 2 ^ (s - m₀) * 2 ^ (m₀ + 1) := by
          rw [← pow_add]; congr 1; omega
        have hmul_r : C.rowLoad r * 2 ^ (m₀ + 1) = 2 ^ (s - m₀) * 2 ^ (m₀ + 1) :=
          hconst.symm.trans (hinc.trans hpow_r)
        exact Nat.eq_of_mul_eq_mul_right (by positivity) hmul_r
      · intro c
        have hinc := partition_col_incident_sum C hpart c
        have hconst : ∑ ℓ ∈ Finset.univ.filter (fun ℓ : C.L => c ∈ C.V ℓ), (C.U ℓ).card =
            C.colLoad c * 2 ^ (s + 1 - m₀) := by
          unfold ExactBicliqueCover.colLoad
          calc ∑ ℓ ∈ Finset.univ.filter (fun ℓ : C.L => c ∈ C.V ℓ), (C.U ℓ).card
              = ∑ _ℓ ∈ Finset.univ.filter (fun ℓ : C.L => c ∈ C.V ℓ), 2 ^ (s + 1 - m₀) := by
                refine Finset.sum_congr rfl fun ℓ hℓ => ?_
                have hcV : c ∈ C.V ℓ := (Finset.mem_filter.mp hℓ).2
                rcases hshape ℓ with ⟨_, hVe⟩ | ⟨hUc, _⟩
                · rw [hVe] at hcV; exact absurd hcV (Finset.notMem_empty c)
                · exact hUc
            _ = (Finset.univ.filter (fun ℓ : C.L => c ∈ C.V ℓ)).card * 2 ^ (s + 1 - m₀) := by simp
        have hpow_c : 2 ^ (s + 1) = 2 ^ m₀ * 2 ^ (s + 1 - m₀) := by
          rw [← pow_add]; congr 1; omega
        have hmul_c : C.colLoad c * 2 ^ (s + 1 - m₀) = 2 ^ m₀ * 2 ^ (s + 1 - m₀) :=
          hconst.symm.trans (hinc.trans hpow_c)
        exact Nat.eq_of_mul_eq_mul_right (by positivity) hmul_c
    · rintro ⟨_, ⟨m, _, hrow, hcol⟩⟩
      have htotR : C.totalRowLoad = 2 ^ (2 * (s + 1)) * 2 ^ (s - m.val) := by
        rw [← ExactBicliqueCover.sum_rowLoad]
        simp only [Nat.add_sub_cancel] at hrow
        simp only [hrow, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          smul_eq_mul, ← pow_add]
        congr 1; omega
      have htotC : C.totalColLoad = 2 ^ (2 * (s + 1)) * 2 ^ m.val := by
        rw [← ExactBicliqueCover.sum_colLoad]
        simp only [hcol, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          smul_eq_mul, ← pow_add]
        congr 1; omega
      rw [htotR, htotC]
      have hm_le : m.val ≤ s := by omega
      calc 2 ^ (2 * (s + 1)) * 2 ^ (s - m.val) * (2 ^ (2 * (s + 1)) * 2 ^ m.val)
          = 2 ^ (2 * (s + 1)) * 2 ^ (2 * (s + 1)) * (2 ^ (s - m.val) * 2 ^ m.val) := by ring
        _ = 2 ^ (2 * (s + 1) + 2 * (s + 1)) * 2 ^ (s - m.val + m.val) := by
            rw [← pow_add, ← pow_add]
        _ = 2 ^ (5 * (s + 1) - 1) := by rw [← pow_add]; congr 1; omega

/-! ### Section 5: Abstract Balanced `4`-Star Blowup Lemma -/

/-- Explicit `4`-star blowup biclique partition constructed from a `(2d, 2d)`-regular base
partition `C₀`, a vertex-balanced `2`-coloring `f : C₀.L → ZMod 2`, and a local `(2, 2)`-biregular
`4`-fiber blowup indexed by `eΓ : Fin 4 ≃ Γ`. -/
def balancedStarBlowupCover {U₀ V₀ Γ : Type*} [Fintype U₀] [DecidableEq U₀]
    [Fintype V₀] [DecidableEq V₀] [Fintype Γ] [DecidableEq Γ]
    {R₀ : U₀ → V₀ → Prop} (C₀ : ExactBicliqueCover R₀)
    (f : C₀.L → ZMod 2) (eΓ : Fin 4 ≃ Γ)
    (H : Γ → Γ → Prop) [∀ a b, Decidable (H a b)]
    {R : U₀ × Γ → V₀ × Γ → Prop}
    (hR_base : ∀ u₀ ξ v₀ ζ, R (u₀, ξ) (v₀, ζ) → R₀ u₀ v₀)
    (φ : C₀.L → U₀ → (Γ ≃ Γ)) (ψ : C₀.L → V₀ → (Γ ≃ Γ))
    (hR_loc : ∀ ℓ : C₀.L, ∀ u₀ ∈ C₀.U ℓ, ∀ v₀ ∈ C₀.V ℓ, ∀ ξ ζ : Γ,
      R (u₀, ξ) (v₀, ζ) ↔ H (φ ℓ u₀ ξ) (ψ ℓ v₀ ζ)) :
    ExactBicliqueCover R where
  L := C₀.L × Fin 4
  U p := Finset.univ.filter fun u =>
    u.1 ∈ C₀.U p.1 ∧
      if f p.1 = 0 then φ p.1 u.1 u.2 = eΓ p.2 else H (φ p.1 u.1 u.2) (eΓ p.2)
  V p := Finset.univ.filter fun v =>
    v.1 ∈ C₀.V p.1 ∧
      if f p.1 = 0 then H (eΓ p.2) (ψ p.1 v.1 v.2) else ψ p.1 v.1 v.2 = eΓ p.2
  isBiclique := by
    rintro ⟨ℓ, k⟩ ⟨u₀, ξ⟩ hu ⟨v₀, ζ⟩ hv
    rw [Finset.mem_filter] at hu hv
    rcases hu.2 with ⟨hu₀, hlocU⟩
    rcases hv.2 with ⟨hv₀, hlocV⟩
    rw [hR_loc ℓ u₀ hu₀ v₀ hv₀ ξ ζ]
    by_cases hf0 : f ℓ = 0
    · simp only [hf0, ↓reduceIte] at hlocU hlocV
      rwa [hlocU]
    · simp only [hf0, ↓reduceIte] at hlocU hlocV
      rwa [hlocV]
  covers := by
    rintro ⟨u₀, ξ⟩ ⟨v₀, ζ⟩ hR
    obtain ⟨ℓ, hu₀, hv₀⟩ := C₀.covers u₀ v₀ (hR_base u₀ ξ v₀ ζ hR)
    have hH := (hR_loc ℓ u₀ hu₀ v₀ hv₀ ξ ζ).mp hR
    by_cases hf0 : f ℓ = 0
    · refine ⟨(ℓ, eΓ.symm (φ ℓ u₀ ξ)), ?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hu₀, by simp [hf0]⟩
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hv₀, by simpa [hf0] using hH⟩
    · refine ⟨(ℓ, eΓ.symm (ψ ℓ v₀ ζ)), ?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hu₀, by simpa [hf0] using hH⟩
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hv₀, by simp [hf0]⟩

/-- **Abstract Balanced `4`-Star Blowup Lemma** (Lemma 3.1 of Paper 2):
Given an exact biclique partition `C₀` of `R₀`, a vertex-balanced `2`-coloring `f : C₀.L → ZMod 2`
assigning `d` color-`0` and `d` color-`1` rectangles to every base vertex, and a local
`(2, 2)`-biregular `4`-fiber blowup `R` on `(U₀ × Γ) × (V₀ × Γ)` (`|Γ| = 4`), `R` admits an
explicit exact biclique partition into `4 * |C₀.L|` bicliques with uniform vertex load `3 * d`
at every row and every column. -/
theorem abstract_balanced_star_blowup {U₀ V₀ Γ : Type*} [Fintype U₀] [DecidableEq U₀]
    [Fintype V₀] [DecidableEq V₀] [Fintype Γ] [DecidableEq Γ]
    {R₀ : U₀ → V₀ → Prop} (C₀ : ExactBicliqueCover R₀) (hpart₀ : C₀.IsPartition)
    (d : ℕ) (f : C₀.L → ZMod 2)
    (hfU : ∀ u₀ : U₀,
      (Finset.univ.filter fun ℓ : C₀.L => u₀ ∈ C₀.U ℓ ∧ f ℓ = 0).card = d ∧
      (Finset.univ.filter fun ℓ : C₀.L => u₀ ∈ C₀.U ℓ ∧ f ℓ = 1).card = d)
    (hfV : ∀ v₀ : V₀,
      (Finset.univ.filter fun ℓ : C₀.L => v₀ ∈ C₀.V ℓ ∧ f ℓ = 0).card = d ∧
      (Finset.univ.filter fun ℓ : C₀.L => v₀ ∈ C₀.V ℓ ∧ f ℓ = 1).card = d)
    (hΓ : Fintype.card Γ = 4)
    (H : Γ → Γ → Prop) [∀ a b, Decidable (H a b)]
    (hH_row : ∀ a : Γ, (Finset.univ.filter fun b => H a b).card = 2)
    (hH_col : ∀ b : Γ, (Finset.univ.filter fun a => H a b).card = 2)
    {R : U₀ × Γ → V₀ × Γ → Prop}
    (hR_base : ∀ u₀ ξ v₀ ζ, R (u₀, ξ) (v₀, ζ) → R₀ u₀ v₀)
    (φ : C₀.L → U₀ → (Γ ≃ Γ)) (ψ : C₀.L → V₀ → (Γ ≃ Γ))
    (hR_loc : ∀ ℓ : C₀.L, ∀ u₀ ∈ C₀.U ℓ, ∀ v₀ ∈ C₀.V ℓ, ∀ ξ ζ : Γ,
      R (u₀, ξ) (v₀, ζ) ↔ H (φ ℓ u₀ ξ) (ψ ℓ v₀ ζ)) :
    ∃ C : ExactBicliqueCover R,
      C.IsPartition ∧
      Fintype.card C.L = 4 * Fintype.card C₀.L ∧
      (∀ u : U₀ × Γ, C.rowLoad u = 3 * d) ∧
      (∀ v : V₀ × Γ, C.colLoad v = 3 * d) := by
  let eΓ : Fin 4 ≃ Γ := (Fintype.equivFinOfCardEq hΓ).symm
  let C := balancedStarBlowupCover C₀ f eΓ H hR_base φ ψ hR_loc
  refine ⟨C, ?_, ?_, ?_, ?_⟩
  · rintro ⟨u₀, ξ⟩ ⟨v₀, ζ⟩ hR
    obtain ⟨ℓ₀, ⟨hu₀, hv₀⟩, huniq₀⟩ := hpart₀ u₀ v₀ (hR_base u₀ ξ v₀ ζ hR)
    obtain ⟨p₀, hpU, hpV⟩ := C.covers (u₀, ξ) (v₀, ζ) hR
    refine ⟨p₀, ⟨hpU, hpV⟩, ?_⟩
    intro p ⟨hU, hV⟩
    change (p : C₀.L × Fin 4) = (p₀ : C₀.L × Fin 4)
    rcases (p : C₀.L × Fin 4) with ⟨ℓ, k⟩
    rcases (p₀ : C₀.L × Fin 4) with ⟨ℓ_p, k_p⟩
    have hpU' := hpU
    have hpV' := hpV
    simp only [C, balancedStarBlowupCover, Finset.mem_filter, Finset.mem_univ, true_and]
      at hU hV hpU' hpV'
    have hℓ : ℓ = ℓ₀ := huniq₀ ℓ ⟨hU.1, hV.1⟩
    have hpℓ : ℓ_p = ℓ₀ := huniq₀ ℓ_p ⟨hpU'.1, hpV'.1⟩
    have hℓ_eq : ℓ_p = ℓ := hpℓ.trans hℓ.symm
    cases hℓ_eq
    by_cases hf0 : f ℓ = 0
    · simp only [hf0, ↓reduceIte] at hU hpU'
      have hk : eΓ k = eΓ k_p := hU.2.symm.trans hpU'.2
      exact Prod.ext rfl (eΓ.injective hk)
    · simp only [hf0, ↓reduceIte] at hV hpV'
      have hk : eΓ k = eΓ k_p := hV.2.symm.trans hpV'.2
      exact Prod.ext rfl (eΓ.injective hk)
  · change Fintype.card (C₀.L × Fin 4) = 4 * Fintype.card C₀.L
    rw [Fintype.card_prod, Fintype.card_fin, mul_comm]
  · rintro ⟨u₀, ξ⟩
    unfold ExactBicliqueCover.rowLoad
    rw [Finset.card_filter]
    change (∑ p : C₀.L × Fin 4, if (u₀, ξ) ∈ C.U p then 1 else 0) = 3 * d
    rw [Fintype.sum_prod_type]
    have hinner : ∀ ℓ : C₀.L,
        (∑ k : Fin 4, if (u₀, ξ) ∈ C.U (ℓ, k) then 1 else 0) =
          if u₀ ∈ C₀.U ℓ then (if f ℓ = 0 then 1 else 2) else 0 := by
      intro ℓ
      by_cases hu : u₀ ∈ C₀.U ℓ
      · simp only [hu, ↓reduceIte]
        by_cases hf0 : f ℓ = 0
        · simp only [hf0, ↓reduceIte]
          have h1 : (∑ k : Fin 4, if (u₀, ξ) ∈ C.U (ℓ, k) then 1 else 0) =
              (Finset.univ.filter fun k : Fin 4 => eΓ k = φ ℓ u₀ ξ).card := by
            rw [Finset.card_filter]
            refine Finset.sum_congr rfl fun k _ => ?_
            simp [C, balancedStarBlowupCover, hu, hf0, eq_comm]
          rw [h1, Finset.card_eq_one]
          refine ⟨eΓ.symm (φ ℓ u₀ ξ), ?_⟩
          ext k
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          exact ⟨fun h => eΓ.injective (by simpa using h), fun h => by subst h; simp⟩
        · simp only [hf0, ↓reduceIte]
          have h2 : (∑ k : Fin 4, if (u₀, ξ) ∈ C.U (ℓ, k) then 1 else 0) =
              (Finset.univ.filter fun k : Fin 4 => H (φ ℓ u₀ ξ) (eΓ k)).card := by
            rw [Finset.card_filter]
            refine Finset.sum_congr rfl fun k _ => ?_
            simp [C, balancedStarBlowupCover, hu, hf0]
          rw [h2]
          have hbij : (Finset.univ.filter fun k : Fin 4 => H (φ ℓ u₀ ξ) (eΓ k)).card =
              (Finset.univ.filter fun b : Γ => H (φ ℓ u₀ ξ) b).card := by
            refine Finset.card_bij (fun k _ => eΓ k)
              (fun k hk => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hk).2⟩)
              (fun _ _ _ _ h => eΓ.injective h)
              (fun b hb => ⟨eΓ.symm b,
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using (Finset.mem_filter.mp hb).2⟩,
                by simp⟩)
          rw [hbij, hH_row]
      · simp only [hu, ↓reduceIte]
        refine Finset.sum_eq_zero fun k _ => ?_
        simp [C, balancedStarBlowupCover, hu]
    simp_rw [hinner]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun ℓ : C₀.L => f ℓ = 0)]
    have hs0 : ∑ ℓ ∈ Finset.univ.filter (fun ℓ : C₀.L => f ℓ = 0),
        (if u₀ ∈ C₀.U ℓ then if f ℓ = 0 then 1 else 2 else 0) = d := by
      calc ∑ ℓ ∈ Finset.univ.filter (fun ℓ : C₀.L => f ℓ = 0),
            (if u₀ ∈ C₀.U ℓ then if f ℓ = 0 then 1 else 2 else 0)
          = ∑ ℓ ∈ Finset.univ.filter (fun ℓ : C₀.L => f ℓ = 0),
              (if u₀ ∈ C₀.U ℓ then 1 else 0) := by
            refine Finset.sum_congr rfl fun ℓ hℓ => ?_
            simp [(Finset.mem_filter.mp hℓ).2]
        _ = (Finset.univ.filter fun ℓ : C₀.L => u₀ ∈ C₀.U ℓ ∧ f ℓ = 0).card := by
            rw [Finset.card_filter, Finset.sum_filter]
            refine Finset.sum_congr rfl fun ℓ _ => by split_ifs <;> simp_all
        _ = d := (hfU u₀).1
    have hs1 : ∑ ℓ ∈ Finset.univ.filter (fun ℓ : C₀.L => ¬ f ℓ = 0),
        (if u₀ ∈ C₀.U ℓ then if f ℓ = 0 then 1 else 2 else 0) = 2 * d := by
      calc ∑ ℓ ∈ Finset.univ.filter (fun ℓ : C₀.L => ¬ f ℓ = 0),
            (if u₀ ∈ C₀.U ℓ then if f ℓ = 0 then 1 else 2 else 0)
          = ∑ ℓ ∈ Finset.univ.filter (fun ℓ : C₀.L => ¬ f ℓ = 0),
              2 * (if u₀ ∈ C₀.U ℓ then 1 else 0) := by
            refine Finset.sum_congr rfl fun ℓ hℓ => ?_
            have hnf := (Finset.mem_filter.mp hℓ).2
            split_ifs <;> simp_all
        _ = 2 * ∑ ℓ ∈ Finset.univ.filter (fun ℓ : C₀.L => ¬ f ℓ = 0),
              (if u₀ ∈ C₀.U ℓ then 1 else 0) := by rw [← Finset.mul_sum]
        _ = 2 * (Finset.univ.filter fun ℓ : C₀.L => u₀ ∈ C₀.U ℓ ∧ f ℓ = 1).card := by
            congr 1
            rw [Finset.card_filter, Finset.sum_filter]
            refine Finset.sum_congr rfl fun ℓ _ => ?_
            rcases zmod2_eq_zero_or_one (f ℓ) with h0 | h1
            · simp [h0]
            · simp [h1]
        _ = 2 * d := by rw [(hfU u₀).2]
    rw [hs0, hs1]; omega
  · rintro ⟨v₀, ζ⟩
    unfold ExactBicliqueCover.colLoad
    rw [Finset.card_filter]
    change (∑ p : C₀.L × Fin 4, if (v₀, ζ) ∈ C.V p then 1 else 0) = 3 * d
    rw [Fintype.sum_prod_type]
    have hinner : ∀ ℓ : C₀.L,
        (∑ k : Fin 4, if (v₀, ζ) ∈ C.V (ℓ, k) then 1 else 0) =
          if v₀ ∈ C₀.V ℓ then (if f ℓ = 0 then 2 else 1) else 0 := by
      intro ℓ
      by_cases hv : v₀ ∈ C₀.V ℓ
      · simp only [hv, ↓reduceIte]
        by_cases hf0 : f ℓ = 0
        · simp only [hf0, ↓reduceIte]
          have h2 : (∑ k : Fin 4, if (v₀, ζ) ∈ C.V (ℓ, k) then 1 else 0) =
              (Finset.univ.filter fun k : Fin 4 => H (eΓ k) (ψ ℓ v₀ ζ)).card := by
            rw [Finset.card_filter]
            refine Finset.sum_congr rfl fun k _ => ?_
            simp [C, balancedStarBlowupCover, hv, hf0]
          rw [h2]
          have hbij : (Finset.univ.filter fun k : Fin 4 => H (eΓ k) (ψ ℓ v₀ ζ)).card =
              (Finset.univ.filter fun a : Γ => H a (ψ ℓ v₀ ζ)).card := by
            refine Finset.card_bij (fun k _ => eΓ k)
              (fun k hk => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hk).2⟩)
              (fun _ _ _ _ h => eΓ.injective h)
              (fun a ha => ⟨eΓ.symm a,
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using (Finset.mem_filter.mp ha).2⟩,
                by simp⟩)
          rw [hbij, hH_col]
        · simp only [hf0, ↓reduceIte]
          have h1 : (∑ k : Fin 4, if (v₀, ζ) ∈ C.V (ℓ, k) then 1 else 0) =
              (Finset.univ.filter fun k : Fin 4 => eΓ k = ψ ℓ v₀ ζ).card := by
            rw [Finset.card_filter]
            refine Finset.sum_congr rfl fun k _ => ?_
            simp [C, balancedStarBlowupCover, hv, hf0, eq_comm]
          rw [h1, Finset.card_eq_one]
          refine ⟨eΓ.symm (ψ ℓ v₀ ζ), ?_⟩
          ext k
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          exact ⟨fun h => eΓ.injective (by simpa using h), fun h => by subst h; simp⟩
      · simp only [hv, ↓reduceIte]
        refine Finset.sum_eq_zero fun k _ => ?_
        simp [C, balancedStarBlowupCover, hv]
    simp_rw [hinner]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun ℓ : C₀.L => f ℓ = 0)]
    have hs0 : ∑ ℓ ∈ Finset.univ.filter (fun ℓ : C₀.L => f ℓ = 0),
        (if v₀ ∈ C₀.V ℓ then if f ℓ = 0 then 2 else 1 else 0) = 2 * d := by
      calc ∑ ℓ ∈ Finset.univ.filter (fun ℓ : C₀.L => f ℓ = 0),
            (if v₀ ∈ C₀.V ℓ then if f ℓ = 0 then 2 else 1 else 0)
          = 2 * ∑ ℓ ∈ Finset.univ.filter (fun ℓ : C₀.L => f ℓ = 0),
              (if v₀ ∈ C₀.V ℓ then 1 else 0) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun ℓ hℓ => ?_
            have hf := (Finset.mem_filter.mp hℓ).2
            split_ifs <;> simp_all
        _ = 2 * (Finset.univ.filter fun ℓ : C₀.L => v₀ ∈ C₀.V ℓ ∧ f ℓ = 0).card := by
            congr 1
            rw [Finset.card_filter, Finset.sum_filter]
            refine Finset.sum_congr rfl fun ℓ _ => by split_ifs <;> simp_all
        _ = 2 * d := by rw [(hfV v₀).1]
    have hs1 : ∑ ℓ ∈ Finset.univ.filter (fun ℓ : C₀.L => ¬ f ℓ = 0),
        (if v₀ ∈ C₀.V ℓ then if f ℓ = 0 then 2 else 1 else 0) = d := by
      calc ∑ ℓ ∈ Finset.univ.filter (fun ℓ : C₀.L => ¬ f ℓ = 0),
            (if v₀ ∈ C₀.V ℓ then if f ℓ = 0 then 2 else 1 else 0)
          = ∑ ℓ ∈ Finset.univ.filter (fun ℓ : C₀.L => ¬ f ℓ = 0),
              (if v₀ ∈ C₀.V ℓ then 1 else 0) := by
            refine Finset.sum_congr rfl fun ℓ hℓ => ?_
            have hnf := (Finset.mem_filter.mp hℓ).2
            split_ifs <;> simp_all
        _ = (Finset.univ.filter fun ℓ : C₀.L => v₀ ∈ C₀.V ℓ ∧ f ℓ = 1).card := by
            rw [Finset.card_filter, Finset.sum_filter]
            refine Finset.sum_congr rfl fun ℓ _ => ?_
            rcases zmod2_eq_zero_or_one (f ℓ) with h0 | h1
            · simp [h0]
            · simp [h1]
        _ = d := (hfV v₀).2
    rw [hs0, hs1]; omega

/-! ### Section 6: Embedded `DISJ_s`, Explicit `≤ 8s` Zero-Cover, and Margin Realization -/

private lemma mod_two_pow_succ_eq (x k : ℕ) :
    x % 2 ^ (k + 1) = x % 2 ^ k + 2 ^ k * (if x.testBit k then 1 else 0) := by
  have hdiv : (x % 2 ^ (k + 1)) / 2 ^ k = (x / 2 ^ k) % 2 := by
    rw [pow_succ', Nat.mod_mul_left_div_self]
  have hmod : (x % 2 ^ (k + 1)) % 2 ^ k = x % 2 ^ k :=
    Nat.mod_mod_of_dvd x (Nat.pow_dvd_pow 2 (by omega))
  have heq := (Nat.div_add_mod (x % 2 ^ (k + 1)) (2 ^ k)).symm
  rw [hdiv, hmod] at heq
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hm2 : (x / 2 ^ k) % 2 < 2 := Nat.mod_lt _ (by omega)
  rcases Nat.eq_zero_or_pos ((x / 2 ^ k) % 2) with h0 | hpos
  · rw [h0] at heq ⊢
    simp only [mul_zero, zero_add, zero_ne_one, decide_false, Bool.false_eq_true, ↓reduceIte,
      add_zero] at heq ⊢
    exact heq
  · have h1 : (x / 2 ^ k) % 2 = 1 := by omega
    rw [h1] at heq ⊢
    simp only [mul_one, decide_true, ↓reduceIte] at heq ⊢
    omega

private lemma prefix_mod_le_iff_testBit_imp (w z : ℕ) :
    ∀ k : ℕ, (∀ i < k, w % 2 ^ (i + 1) ≤ z % 2 ^ (i + 1)) ↔
      (∀ i < k, w.testBit i = true → z.testBit i = true) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    constructor
    · intro hall i hi hwi
      have hprev : ∀ j < k, w % 2 ^ (j + 1) ≤ z % 2 ^ (j + 1) :=
        fun j hj => hall j (by omega)
      by_cases hik : i < k
      · exact (ih.mp hprev) i hik hwi
      · have hieq : i = k := by omega
        subst hieq
        have hwk_le : w % 2 ^ i ≤ z % 2 ^ i := by
          rcases i with _ | k'
          · simp [Nat.mod_one]
          · exact hprev k' (by omega)
        have hz_lt : z % 2 ^ i < 2 ^ i := Nat.mod_lt _ (by positivity)
        have htop := hall i (by omega)
        rw [mod_two_pow_succ_eq w i, mod_two_pow_succ_eq z i, hwi] at htop
        by_contra hzi
        have hzf : z.testBit i = false := by revert hzi; cases z.testBit i <;> simp
        rw [hzf] at htop
        simp only [↓reduceIte, mul_one, Bool.false_eq_true, mul_zero, add_zero] at htop
        omega
    · intro himp i hi
      have hprev_imp : ∀ j < k, w.testBit j = true → z.testBit j = true :=
        fun j hj => himp j (by omega)
      have hprev_mod := ih.mpr hprev_imp
      by_cases hik : i < k
      · exact hprev_mod i hik
      · have hieq : i = k := by omega
        subst hieq
        have hwk_le : w % 2 ^ i ≤ z % 2 ^ i := by
          rcases i with _ | k'
          · simp [Nat.mod_one]
          · exact hprev_mod k' (by omega)
        rw [mod_two_pow_succ_eq w i, mod_two_pow_succ_eq z i]
        have hstep := himp i (by omega)
        cases hw : w.testBit i <;> cases hz : z.testBit i
        · simp only [Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero]; exact hwk_le
        · simp only [Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero, mul_one]; omega
        · exfalso; exact Bool.false_ne_true (hz ▸ hstep hw)
        · simp only [↓reduceIte, mul_one]; omega

private lemma testBit_compl_two_pow :
    ∀ {s x i : ℕ}, x < 2 ^ s → i < s → (2 ^ s - 1 - x).testBit i = !x.testBit i := by
  intro s
  induction s with
  | zero => intro _ _ _ hi; omega
  | succ s ih =>
    intro x i hx hi
    have hpow : 0 < 2 ^ s := by positivity
    have hx_lo : x % 2 ^ s < 2 ^ s := Nat.mod_lt _ hpow
    have hx_hi : x / 2 ^ s < 2 := by
      have : 2 ^ (s + 1) = 2 ^ s * 2 := by rw [pow_succ]
      exact Nat.div_lt_of_lt_mul (by linarith)
    have hx_eq : x = x % 2 ^ s + 2 ^ s * (x / 2 ^ s) := by
      have hd := (Nat.div_add_mod x (2 ^ s)).symm
      omega
    have hq_cases : x / 2 ^ s = 0 ∨ x / 2 ^ s = 1 := by
      rcases Nat.eq_zero_or_pos (x / 2 ^ s) with hq0 | hqpos
      · left; exact hq0
      · right; omega
    have hc_eq : 2 ^ (s + 1) - 1 - x =
        (2 ^ s - 1 - x % 2 ^ s) + 2 ^ s * (1 - x / 2 ^ s) := by
      have hp2 : 2 ^ (s + 1) = 2 ^ s + 2 ^ s := by rw [pow_succ]; ring
      rcases hq_cases with hq0 | hq1
      · rw [hq0] at hx_eq ⊢; omega
      · rw [hq1] at hx_eq ⊢; omega
    have hadd_tb : ∀ a q j : ℕ, a < 2 ^ s → q < 2 → j < s + 1 →
        (a + 2 ^ s * q).testBit j = if j < s then a.testBit j else decide (q = 1) := by
      intro a q j ha hq hj
      by_cases hjs : j < s
      · simp only [hjs, ↓reduceIte, Nat.testBit_eq_decide_div_mod_eq]
        have hdvd : 2 ^ (j + 1) ∣ 2 ^ s := Nat.pow_dvd_pow 2 hjs
        obtain ⟨m, hm⟩ := hdvd
        have hpos_j : 0 < 2 ^ j := by positivity
        have hrw : a + 2 ^ s * q = 2 ^ j * (2 * (m * q)) + a := by
          rw [hm, pow_succ]; ring
        rw [hrw, Nat.mul_add_div hpos_j, Nat.mul_add_mod_self_left]
      · have hjeq : j = s := by omega
        rw [hjeq]
        simp only [lt_irrefl, ↓reduceIte, Nat.testBit_eq_decide_div_mod_eq]
        have hrw : a + 2 ^ s * q = 2 ^ s * q + a := add_comm _ _
        rw [hrw, Nat.mul_add_div hpow, Nat.div_eq_of_lt ha, add_zero, Nat.mod_eq_of_lt hq]
    have hsub_q_lt : 1 - x / 2 ^ s < 2 := by omega
    rw [hc_eq, hadd_tb (2 ^ s - 1 - x % 2 ^ s) (1 - x / 2 ^ s) i (by omega) hsub_q_lt hi]
    conv_rhs => rw [hx_eq, hadd_tb (x % 2 ^ s) (x / 2 ^ s) i hx_lo hx_hi hi]
    by_cases his : i < s
    · simp only [his, ↓reduceIte]
      exact ih hx_lo his
    · simp only [his, ↓reduceIte]
      rcases hq_cases with hq0 | hq1
      · simp [hq0]
      · simp [hq1]

/-- Restricting `K_coreRel s` to `x' = y' = 0` and complementing `z' ↦ 2^s - 1 - z'`
embeds the `2^s × 2^s` Set Disjointness matrix `DISJ_s` verbatim (Eq. `eq:disj-embed`). -/
theorem disj_embedded_in_K_coreRel (s : ℕ) (w z : Fin (2 ^ s)) :
    K_coreRel s (0, w) (0, ⟨2 ^ s - 1 - z.val, by have := z.isLt; omega⟩) ↔
      ∀ i < s, ¬ (w.val.testBit i = true ∧ z.val.testBit i = true) := by
  have hzero : K_coreRel s (0, w) (0, ⟨2 ^ s - 1 - z.val, by have := z.isLt; omega⟩) ↔
      ∀ i < s, w.val % 2 ^ (i + 1) ≤ (2 ^ s - 1 - z.val) % 2 ^ (i + 1) := by
    unfold K_coreRel borrowVec borrowBit
    constructor
    · intro h i hi
      have hi_eq := congrFun h ⟨i, hi⟩
      simp only [Pi.add_apply, Pi.zero_apply, add_zero] at hi_eq
      by_contra hgt
      push Not at hgt
      simp only [hgt, ↓reduceIte] at hi_eq
      exact zero_ne_one hi_eq
    · intro hall
      funext i
      simp only [Pi.add_apply, Pi.zero_apply, add_zero]
      have hle := hall i.val i.isLt
      have hnot : ¬ ((2 ^ s - 1 - z.val) % 2 ^ (i.val + 1) < w.val % 2 ^ (i.val + 1)) := by omega
      simp [hnot]
  rw [hzero, prefix_mod_le_iff_testBit_imp]
  constructor
  · intro himp i hi ⟨hw, hz⟩
    have hc := himp i hi hw
    rw [testBit_compl_two_pow z.isLt hi, hz] at hc
    exact Bool.false_ne_true hc
  · intro hdisj i hi hw
    have hc := testBit_compl_two_pow z.isLt hi
    rw [hc]
    cases hz : z.val.testBit i
    · rfl
    · exfalso; exact hdisj i hi ⟨hw, hz⟩

/-- Induced `2^s × 2^s` Boolean-cube Set Disjointness embedding in `K_coreRel s`. -/
theorem disj_bool_embedded_in_K_coreRel (s : ℕ) :
    ∃ (fRow fCol : (Fin s → Bool) → (Fin s → ZMod 2) × Fin (2 ^ s)),
      Function.Injective fRow ∧ Function.Injective fCol ∧
      ∀ a b : Fin s → Bool,
        K_coreRel s (fRow a) (fCol b) ↔ ∀ i : Fin s, ¬ (a i = true ∧ b i = true) := by
  let toFin : (Fin s → Bool) → Fin (2 ^ s) := fun a =>
    ⟨vecToNat (fun i => if a i then (1 : ZMod 2) else 0), vecToNat_lt _⟩
  have htoFin_tb : ∀ (a : Fin s → Bool) (i : Fin s), (toFin a).val.testBit i.val = a i := by
    intro a i
    dsimp only [toFin]
    rw [testBit_vecToNat]
    cases a i <;> decide
  have htoFin_inj : Function.Injective toFin := by
    intro a₁ a₂ h
    funext i
    rw [← htoFin_tb a₁ i, ← htoFin_tb a₂ i, h]
  refine ⟨fun a => (0, toFin a),
    fun b => (0, ⟨2 ^ s - 1 - (toFin b).val, by have := (toFin b).isLt; omega⟩),
    fun a₁ a₂ h => htoFin_inj (congrArg Prod.snd h),
    fun b₁ b₂ h => ?_,
    fun a b => ?_⟩
  · have hval : 2 ^ s - 1 - (toFin b₁).val = 2 ^ s - 1 - (toFin b₂).val :=
      congrArg (fun p => p.2.val) h
    have h1 := (toFin b₁).isLt
    have h2 := (toFin b₂).isLt
    exact htoFin_inj (Fin.ext (by omega))
  · rw [disj_embedded_in_K_coreRel s (toFin a) (toFin b)]
    constructor
    · intro hall i
      simpa [htoFin_tb a i, htoFin_tb b i] using hall i.val i.isLt
    · intro hall i hi
      simpa [htoFin_tb a ⟨i, hi⟩, htoFin_tb b ⟨i, hi⟩] using hall ⟨i, hi⟩

/-- Local carry-transition step polynomial over `ZMod 2`:
`nextBorrow wb zb cb = wb * (1 + zb) + (1 + wb + zb) * cb`. -/
def nextBorrow (wb zb cb : ZMod 2) : ZMod 2 :=
  wb * (1 + zb) + (1 + wb + zb) * cb

private lemma natBit_eq_ite_testBit (x j : ℕ) :
    natBit x j = if x.testBit j then 1 else 0 := by
  unfold natBit
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hdiv := (Nat.div_add_mod (x / 2 ^ j) 2).symm
  have hm : (x / 2 ^ j) % 2 < 2 := Nat.mod_lt _ (by omega)
  have hcast : ((x / 2 ^ j : ℕ) : ZMod 2) = (((x / 2 ^ j) % 2 : ℕ) : ZMod 2) := by
    conv_lhs => rw [hdiv]
    push_cast
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [h2, zero_mul, zero_add]
  rw [hcast]
  rcases Nat.eq_zero_or_pos ((x / 2 ^ j) % 2) with h0 | hpos
  · simp [h0]
  · have h1 : (x / 2 ^ j) % 2 = 1 := by omega
    simp [h1]

private lemma borrowBit_succ_eq_nextBorrow (j w z : ℕ) :
    borrowBit (j + 1) w z = nextBorrow (natBit w j) (natBit z j) (borrowBit j w z) := by
  rw [natBit_eq_ite_testBit, natBit_eq_ite_testBit]
  unfold borrowBit nextBorrow
  rw [mod_two_pow_succ_eq w j, mod_two_pow_succ_eq z j]
  have hw_lt : w % 2 ^ j < 2 ^ j := Nat.mod_lt _ (by positivity)
  have hz_lt : z % 2 ^ j < 2 ^ j := Nat.mod_lt _ (by positivity)
  by_cases hlt : z % 2 ^ j < w % 2 ^ j
  · cases hw : w.testBit j <;> cases hz : z.testBit j
    · simp only [Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero, hlt]
      decide
    · have hnot : ¬ (z % 2 ^ j + 2 ^ j * 1 < w % 2 ^ j + 2 ^ j * 0) := by omega
      simp only [Bool.false_eq_true, ↓reduceIte, hlt, hnot]
      decide
    · have hyes : z % 2 ^ j + 2 ^ j * 0 < w % 2 ^ j + 2 ^ j * 1 := by omega
      simp only [Bool.false_eq_true, ↓reduceIte, hlt, hyes]
      decide
    · have hyes : z % 2 ^ j + 2 ^ j * 1 < w % 2 ^ j + 2 ^ j * 1 := by omega
      simp only [↓reduceIte, hlt, hyes]
      decide
  · cases hw : w.testBit j <;> cases hz : z.testBit j
    · simp only [Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero, hlt]
      decide
    · have hnot : ¬ (z % 2 ^ j + 2 ^ j * 1 < w % 2 ^ j + 2 ^ j * 0) := by omega
      simp only [Bool.false_eq_true, ↓reduceIte, hlt, hnot]
      decide
    · have hyes : z % 2 ^ j + 2 ^ j * 0 < w % 2 ^ j + 2 ^ j * 1 := by omega
      simp only [Bool.false_eq_true, ↓reduceIte, hlt, hyes]
      decide
    · have hnot : ¬ (z % 2 ^ j + 2 ^ j * 1 < w % 2 ^ j + 2 ^ j * 1) := by omega
      simp only [↓reduceIte, hlt, hnot]
      decide

private lemma K_coreRel_iff_local_transitions (s : ℕ)
    (r c : (Fin s → ZMod 2) × Fin (2 ^ s)) :
    K_coreRel s r c ↔
      ∀ j : Fin s, r.1 j + c.1 j =
        nextBorrow (natBit r.2.val j.val) (natBit c.2.val j.val)
          (if _hj : j.val = 0 then 0 else r.1 ⟨j.val - 1, by omega⟩ + c.1 ⟨j.val - 1, by omega⟩) := by
  constructor
  · intro hK j
    have hj_eq : r.1 j + c.1 j = borrowBit (j.val + 1) r.2.val c.2.val := by
      simpa [K_coreRel, borrowVec] using congrFun hK j
    rw [hj_eq, borrowBit_succ_eq_nextBorrow]
    by_cases hj0 : j.val = 0
    · simp [hj0, borrowBit, Nat.mod_one]
    · simp only [hj0, ↓reduceDIte]
      have hprev : r.1 ⟨j.val - 1, by omega⟩ + c.1 ⟨j.val - 1, by omega⟩ =
          borrowBit j.val r.2.val c.2.val := by
        have hp := congrFun hK ⟨j.val - 1, by omega⟩
        simp only [Pi.add_apply, borrowVec] at hp
        rw [show j.val - 1 + 1 = j.val by omega] at hp
        exact hp
      rw [hprev]
  · intro hall
    have hind : ∀ k : ℕ, (hk : k < s) →
        r.1 ⟨k, hk⟩ + c.1 ⟨k, hk⟩ = borrowBit (k + 1) r.2.val c.2.val := by
      intro k
      induction k with
      | zero =>
        intro hk
        have h0 := hall ⟨0, hk⟩
        simp only [↓reduceDIte] at h0
        rw [h0, borrowBit_succ_eq_nextBorrow]
        simp [borrowBit, Nat.mod_one]
      | succ k ih =>
        intro hk
        have hk1 := hall ⟨k + 1, hk⟩
        simp only [Nat.succ_ne_zero, ↓reduceDIte, Nat.add_sub_cancel] at hk1
        rw [hk1, ih (by omega), ← borrowBit_succ_eq_nextBorrow]
    funext j
    exact hind j.val j.isLt

/-- Index type of the explicit all-zeros rectangle cover of `K_coreRel s`:
`0` rectangles at `s = 0` (`K_1 = (1)` has no zero entries) and `4 + 8 * (s - 1) = 8 * s - 4`
rectangles for `s ≥ 1`. -/
def ZeroCoverIdx : ℕ → Type
  | 0 => PEmpty
  | m + 1 => (ZMod 2 × ZMod 2) ⊕ (Fin m × ZMod 2 × ZMod 2 × ZMod 2)

instance instFintypeZeroCoverIdx : ∀ s, Fintype (ZeroCoverIdx s)
  | 0 => inferInstanceAs (Fintype PEmpty)
  | m + 1 => inferInstanceAs (Fintype ((ZMod 2 × ZMod 2) ⊕ (Fin m × ZMod 2 × ZMod 2 × ZMod 2)))

instance instDecidableEqZeroCoverIdx : ∀ s, DecidableEq (ZeroCoverIdx s)
  | 0 => inferInstanceAs (DecidableEq PEmpty)
  | m + 1 =>
      inferInstanceAs (DecidableEq ((ZMod 2 × ZMod 2) ⊕ (Fin m × ZMod 2 × ZMod 2 × ZMod 2)))

/-- Explicit exact biclique cover of the zero entries `¬ K_coreRel s r c` by `M_0(s) ≤ 8 * s`
all-zeros rectangles (`0` at `s = 0`, `8 * s - 4` for `s ≥ 1`). -/
def zeroCoverKCore : (s : ℕ) →
    ExactBicliqueCover (fun r c : (Fin s → ZMod 2) × Fin (2 ^ s) => ¬ K_coreRel s r c)
  | 0 =>
    { L := ZeroCoverIdx 0
      U := fun q => PEmpty.elim q
      V := fun q => PEmpty.elim q
      isBiclique := fun q => PEmpty.elim q
      covers := fun r c hnot => by
        exfalso
        apply hnot
        funext i
        exact Fin.elim0 i }
  | m + 1 =>
    { L := ZeroCoverIdx (m + 1)
      U := Sum.elim
        (fun ⟨xr, wr⟩ => Finset.univ.filter fun r =>
          r.1 0 = xr ∧ natBit r.2.val 0 = wr)
        (fun ⟨k, xp, xr, wr⟩ => Finset.univ.filter fun r =>
          r.1 ⟨k.val, by omega⟩ = xp ∧ r.1 ⟨k.val + 1, by omega⟩ = xr ∧
            natBit r.2.val (k.val + 1) = wr)
      V := Sum.elim
        (fun ⟨xr, wr⟩ => Finset.univ.filter fun c =>
          xr + c.1 0 ≠ nextBorrow wr (natBit c.2.val 0) 0)
        (fun ⟨k, xp, xr, wr⟩ => Finset.univ.filter fun c =>
          xr + c.1 ⟨k.val + 1, by omega⟩ ≠
            nextBorrow wr (natBit c.2.val (k.val + 1)) (xp + c.1 ⟨k.val, by omega⟩))
      isBiclique := by
        rintro (⟨xr, wr⟩ | ⟨k, xp, xr, wr⟩) r hr c hc hK
        · rw [Sum.elim_inl, Finset.mem_filter] at hr hc
          have hloc := (K_coreRel_iff_local_transitions (m + 1) r c).mp hK 0
          simp only [Fin.val_zero, ↓reduceDIte] at hloc
          rw [hr.2.1, hr.2.2] at hloc
          exact hc.2 hloc
        · rw [Sum.elim_inr, Finset.mem_filter] at hr hc
          have hloc := (K_coreRel_iff_local_transitions (m + 1) r c).mp hK ⟨k.val + 1, by omega⟩
          simp only [Nat.succ_ne_zero, ↓reduceDIte, Nat.add_sub_cancel] at hloc
          rw [hr.2.1, hr.2.2.1, hr.2.2.2] at hloc
          exact hc.2 hloc
      covers := by
        intro r c hnot
        have hnot_all : ¬ ∀ j : Fin (m + 1), r.1 j + c.1 j =
            nextBorrow (natBit r.2.val j.val) (natBit c.2.val j.val)
              (if _hj : j.val = 0 then 0
               else r.1 ⟨j.val - 1, by omega⟩ + c.1 ⟨j.val - 1, by omega⟩) :=
          fun hall => hnot ((K_coreRel_iff_local_transitions (m + 1) r c).mpr hall)
        push Not at hnot_all
        rcases hnot_all with ⟨j, hj_ne⟩
        rcases j with ⟨jval, hjlt⟩
        rcases jval with _ | kval
        · simp only [↓reduceDIte] at hj_ne
          have h0 : (⟨0, hjlt⟩ : Fin (m + 1)) = 0 := rfl
          rw [h0] at hj_ne
          refine ⟨Sum.inl (r.1 0, natBit r.2.val 0), ?_, ?_⟩
          · simp
          · simp [hj_ne]
        · simp only [Nat.succ_ne_zero, ↓reduceDIte, Nat.add_sub_cancel] at hj_ne
          refine ⟨Sum.inr (⟨kval, by omega⟩, r.1 ⟨kval, by omega⟩,
            r.1 ⟨kval + 1, hjlt⟩, natBit r.2.val (kval + 1)), ?_, ?_⟩
          · simp
          · simp [hj_ne] }

theorem zeroCoverKCore_card_eq (s : ℕ) :
    Fintype.card (zeroCoverKCore s).L = if s = 0 then 0 else 8 * s - 4 := by
  cases s with
  | zero =>
    change Fintype.card PEmpty = 0
    simp
  | succ m =>
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    change Fintype.card ((ZMod 2 × ZMod 2) ⊕ (Fin m × ZMod 2 × ZMod 2 × ZMod 2)) =
      8 * (m + 1) - 4
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, ZMod.card]
    omega

/-- Explicit cover of all zero entries of `K_coreRel s` by at most `8 * s` (`0` for `s = 0`,
`8 * s - 4` for `s ≥ 1`) all-zeros rectangles (Proposition 4.2(c)). -/
theorem zero_cover_K_coreRel_card_le_eight_s (s : ℕ) :
    ∃ C : ExactBicliqueCover (fun r c => ¬ K_coreRel s r c),
      Fintype.card C.L ≤ 8 * s ∧
      (1 ≤ s → Fintype.card C.L = 8 * s - 4) := by
  refine ⟨zeroCoverKCore s, ?_, ?_⟩
  · rw [zeroCoverKCore_card_eq]
    split_ifs <;> omega
  · intro hs
    rw [zeroCoverKCore_card_eq]
    simp [show s ≠ 0 by omega]

/-- Alias of `zero_cover_K_coreRel_card_le_eight_s`. -/
theorem zero_cover_K_coreRel_card_le (s : ℕ) :
    ∃ C : ExactBicliqueCover (fun r c => ¬ K_coreRel s r c),
      Fintype.card C.L ≤ 8 * s := by
  obtain ⟨C, hle, _⟩ := zero_cover_K_coreRel_card_le_eight_s s
  exact ⟨C, hle⟩

/-- Indicator `{0, 1}` matrix of a combinatorial rectangle `U × V` over `ℝ`. -/
def rectIndicatorMat {α β : Type*} [DecidableEq α] [DecidableEq β]
    (U : Finset α) (V : Finset β) : Matrix α β ℝ :=
  fun r c => if r ∈ U ∧ c ∈ V then 1 else 0

/-- Explicit margin realization `S = J - 2 * ∑_{q} 1_{R_q}` for `K_coreRel s` decomposed into
`≤ 8 * s + 1` rank-1 `{0, 1}`-rectangles with `ℓ₁` weight `≤ 16 * s + 1` such that
`K_coreRel s r c → S r c = 1` and `¬ K_coreRel s r c → S r c ≤ -1` (Proposition 4.2(c)). -/
theorem margin_witness_K_coreRel (s : ℕ) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q)
      (U : Q → Finset ((Fin s → ZMod 2) × Fin (2 ^ s)))
      (V : Q → Finset ((Fin s → ZMod 2) × Fin (2 ^ s)))
      (w : Q → ℝ),
      let S : Matrix ((Fin s → ZMod 2) × Fin (2 ^ s)) ((Fin s → ZMod 2) × Fin (2 ^ s)) ℝ :=
        ∑ q : Q, w q • rectIndicatorMat (U q) (V q)
      Fintype.card Q ≤ 8 * s + 1 ∧
      (∑ q : Q, |w q|) ≤ (16 * s + 1 : ℝ) ∧
      (∀ r c, K_coreRel s r c → S r c = 1) ∧
      (∀ r c, ¬ K_coreRel s r c → S r c ≤ -1) := by
  let C₀ := zeroCoverKCore s
  let Q := Option C₀.L
  let U : Q → Finset ((Fin s → ZMod 2) × Fin (2 ^ s)) := fun q =>
    Option.elim q Finset.univ C₀.U
  let V : Q → Finset ((Fin s → ZMod 2) × Fin (2 ^ s)) := fun q =>
    Option.elim q Finset.univ C₀.V
  let w : Q → ℝ := fun q => Option.elim q (1 : ℝ) (fun _ => (-2 : ℝ))
  have hcardL : Fintype.card C₀.L ≤ 8 * s := by
    dsimp only [C₀]
    rw [zeroCoverKCore_card_eq]
    split_ifs <;> omega
  refine ⟨Q, inferInstance, inferInstance, U, V, w, ?_⟩
  dsimp only
  let S : Matrix ((Fin s → ZMod 2) × Fin (2 ^ s)) ((Fin s → ZMod 2) × Fin (2 ^ s)) ℝ :=
    ∑ q : Q, w q • rectIndicatorMat (U q) (V q)
  have hS_eval : ∀ r c, S r c =
      1 - 2 * ((Finset.univ.filter fun q : C₀.L => r ∈ C₀.U q ∧ c ∈ C₀.V q).card : ℝ) := by
    intro r c
    change (∑ q : Option C₀.L, w q • rectIndicatorMat (U q) (V q)) r c = _
    rw [Matrix.sum_apply, Fintype.sum_option]
    simp only [w, U, V, Option.elim_none, Option.elim_some, Matrix.smul_apply, smul_eq_mul,
      rectIndicatorMat, Finset.mem_univ, and_self, ↓reduceIte, mul_one]
    have hsum : ∑ x : C₀.L, (-2 : ℝ) * (if r ∈ C₀.U x ∧ c ∈ C₀.V x then (1 : ℝ) else 0) =
        (-2 : ℝ) * ((Finset.univ.filter fun q : C₀.L => r ∈ C₀.U q ∧ c ∈ C₀.V q).card : ℝ) := by
      rw [← Finset.mul_sum, Finset.card_filter, Nat.cast_sum]
      congr 1
      refine Finset.sum_congr rfl fun x _ => by split_ifs <;> simp
    rw [hsum]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · change Fintype.card (Option C₀.L) ≤ 8 * s + 1
    rw [Fintype.card_option]
    omega
  · rw [Fintype.sum_option]
    simp only [w, Option.elim_none, Option.elim_some, abs_one, abs_neg]
    have habs2 : |(2 : ℝ)| = 2 := by norm_num
    simp only [habs2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcast : (Fintype.card C₀.L : ℝ) ≤ (8 * s : ℝ) := by exact_mod_cast hcardL
    linarith
  · intro r c hK
    have hrc := hS_eval r c
    have hempty : (Finset.univ.filter fun q : C₀.L => r ∈ C₀.U q ∧ c ∈ C₀.V q) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro q _ ⟨hr, hc⟩
      exact C₀.isBiclique q r hr c hc hK
    rw [hempty, Finset.card_empty, Nat.cast_zero] at hrc
    dsimp only [S] at hrc
    linarith
  · intro r c hnotK
    have hrc := hS_eval r c
    obtain ⟨q₀, hr₀, hc₀⟩ := C₀.covers r c hnotK
    have hpos : 1 ≤ (Finset.univ.filter fun q : C₀.L => r ∈ C₀.U q ∧ c ∈ C₀.V q).card :=
      Finset.card_pos.mpr ⟨q₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr₀, hc₀⟩⟩
    have hpos_r : (1 : ℝ) ≤
        ((Finset.univ.filter fun q : C₀.L => r ∈ C₀.U q ∧ c ∈ C₀.V q).card : ℝ) := by
      exact_mod_cast hpos
    dsimp only [S] at hrc
    linarith

end CarryAutomaton
