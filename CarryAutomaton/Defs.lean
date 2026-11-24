module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

@[expose] public section

/-!
# Shared Definitions for `CarryAutomaton`

Core definitions for the canonical modular Addition–XOR relation `M_t`, its borrow-core
biadjacency matrix (denoted `C_t` in Paper 2 and parameterized cleanly by `s = t - 1` via
`K_coreRel s` / `K_coreMat` / `K_mat` in Lean), the `i`-bit borrow indicator vector `borrowVec`,
bicliques, exact biclique covers, zero-duplicate biclique partitions, label weight, and maximum
vertex load.
-/

namespace CarryAutomaton

open Finset BigOperators

/-- Canonical modular Addition–XOR relation on `(ℤ/2^t ℤ)² × (ℤ/2^t ℤ)²`:
`M_rel t (u, w) (v, z) ↔ (u ⊕ v) + w ≡ z (mod 2^t)`. -/
def M_rel (t : ℕ) (r c : Fin (2 ^ t) × Fin (2 ^ t)) : Prop :=
  ((r.1.val ^^^ c.1.val) + r.2.val) % 2 ^ t = c.2.val

instance (t : ℕ) (r c : Fin (2 ^ t) × Fin (2 ^ t)) : Decidable (M_rel t r c) :=
  inferInstanceAs (Decidable (((r.1.val ^^^ c.1.val) + r.2.val) % 2 ^ t = c.2.val))

/-- Biadjacency matrix `M_t` over any ring/semiring `R`. -/
def M_mat (R : Type*) [Zero R] [One R] (t : ℕ) :
    Matrix (Fin (2 ^ t) × Fin (2 ^ t)) (Fin (2 ^ t) × Fin (2 ^ t)) R :=
  fun r c => if M_rel t r c then 1 else 0

/-- `i`-bit strict borrow indicator `c_i(w', z') = 1[(w' mod 2^i) > (z' mod 2^i)]` in `ZMod 2`. -/
def borrowBit (i : ℕ) (w z : ℕ) : ZMod 2 :=
  if z % 2 ^ i < w % 2 ^ i then 1 else 0

/-- `s`-bit borrow vector `c(w', z') = (c_1(w', z'), ..., c_s(w', z')) ∈ (ZMod 2)^s`. -/
def borrowVec (s : ℕ) (w z : Fin (2 ^ s)) : Fin s → ZMod 2 :=
  fun i => borrowBit (i.val + 1) w.val z.val

/-- Borrow-core relation `K_t` (with `s = t - 1`):
`K_coreRel s (x', w') (y', z') ↔ x' + y' = borrowVec s w' z'` over `𝔽₂^s`. -/
def K_coreRel (s : ℕ) (r c : (Fin s → ZMod 2) × Fin (2 ^ s)) : Prop :=
  r.1 + c.1 = borrowVec s r.2 c.2

instance (s : ℕ) (r c : (Fin s → ZMod 2) × Fin (2 ^ s)) : Decidable (K_coreRel s r c) :=
  inferInstanceAs (Decidable (r.1 + c.1 = borrowVec s r.2 c.2))

/-- Biadjacency matrix of the `2^{2s} × 2^{2s}` borrow core `K_{s+1}`. -/
def K_coreMat (R : Type*) [Zero R] [One R] (s : ℕ) :
    Matrix ((Fin s → ZMod 2) × Fin (2 ^ s)) ((Fin s → ZMod 2) × Fin (2 ^ s)) R :=
  fun r c => if K_coreRel s r c then 1 else 0

/-- Biadjacency matrix `K_t` for `t ≥ 1` (`s = t - 1`). -/
abbrev K_mat (R : Type*) [Zero R] [One R] (t : ℕ) :=
  K_coreMat R (t - 1)

/-! ### Bicliques, Covers, Partitions, Weights, and Local Loads -/

/-- A rectangle `U × V` is an all-ones biclique of relation `R`. -/
def IsBiclique {α β : Type*} (R : α → β → Prop) (U : Finset α) (V : Finset β) : Prop :=
  ∀ r ∈ U, ∀ c ∈ V, R r c

/-- A nonempty all-ones biclique of `R`. -/
def IsNonemptyBiclique {α β : Type*} (R : α → β → Prop) (U : Finset α) (V : Finset β) : Prop :=
  U.Nonempty ∧ V.Nonempty ∧ IsBiclique R U V

/-- A maximal (inclusion-maximal) nonempty biclique of `R`. -/
def IsMaximalBiclique {α β : Type*} (R : α → β → Prop) (U : Finset α) (V : Finset β) : Prop :=
  IsNonemptyBiclique R U V ∧
    ∀ U' V', IsBiclique R U' V' → U ⊆ U' → V ⊆ V' → U' = U ∧ V' = V

/-- A finite family of bicliques indexed by `L` forming an exact biclique cover of `R`. -/
structure ExactBicliqueCover {α β : Type*} (R : α → β → Prop) where
  L : Type
  [fintypeL : Fintype L]
  [decEqL : DecidableEq L]
  U : L → Finset α
  V : L → Finset β
  isBiclique : ∀ ℓ, IsBiclique R (U ℓ) (V ℓ)
  covers : ∀ r c, R r c → ∃ ℓ, r ∈ U ℓ ∧ c ∈ V ℓ

attribute [instance] ExactBicliqueCover.fintypeL ExactBicliqueCover.decEqL

/-- An exact biclique cover is a zero-duplicate biclique partition if every 1-entry lies in
exactly one biclique. -/
def ExactBicliqueCover.IsPartition {α β : Type*} {R : α → β → Prop}
    (C : ExactBicliqueCover R) : Prop :=
  ∀ r c, R r c → ∃! ℓ, r ∈ C.U ℓ ∧ c ∈ C.V ℓ

/-- Row degree `|A(r)|` of row `r` in a biclique cover. -/
def ExactBicliqueCover.rowLoad {α β : Type*} [DecidableEq α] {R : α → β → Prop}
    (C : ExactBicliqueCover R) (r : α) : ℕ :=
  (Finset.univ.filter fun ℓ => r ∈ C.U ℓ).card

/-- Column degree `|B(c)|` of column `c` in a biclique cover. -/
def ExactBicliqueCover.colLoad {α β : Type*} [DecidableEq β] {R : α → β → Prop}
    (C : ExactBicliqueCover R) (c : β) : ℕ :=
  (Finset.univ.filter fun ℓ => c ∈ C.V ℓ).card

/-- Total row emissions `∑_r |A(r)| = ∑_ℓ |U_ℓ|`. -/
def ExactBicliqueCover.totalRowLoad {α β : Type*} {R : α → β → Prop}
    (C : ExactBicliqueCover R) : ℕ :=
  ∑ ℓ : C.L, (C.U ℓ).card

/-- Total column emissions `∑_c |B(c)| = ∑_ℓ |V_ℓ|`. -/
def ExactBicliqueCover.totalColLoad {α β : Type*} {R : α → β → Prop}
    (C : ExactBicliqueCover R) : ℕ :=
  ∑ ℓ : C.L, (C.V ℓ).card

/-- Total label weight `W_label = ∑_ℓ (|U_ℓ| + |V_ℓ|)`. -/
def ExactBicliqueCover.labelWeight {α β : Type*} {R : α → β → Prop}
    (C : ExactBicliqueCover R) : ℕ :=
  C.totalRowLoad + C.totalColLoad

/-- Maximum vertex load `≤ k` on both rows and columns. -/
def ExactBicliqueCover.HasMaxLoadLe {α β : Type*} [DecidableEq α] [DecidableEq β]
    {R : α → β → Prop} (C : ExactBicliqueCover R) (k : ℕ) : Prop :=
  (∀ r, C.rowLoad r ≤ k) ∧ (∀ c, C.colLoad c ≤ k)

lemma ExactBicliqueCover.sum_rowLoad {α β : Type*} [Fintype α] [DecidableEq α]
    {R : α → β → Prop} (C : ExactBicliqueCover R) :
    ∑ r : α, C.rowLoad r = C.totalRowLoad := by
  simp only [ExactBicliqueCover.rowLoad, ExactBicliqueCover.totalRowLoad,
    Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp

lemma ExactBicliqueCover.sum_colLoad {α β : Type*} [Fintype β] [DecidableEq β]
    {R : α → β → Prop} (C : ExactBicliqueCover R) :
    ∑ c : β, C.colLoad c = C.totalColLoad := by
  simp only [ExactBicliqueCover.colLoad, ExactBicliqueCover.totalColLoad,
    Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp

end CarryAutomaton
