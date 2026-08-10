import Mathlib

/-!
# First-Degree Entailment (FDE) — Belnap–Dunn four-valued logic

Formalization of FDE: syntax, the four-valued semantics over the Belnap bilattice,
designated-value consequence, and (target) soundness and completeness of a proof system.

Semantics (Dunn/Belnap): a valuation assigns each atom one of four values:
- `t` — told true only
- `f` — told false only
- `b` — told both true and false
- `n` — told neither

The designated values (those that preserve consequence) are `t` and `b`.
Negation swaps `t`↔`f` and fixes `b`,`n`; conjunction is glb and disjunction lub in the
truth order `f < b,n < t`... actually we define the operations explicitly on the
four-element type rather than via a lattice instance, to keep the semantics elementary.
-/

namespace FDE

/-- The four Belnap–Dunn truth values. -/
inductive Val4 where
  | t  -- told true only
  | f  -- told false only
  | b  -- told both
  | n  -- told neither
  deriving DecidableEq, Repr

/-- Designated values: told-true (t) and both (b). -/
def Val4.designated : Val4 → Bool
  | .t => true
  | .b => true
  | .f => false
  | .n => false

/-- Negation on the four values. -/
def Val4.neg : Val4 → Val4
  | .t => .f
  | .f => .t
  | .b => .b
  | .n => .n

/-- Conjunction (truth-order glb). -/
def Val4.and : Val4 → Val4 → Val4
  | .f, _ => .f
  | _, .f => .f
  | .t, x => x
  | x, .t => x
  | .b, .b => .b
  | .n, .n => .n
  | .b, .n => .f  -- both ∧ neither: true-lower bound... in truth order glb(b,n)=f
  | .n, .b => .f

/-- Disjunction (truth-order lub). -/
def Val4.or : Val4 → Val4 → Val4
  | .t, _ => .t
  | _, .t => .t
  | .f, x => x
  | x, .f => x
  | .b, .b => .b
  | .n, .n => .n
  | .b, .n => .t  -- lub(b,n)=t in truth order
  | .n, .b => .t

/-- Formulas of FDE: atoms, negation, conjunction, disjunction.
    (No implication — FDE is the implication-free fragment; adding one is future work.) -/
inductive Formula where
  | atom : ℕ → Formula
  | neg : Formula → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
  deriving DecidableEq, Repr

/-- A valuation assigns a four-value to each atom. -/
abbrev Valuation := ℕ → Val4

/-- Evaluate a formula under a valuation. -/
def eval (v : Valuation) : Formula → Val4
  | .atom p => v p
  | .neg φ => (eval v φ).neg
  | .and φ ψ => (eval v φ).and (eval v ψ)
  | .or φ ψ => (eval v φ).or (eval v ψ)

/-- Semantic consequence: Γ ⊨ φ iff every valuation designating all of Γ also designates φ. -/
def Entails (Γ : Set Formula) (φ : Formula) : Prop :=
  ∀ v : Valuation, (∀ γ ∈ Γ, (eval v γ).designated) → (eval v φ).designated

end FDE
