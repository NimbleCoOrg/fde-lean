import FDE.Basic

/-!
# A sequent calculus for FDE

Sequents `Γ ⇒ Δ` are pairs of formula multisets (here: lists). The intended reading is the
**four-valued** one: a valuation `v` *satisfies* `Γ ⇒ Δ` iff, whenever every formula in `Γ`
is designated under `v` (i.e. has truth-support: value `t` or `b`), some formula in `Δ` is
designated under `v`.

Because FDE has no separate falsity side in this reading, the negation rules push negation
inward (negation normal form) rather than moving formulas across the turnstile. We handle
this by working with formulas already in a negation-normalized calculus: the rules for `¬`
decompose `¬(φ ∧ ψ)` / `¬(φ ∨ ψ)` / `¬¬φ` on both sides.

This is the standard G3-style invertible calculus for FDE (cf. the four-sided sequent
systems of Omori–Wansing / Wansing, here collapsed to the two-sided designated-truth
fragment which suffices for first-degree entailment).

## Rules (all invertible)
- `id`:  `Γ, atom p ⇒ Δ, atom p`   (only for atoms — atomic initial sequents)
- `∧L`: from `Γ, φ, ψ ⇒ Δ` infer `Γ, φ ∧ ψ ⇒ Δ`
- `∧R`: from `Γ ⇒ Δ, φ` and `Γ ⇒ Δ, ψ` infer `Γ ⇒ Δ, φ ∧ ψ`
- `∨L`: from `Γ, φ ⇒ Δ` and `Γ, ψ ⇒ Δ` infer `Γ, φ ∨ ψ ⇒ Δ`
- `∨R`: from `Γ ⇒ Δ, φ, ψ` infer `Γ ⇒ Δ, φ ∨ ψ`
- `¬L`/`¬R`: decompose negations by De Morgan + double negation (NNF descent)
-/

namespace FDE

/-- A sequent: antecedent and succedent are lists of formulas. -/
structure Sequent where
  antecedent : List Formula
  succedent : List Formula
  deriving DecidableEq, Repr

/-- Notation `Γ ⇒ Δ` for sequents. -/
scoped notation Γ " ⇒ " Δ => Sequent.mk Γ Δ

/-- A valuation satisfies a sequent: if everything in the antecedent is designated,
    then something in the succedent is designated. -/
def Sequent.Satisfied (v : Valuation) : Sequent → Prop
  | ⟨Γ, Δ⟩ => (∀ γ ∈ Γ, (eval v γ).designated) → (∃ δ ∈ Δ, (eval v δ).designated)

/-- A sequent is valid iff every valuation satisfies it. -/
def Sequent.Valid (S : Sequent) : Prop := ∀ v, S.Satisfied v

/-- The derivability predicate for the FDE sequent calculus (NNF-based).
    `⊢ₛ S` means the sequent `S` is derivable.

    Structural rules: we work with *lists* but close under exchange (permutation) on both
    sides via the `ex` constructor. Contraction and weakening are *admissible* for this
    system (proved later); we don't need them as primitives because the logical rules
    duplicate/erase context as required. -/
inductive Deriv : Sequent → Prop where
  /-- Atomic initial sequent: `Γ, atom p ⇒ Δ, atom p`. -/
  | id (Γ Δ : List Formula) (p : ℕ) :
      Deriv (⟨.atom p :: Γ, .atom p :: Δ⟩)
  /-- Negated-atom initial sequent: `Γ, ¬p ⇒ Δ, ¬p`. Valid because `¬p` designated is
      the same condition on both sides. Required for completeness: proof search can bottom
      out at a literal sequent whose only shared atom across the turnstile is negated. -/
  | idNeg (Γ Δ : List Formula) (p : ℕ) :
      Deriv (⟨.neg (.atom p) :: Γ, .neg (.atom p) :: Δ⟩)
  /-- Exchange on both sides: permuting antecedent and succedent preserves derivability. -/
  | ex {Γ Γ' Δ Δ' : List Formula} :
      List.Perm Γ Γ' → List.Perm Δ Δ' →
      Deriv (⟨Γ, Δ⟩) →
      Deriv (⟨Γ', Δ'⟩)
  /-- Left conjunction. -/
  | andL {Γ Δ φ ψ} :
      Deriv (⟨φ :: ψ :: Γ, Δ⟩) →
      Deriv (⟨.and φ ψ :: Γ, Δ⟩)
  /-- Right conjunction. -/
  | andR {Γ Δ φ ψ} :
      Deriv (⟨Γ, φ :: Δ⟩) → Deriv (⟨Γ, ψ :: Δ⟩) →
      Deriv (⟨Γ, .and φ ψ :: Δ⟩)
  /-- Left disjunction. -/
  | orL {Γ Δ φ ψ} :
      Deriv (⟨φ :: Γ, Δ⟩) → Deriv (⟨ψ :: Γ, Δ⟩) →
      Deriv (⟨.or φ ψ :: Γ, Δ⟩)
  /-- Right disjunction. -/
  | orR {Γ Δ φ ψ} :
      Deriv (⟨Γ, φ :: ψ :: Δ⟩) →
      Deriv (⟨Γ, .or φ ψ :: Δ⟩)
  /-- Left double negation. -/
  | negnegL {Γ Δ φ} :
      Deriv (⟨φ :: Γ, Δ⟩) →
      Deriv (⟨.neg (.neg φ) :: Γ, Δ⟩)
  /-- Right double negation. -/
  | negnegR {Γ Δ φ} :
      Deriv (⟨Γ, φ :: Δ⟩) →
      Deriv (⟨Γ, .neg (.neg φ) :: Δ⟩)
  /-- Left negated conjunction (De Morgan): `¬(φ ∧ ψ)` behaves as `¬φ ∨ ¬ψ`. -/
  | negandL {Γ Δ φ ψ} :
      Deriv (⟨.neg φ :: Γ, Δ⟩) → Deriv (⟨.neg ψ :: Γ, Δ⟩) →
      Deriv (⟨.neg (.and φ ψ) :: Γ, Δ⟩)
  /-- Right negated conjunction: `¬(φ ∧ ψ)` on the right behaves as `¬φ ∨ ¬ψ`. -/
  | negandR {Γ Δ φ ψ} :
      Deriv (⟨Γ, .neg φ :: .neg ψ :: Δ⟩) →
      Deriv (⟨Γ, .neg (.and φ ψ) :: Δ⟩)
  /-- Left negated disjunction (De Morgan): `¬(φ ∨ ψ)` behaves as `¬φ ∧ ¬ψ`. -/
  | negorL {Γ Δ φ ψ} :
      Deriv (⟨.neg φ :: .neg ψ :: Γ, Δ⟩) →
      Deriv (⟨.neg (.or φ ψ) :: Γ, Δ⟩)
  /-- Right negated disjunction: `¬(φ ∨ ψ)` on the right behaves as `¬φ ∧ ¬ψ`. -/
  | negorR {Γ Δ φ ψ} :
      Deriv (⟨Γ, .neg φ :: Δ⟩) → Deriv (⟨Γ, .neg ψ :: Δ⟩) →
      Deriv (⟨Γ, .neg (.or φ ψ) :: Δ⟩)

/-- Notation: `⊢ₛ S` for derivability. -/
scoped notation "⊢ₛ " S => Deriv S

end FDE
