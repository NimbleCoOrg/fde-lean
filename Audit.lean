import FDE.Corollaries

open FDE

-- (1) Axiom footprint as published
#print axioms FDE.Deriv.sound
#print axioms FDE.completeness
#print axioms FDE.decidable_deriv
#print axioms FDE.deriv_iff_valid
#print axioms FDE.no_valid_formula
#print axioms FDE.disjunction_property

-- (2) Is the "decidability" statement classically trivial?
--     If this one-liner typechecks, the statement carries no decision content.
example (S : Sequent) : (⊢ₛ S) ∨ (¬ ⊢ₛ S) := Classical.em _

-- (3) Does the Decidable instance actually compute a decision?
example : Bool := decide (⊢ₛ (Sequent.mk [Formula.atom 0] [Formula.atom 0]))
