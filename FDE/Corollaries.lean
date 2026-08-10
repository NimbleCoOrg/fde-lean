import FDE.Completeness

/-!
# Corollaries of soundness and completeness for FDE

Three downstream results, each a direct consequence of the soundness/completeness pair:

1. **`no_valid_formula` — FDE has no theorems.** The constant-`n` valuation evaluates every
   formula to `n` (both `neg` and the binary connectives fix `n`), and `n` is not designated.
   Hence no single-conclusion sequent `⟨[], [φ]⟩` is valid, and by soundness none is
   derivable. This is the famous "no logical truths" feature of first-degree entailment.

2. **`disjunction_property` — vacuously true, and we say so.** Since `⊢ₛ ⟨[], [φ ∨ ψ]⟩`
   never happens (point 1), any statement with it as antecedent holds vacuously. The
   *substantive* disjunction property at the sequent level is `orR_inv` (proved in
   `FDE.Completeness`): `Γ ⇒ Δ, φ ∨ ψ` is valid iff `Γ ⇒ Δ, φ, ψ` is valid.

3. **`decidable_deriv` — derivability is decidable.** The decision procedure is proof
   search, mirroring `completeness_aux`: well-founded recursion on the sequent measure,
   casing on `decompose`. The only genuinely new check is the atomic-initial decision at the
   leaf (`decide_sat_or`): with all-literal sequents, "initial or saturated" is decidable
   because an atom `p` witnessing `atom p ∈ Γ ∧ atom p ∈ Δ` must occur in `Γ`, so the
   existential over `ℕ` reduces to a bounded scan of the antecedent. The underivable branches
   are justified by the **sound → invert → complete loop**: if `S` were derivable it would be
   valid (soundness), so its premises would be valid (the matching inversion lemma), so they
   would be derivable (completeness) — contradicting the recursive underivability result.

   As a consequence, validity of sequents is also decidable (`deriv_iff_valid`).
-/

namespace FDE

/-! ## A. No valid formulas -/

/-- The constant-`n` valuation sends every formula to `n`: negation and both connectives
    all fix `n`. This is the semantic heart of "FDE has no theorems". -/
theorem eval_const_n (φ : Formula) : eval (fun _ => .n) φ = .n := by
  induction φ with
  | atom p => rfl
  | neg φ ih => simp [eval, ih, Val4.neg]
  | and φ ψ ihφ ihψ => simp [eval, ihφ, ihψ, Val4.and]
  | or φ ψ ihφ ihψ => simp [eval, ihφ, ihψ, Val4.or]

/-- **FDE has no valid formulas**: for every `φ`, the sequent `⟨[], [φ]⟩` is refuted by the
    constant-`n` valuation. The antecedent is vacuously designated; the sole succedent
    formula evaluates to non-designated `n`. -/
theorem no_valid_formula (φ : Formula) : ¬ Sequent.Valid ⟨[], [φ]⟩ := by
  intro h
  have hdes := h (fun _ => .n) (fun γ hγ => by cases hγ)
  rcases hdes with ⟨δ, hδ, hδdes⟩
  have : δ = φ := List.mem_singleton.mp hδ
  subst this
  rw [eval_const_n] at hδdes
  exact Bool.noConfusion hδdes

/-- Corollary: no formula is derivable as a theorem of the calculus. -/
theorem no_derivable_formula (φ : Formula) : ¬ ⊢ₛ ⟨[], [φ]⟩ :=
  fun h => no_valid_formula φ h.sound

/-! ## B. Disjunction property (vacuous) -/

/-- **The disjunction property, vacuously**: a derivable `φ ∨ ψ` would be a theorem of FDE,
    but FDE has no theorems. The interesting sequent-level disjunction property —
    `orR`-invertibility — is `orR_inv` in `FDE.Completeness`. -/
theorem disjunction_property {φ ψ : Formula} (h : ⊢ₛ ⟨[], [Formula.or φ ψ]⟩) :
    (⊢ₛ ⟨[], [φ]⟩) ∨ (⊢ₛ ⟨[], [ψ]⟩) := by
  exfalso
  exact no_derivable_formula (Formula.or φ ψ) h

/-- The sequent-level disjunction property IS substantive: `orR`-invertibility says
    `Γ ⇒ Δ, φ ∨ ψ` is valid iff `Γ ⇒ Δ, φ, ψ` is valid. (Restated here for discoverability;
    the proof lives in `FDE.Completeness`.) -/
theorem disjunction_property_sequent {Γ Δ : List Formula} {φ ψ : Formula}
    (h : Sequent.Valid ⟨Γ, .or φ ψ :: Δ⟩) : Sequent.Valid ⟨Γ, φ :: ψ :: Δ⟩ :=
  orR_inv h

/-! ## C. Decidability of derivability -/

/-- `isLiteral` is decidable: `atom` and `neg (atom _)` are literal, everything else
    isn't. -/
instance Formula.decidableIsLiteral (φ : Formula) : Decidable φ.isLiteral := by
  cases φ with
  | atom p => exact isTrue trivial
  | neg ψ =>
      cases ψ with
      | atom p => exact isTrue trivial
      | neg _ => exact isFalse id
      | and _ _ => exact isFalse id
      | or _ _ => exact isFalse id
  | and _ _ => exact isFalse id
  | or _ _ => exact isFalse id

/-- Per-formula decision for the atom-shape predicate used by `decidable_pos_pair`: either
    `φ` is literally `atom p` for some `p` (then check membership in `Δ`), or no such `p`
    exists. This bounds the `∃ p : ℕ` to the single candidate `φ` might be. -/
instance decidable_atom_mem (φ : Formula) (Δ : List Formula) :
    Decidable (∃ p, φ = .atom p ∧ (.atom p) ∈ Δ) := by
  cases φ with
  | atom p =>
      cases (inferInstance : Decidable ((.atom p) ∈ Δ)) with
      | isTrue h => exact isTrue ⟨p, rfl, h⟩
      | isFalse h =>
          exact isFalse (fun hw => by
            obtain ⟨q, hq, hmem⟩ := hw
            have : q = p := Formula.atom.inj hq.symm
            subst this
            exact h hmem)
  | neg ψ => exact isFalse (fun hw => by obtain ⟨_, hq, _⟩ := hw; cases hq)
  | and a b => exact isFalse (fun hw => by obtain ⟨_, hq, _⟩ := hw; cases hq)
  | or a b => exact isFalse (fun hw => by obtain ⟨_, hq, _⟩ := hw; cases hq)

/-- Per-formula decision for the negated-atom shape, used by `decidable_neg_pair`. -/
instance decidable_neg_atom_mem (φ : Formula) (Δ : List Formula) :
    Decidable (∃ p, φ = .neg (.atom p) ∧ (.neg (.atom p)) ∈ Δ) := by
  cases φ with
  | atom p => exact isFalse (fun hw => by obtain ⟨_, hq, _⟩ := hw; cases hq)
  | neg ψ =>
      cases ψ with
      | atom p =>
          cases (inferInstance : Decidable ((.neg (.atom p)) ∈ Δ)) with
          | isTrue h => exact isTrue ⟨p, rfl, h⟩
          | isFalse h =>
              exact isFalse (fun hw => by
                obtain ⟨q, hq, hmem⟩ := hw
                have : q = p := by
                  have := Formula.neg.inj hq.symm
                  exact Formula.atom.inj this
                subst this
                exact h hmem)
      | neg χ => exact isFalse (fun hw => by obtain ⟨_, hq, _⟩ := hw; cases hq)
      | and a b => exact isFalse (fun hw => by obtain ⟨_, hq, _⟩ := hw; cases hq)
      | or a b => exact isFalse (fun hw => by obtain ⟨_, hq, _⟩ := hw; cases hq)
  | and a b => exact isFalse (fun hw => by obtain ⟨_, hq, _⟩ := hw; cases hq)
  | or a b => exact isFalse (fun hw => by obtain ⟨_, hq, _⟩ := hw; cases hq)

/-- The positive identity pair `∃ p, atom p ∈ Γ ∧ atom p ∈ Δ` is decidable: a witness must
    occur in `Γ`, so the `∃ p : ℕ` reduces to a bounded scan of `Γ` (which the library's
    `∃ a ∈ l, P a` instance handles, given the per-element `decidable_atom_mem`). -/
instance decidable_pos_pair (S : Sequent) :
    Decidable (∃ p, (.atom p) ∈ S.antecedent ∧ (.atom p) ∈ S.succedent) :=
  decidable_of_decidable_of_iff (p := ∃ φ ∈ S.antecedent,
      ∃ p, φ = .atom p ∧ (.atom p) ∈ S.succedent)
    (q := ∃ p, (.atom p) ∈ S.antecedent ∧ (.atom p) ∈ S.succedent)
    ⟨fun h => by
       obtain ⟨φ, hφ, p, rfl, hpR⟩ := h
       exact ⟨p, hφ, hpR⟩,
     fun h => by
       obtain ⟨p, hpL, hpR⟩ := h
       exact ⟨.atom p, hpL, p, rfl, hpR⟩⟩

/-- The negative identity pair `∃ p, ¬p ∈ Γ ∧ ¬p ∈ Δ` is decidable by the same scan. -/
instance decidable_neg_pair (S : Sequent) :
    Decidable (∃ p, (.neg (.atom p)) ∈ S.antecedent ∧ (.neg (.atom p)) ∈ S.succedent) :=
  decidable_of_decidable_of_iff (p := ∃ φ ∈ S.antecedent,
      ∃ p, φ = .neg (.atom p) ∧ (.neg (.atom p)) ∈ S.succedent)
    (q := ∃ p, (.neg (.atom p)) ∈ S.antecedent ∧ (.neg (.atom p)) ∈ S.succedent)
    ⟨fun h => by
       obtain ⟨φ, hφ, p, rfl, hpR⟩ := h
       exact ⟨p, hφ, hpR⟩,
     fun h => by
       obtain ⟨p, hpL, hpR⟩ := h
       exact ⟨.neg (.atom p), hpL, p, rfl, hpR⟩⟩

/-- Leaf decision for the decider: on a sequent whose formulas are all literals, either an
    identity pair is present (positive or negative) or the sequent is saturated. This is
    the *decidable* content of the all-literal branch of `decompose`. Note we do NOT need
    a `Decidable S.Saturated` instance (its `∀ p : ℕ` conjuncts are unbounded): the
    saturation proof is assembled directly from the two decided pair-negations. -/
theorem decide_sat_or (S : Sequent)
    (hL : ∀ γ ∈ S.antecedent, γ.isLiteral) (hR : ∀ δ ∈ S.succedent, δ.isLiteral) :
    (∃ p, (.atom p) ∈ S.antecedent ∧ (.atom p) ∈ S.succedent) ∨
    (∃ p, (.neg (.atom p)) ∈ S.antecedent ∧ (.neg (.atom p)) ∈ S.succedent) ∨
    S.Saturated := by
  cases decidable_pos_pair S with
  | isTrue h => exact Or.inl h
  | isFalse hpos =>
      cases decidable_neg_pair S with
      | isTrue h => exact Or.inr (Or.inl h)
      | isFalse hneg =>
          exact Or.inr (Or.inr ⟨hL, hR, fun p hp => hpos ⟨p, hp⟩, fun p hp => hneg ⟨p, hp⟩⟩)

/-- An identity pair yields a derivation, via permutation to head position. -/
theorem deriv_of_pos_pair {S : Sequent}
    (h : ∃ p, (.atom p) ∈ S.antecedent ∧ (.atom p) ∈ S.succedent) : ⊢ₛ S := by
  obtain ⟨p, hpL, hpR⟩ := h
  obtain ⟨Γ₀, hΓ⟩ := left_perm_of_mem hpL
  obtain ⟨Δ₀, hΔ⟩ := right_perm_of_mem hpR
  exact Deriv.ex hΓ.symm hΔ.symm (Deriv.id Γ₀ Δ₀ p)

/-- The negative-atom analogue. -/
theorem deriv_of_neg_pair {S : Sequent}
    (h : ∃ p, (.neg (.atom p)) ∈ S.antecedent ∧ (.neg (.atom p)) ∈ S.succedent) : ⊢ₛ S := by
  obtain ⟨p, hpL, hpR⟩ := h
  obtain ⟨Γ₀, hΓ⟩ := left_perm_of_mem hpL
  obtain ⟨Δ₀, hΔ⟩ := right_perm_of_mem hpR
  exact Deriv.ex hΓ.symm hΔ.symm (Deriv.idNeg Γ₀ Δ₀ p)

/-- **Derivability is decidable**, as a Prop-valued disjunction: every sequent is either
    derivable or (refutably) not. Proved by strong induction on the measure, mirroring
    `completeness_aux`: case on `decompose`. The initial branch gives `inl`; the saturated
    branch gives `inr` (the refuting valuation + soundness); each rule branch recurses on
    its premises — all derivable assembles via the rule, and any underivable premise makes
    `S` underivable by the **sound → invert → complete loop**: `⊢ₛ S` would give `Valid S`
    (soundness), hence `Valid` of the premise (the matching `_inv` lemma, transported across
    the permutation), hence `⊢ₛ` premise (completeness) — contradicting the recursive result.
    No derivability-level invertibility (cut-admissibility) is needed; it falls out of the
    loop. The decision is stated in `Prop` (not as a `Decidable`/`PSum` value) because
    `decompose`'s `Or`/`∃` only eliminate into `Prop` — the `Decidable` instance and `PSum`
    procedure are recovered from this via `Classical` choice. -/
theorem derivable_or_not : ∀ (n : ℕ) (S : Sequent), S.measure = n → (⊢ₛ S) ∨ (¬ ⊢ₛ S) := by
  intro n
  induction' n using Nat.strong_induction_on with n ih
  intro S hmeas
  obtain d | d | d | d | d | d | d | d | d | d | d | d := decompose S
  · exact Or.inl d
  · -- saturated: refuting valuation + soundness gives underivability
    exact Or.inr fun hd => by
      obtain ⟨hLdes, hRdes⟩ := Saturated.refutes d
      obtain ⟨δ, hδ, hδdes⟩ := hd.sound S.refutingVal hLdes
      exact hRdes δ hδ hδdes
  · -- andL (one premise)
    obtain ⟨φ, ψ, Γ₀, hΓ⟩ := d
    have hlt : Sequent.measure ⟨φ :: ψ :: Γ₀, S.succedent⟩ < n := by
      rw [← hmeas]; exact measure_andL hΓ
    cases ih _ hlt _ rfl with
    | inl hd => exact Or.inl (Deriv.ex hΓ.symm (List.Perm.refl _) (Deriv.andL hd))
    | inr hnd =>
        exact Or.inr fun hS => hnd (completeness (andL_inv
          (valid_of_perm hΓ.symm (List.Perm.refl _) hS.sound)))
  · -- andR (two premises)
    obtain ⟨φ, ψ, Δ₀, hΔ⟩ := d
    have hltφ : Sequent.measure ⟨S.antecedent, φ :: Δ₀⟩ < n := by
      rw [← hmeas]; exact (measure_andR hΔ).1
    have hltψ : Sequent.measure ⟨S.antecedent, ψ :: Δ₀⟩ < n := by
      rw [← hmeas]; exact (measure_andR hΔ).2
    cases ih _ hltφ _ rfl with
    | inl hdφ =>
        cases ih _ hltψ _ rfl with
        | inl hdψ =>
            exact Or.inl (Deriv.ex (List.Perm.refl _) hΔ.symm (Deriv.andR hdφ hdψ))
        | inr hndψ =>
            exact Or.inr fun hS => hndψ (completeness ((andR_inv
              (valid_of_perm (List.Perm.refl _) hΔ.symm hS.sound)).2))
    | inr hndφ =>
        exact Or.inr fun hS => hndφ (completeness ((andR_inv
          (valid_of_perm (List.Perm.refl _) hΔ.symm hS.sound)).1))
  · -- orL (two premises)
    obtain ⟨φ, ψ, Γ₀, hΓ⟩ := d
    have hltφ : Sequent.measure ⟨φ :: Γ₀, S.succedent⟩ < n := by
      rw [← hmeas]; exact (measure_orL hΓ).1
    have hltψ : Sequent.measure ⟨ψ :: Γ₀, S.succedent⟩ < n := by
      rw [← hmeas]; exact (measure_orL hΓ).2
    cases ih _ hltφ _ rfl with
    | inl hdφ =>
        cases ih _ hltψ _ rfl with
        | inl hdψ =>
            exact Or.inl (Deriv.ex hΓ.symm (List.Perm.refl _) (Deriv.orL hdφ hdψ))
        | inr hndψ =>
            exact Or.inr fun hS => hndψ (completeness ((orL_inv
              (valid_of_perm hΓ.symm (List.Perm.refl _) hS.sound)).2))
    | inr hndφ =>
        exact Or.inr fun hS => hndφ (completeness ((orL_inv
          (valid_of_perm hΓ.symm (List.Perm.refl _) hS.sound)).1))
  · -- orR (one premise)
    obtain ⟨φ, ψ, Δ₀, hΔ⟩ := d
    have hlt : Sequent.measure ⟨S.antecedent, φ :: ψ :: Δ₀⟩ < n := by
      rw [← hmeas]; exact measure_orR hΔ
    cases ih _ hlt _ rfl with
    | inl hd => exact Or.inl (Deriv.ex (List.Perm.refl _) hΔ.symm (Deriv.orR hd))
    | inr hnd =>
        exact Or.inr fun hS => hnd (completeness (orR_inv
          (valid_of_perm (List.Perm.refl _) hΔ.symm hS.sound)))
  · -- negnegL (one premise)
    obtain ⟨φ, Γ₀, hΓ⟩ := d
    have hlt : Sequent.measure ⟨φ :: Γ₀, S.succedent⟩ < n := by
      rw [← hmeas]; exact measure_negnegL hΓ
    cases ih _ hlt _ rfl with
    | inl hd => exact Or.inl (Deriv.ex hΓ.symm (List.Perm.refl _) (Deriv.negnegL hd))
    | inr hnd =>
        exact Or.inr fun hS => hnd (completeness (negnegL_inv
          (valid_of_perm hΓ.symm (List.Perm.refl _) hS.sound)))
  · -- negnegR (one premise)
    obtain ⟨φ, Δ₀, hΔ⟩ := d
    have hlt : Sequent.measure ⟨S.antecedent, φ :: Δ₀⟩ < n := by
      rw [← hmeas]; exact measure_negnegR hΔ
    cases ih _ hlt _ rfl with
    | inl hd => exact Or.inl (Deriv.ex (List.Perm.refl _) hΔ.symm (Deriv.negnegR hd))
    | inr hnd =>
        exact Or.inr fun hS => hnd (completeness (negnegR_inv
          (valid_of_perm (List.Perm.refl _) hΔ.symm hS.sound)))
  · -- negandL (two premises)
    obtain ⟨φ, ψ, Γ₀, hΓ⟩ := d
    have hltφ : Sequent.measure ⟨.neg φ :: Γ₀, S.succedent⟩ < n := by
      rw [← hmeas]; exact (measure_negandL hΓ).1
    have hltψ : Sequent.measure ⟨.neg ψ :: Γ₀, S.succedent⟩ < n := by
      rw [← hmeas]; exact (measure_negandL hΓ).2
    cases ih _ hltφ _ rfl with
    | inl hdφ =>
        cases ih _ hltψ _ rfl with
        | inl hdψ =>
            exact Or.inl (Deriv.ex hΓ.symm (List.Perm.refl _) (Deriv.negandL hdφ hdψ))
        | inr hndψ =>
            exact Or.inr fun hS => hndψ (completeness ((negandL_inv
              (valid_of_perm hΓ.symm (List.Perm.refl _) hS.sound)).2))
    | inr hndφ =>
        exact Or.inr fun hS => hndφ (completeness ((negandL_inv
          (valid_of_perm hΓ.symm (List.Perm.refl _) hS.sound)).1))
  · -- negandR (one premise)
    obtain ⟨φ, ψ, Δ₀, hΔ⟩ := d
    have hlt : Sequent.measure ⟨S.antecedent, .neg φ :: .neg ψ :: Δ₀⟩ < n := by
      rw [← hmeas]; exact measure_negandR hΔ
    cases ih _ hlt _ rfl with
    | inl hd => exact Or.inl (Deriv.ex (List.Perm.refl _) hΔ.symm (Deriv.negandR hd))
    | inr hnd =>
        exact Or.inr fun hS => hnd (completeness (negandR_inv
          (valid_of_perm (List.Perm.refl _) hΔ.symm hS.sound)))
  · -- negorL (one premise)
    obtain ⟨φ, ψ, Γ₀, hΓ⟩ := d
    have hlt : Sequent.measure ⟨.neg φ :: .neg ψ :: Γ₀, S.succedent⟩ < n := by
      rw [← hmeas]; exact measure_negorL hΓ
    cases ih _ hlt _ rfl with
    | inl hd => exact Or.inl (Deriv.ex hΓ.symm (List.Perm.refl _) (Deriv.negorL hd))
    | inr hnd =>
        exact Or.inr fun hS => hnd (completeness (negorL_inv
          (valid_of_perm hΓ.symm (List.Perm.refl _) hS.sound)))
  · -- negorR (two premises)
    obtain ⟨φ, ψ, Δ₀, hΔ⟩ := d
    have hltφ : Sequent.measure ⟨S.antecedent, .neg φ :: Δ₀⟩ < n := by
      rw [← hmeas]; exact (measure_negorR hΔ).1
    have hltψ : Sequent.measure ⟨S.antecedent, .neg ψ :: Δ₀⟩ < n := by
      rw [← hmeas]; exact (measure_negorR hΔ).2
    cases ih _ hltφ _ rfl with
    | inl hdφ =>
        cases ih _ hltψ _ rfl with
        | inl hdψ =>
            exact Or.inl (Deriv.ex (List.Perm.refl _) hΔ.symm (Deriv.negorR hdφ hdψ))
        | inr hndψ =>
            exact Or.inr fun hS => hndψ (completeness ((negorR_inv
              (valid_of_perm (List.Perm.refl _) hΔ.symm hS.sound)).2))
    | inr hndφ =>
        exact Or.inr fun hS => hndφ (completeness ((negorR_inv
          (valid_of_perm (List.Perm.refl _) hΔ.symm hS.sound)).1))

/-- **Derivability is decidable**: every sequent is either derivable or (refutably) not.
    This is the decision content promised by the calculus's terminating proof search. -/
theorem decidable_deriv (S : Sequent) : (⊢ₛ S) ∨ (¬ ⊢ₛ S) :=
  derivable_or_not S.measure S rfl

/-- A `Decidable` instance for derivability, recovered from `decidable_deriv` via
    `Classical` choice. **This is `noncomputable` and does not execute**: `Deriv` is
    `Prop`-valued, so `decide`/`if … then … else …` cannot reduce it (verified:
    `decide (⊢ₛ ⟨[.atom 0],[.atom 0]⟩)` fails with `dependsOnNoncomputable`). The
    `Classical.choice` is inherited from `completeness` (which the negative branches call),
    not introduced by this lift — the lift adds nothing to the axiom footprint. -/
noncomputable instance decidableDerivInst (S : Sequent) : Decidable (⊢ₛ S) :=
  Classical.choice <|
    match decidable_deriv S with
    | Or.inl h => ⟨isTrue h⟩
    | Or.inr h => ⟨isFalse h⟩

/-- Derivability and validity coincide: soundness and completeness as a single iff. Hence
    validity of sequents is decidable too (transport `decidable_deriv` across this). -/
theorem deriv_iff_valid {S : Sequent} : (⊢ₛ S) ↔ S.Valid :=
  ⟨Deriv.sound, completeness⟩

end FDE
