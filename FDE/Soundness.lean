import FDE.Sequent

/-!
# Soundness of the FDE sequent calculus

Every derivable sequent is valid: `⊢ₛ S → Sequent.Valid S`.

Proof by induction on the derivation. The key observations for the right-rules:

- `andR`: if `Γ ⇒ φ :: Δ` and `Γ ⇒ ψ :: Δ` are valid, then for a valuation designating all
  of `Γ`, either some `δ ∈ Δ` is designated (both branches give such a `δ` via the shared
  tail), or `φ` and `ψ` are both designated, hence `φ ∧ ψ` is designated.
- `orR` / the negation rules are analogous, using the De Morgan / double-negation lemmas.

The all/some-designated hypotheses are transported along list permutations via
`List.Perm.mem_iff`.
-/

namespace FDE

/-! ## Designated-value algebra lemmas -/

theorem designated_and (v : Valuation) (φ ψ : Formula) :
    (eval v (.and φ ψ)).designated = ((eval v φ).designated && (eval v ψ).designated) := by
  cases hφ : eval v φ <;> cases hψ : eval v ψ <;>
    simp [eval, Val4.and, Val4.designated, hφ, hψ]

theorem designated_or (v : Valuation) (φ ψ : Formula) :
    (eval v (.or φ ψ)).designated = ((eval v φ).designated || (eval v ψ).designated) := by
  cases hφ : eval v φ <;> cases hψ : eval v ψ <;>
    simp [eval, Val4.or, Val4.designated, hφ, hψ]

theorem designated_negneg (v : Valuation) (φ : Formula) :
    (eval v (.neg (.neg φ))).designated = (eval v φ).designated := by
  cases h : eval v φ <;> simp [eval, Val4.neg, Val4.designated, h]

theorem designated_neg_and (v : Valuation) (φ ψ : Formula) :
    (eval v (.neg (.and φ ψ))).designated =
      ((eval v (.neg φ)).designated || (eval v (.neg ψ)).designated) := by
  cases hφ : eval v φ <;> cases hψ : eval v ψ <;>
    simp [eval, Val4.and, Val4.or, Val4.neg, Val4.designated, hφ, hψ]

theorem designated_neg_or (v : Valuation) (φ ψ : Formula) :
    (eval v (.neg (.or φ ψ))).designated =
      ((eval v (.neg φ)).designated && (eval v (.neg ψ)).designated) := by
  cases hφ : eval v φ <;> cases hψ : eval v ψ <;>
    simp [eval, Val4.and, Val4.or, Val4.neg, Val4.designated, hφ, hψ]

theorem designated_neg_atom (v : Valuation) (p : ℕ) :
    (eval v (.neg (.atom p))).designated = (v p).neg.designated := by
  simp [eval]

/-! ## Transport along permutations -/

theorem all_designated_of_perm {Γ Γ' : List Formula} (h : List.Perm Γ Γ') (v : Valuation) :
    (∀ γ ∈ Γ', (eval v γ).designated) → ∀ γ ∈ Γ, (eval v γ).designated := by
  intro hΓ' γ hγ
  exact hΓ' γ ((List.Perm.mem_iff h).mp hγ)

theorem exists_designated_of_perm {Δ Δ' : List Formula} (h : List.Perm Δ Δ') (v : Valuation) :
    (∃ δ ∈ Δ, (eval v δ).designated) → ∃ δ ∈ Δ', (eval v δ).designated := by
  rintro ⟨δ, hδ, hv⟩
  exact ⟨δ, (List.Perm.mem_iff h).mp hδ, hv⟩

/-! ## Soundness -/

/-- Soundness: every derivable sequent is valid. -/
theorem Deriv.sound {S : Sequent} (h : ⊢ₛ S) : S.Valid := by
  induction h with
  | id Γ Δ p =>
      intro v hΓ
      exact ⟨.atom p, List.mem_cons_self, hΓ (.atom p) (List.mem_cons_self)⟩
  | idNeg Γ Δ p =>
      intro v hΓ
      exact ⟨.neg (.atom p), List.mem_cons_self, hΓ (.neg (.atom p)) (List.mem_cons_self)⟩
  | ex hΓ hΔ _ ih =>
      intro v hΓ'
      exact exists_designated_of_perm hΔ v (ih v (all_designated_of_perm hΓ v hΓ'))
  | andL _ ih =>
      intro v hΓ
      apply ih v
      intro γ hγ
      have hφψ := hΓ (.and _ _) (List.mem_cons_self)
      rw [designated_and] at hφψ
      simp only [Bool.and_eq_true] at hφψ
      rcases List.mem_cons.mp hγ with rfl | hγ'
      · exact hφψ.1
      · rcases List.mem_cons.mp hγ' with rfl | hγ''
        · exact hφψ.2
        · exact hΓ γ (List.mem_cons_of_mem _ hγ'')
  | andR _ _ ihφ ihψ =>
      intro v hΓ
      rcases ihφ v hΓ with ⟨δ, hδ, hvd⟩
      rcases ihψ v hΓ with ⟨δ', hδ', hvd'⟩
      rcases List.mem_cons.mp hδ with rfl | hδ
      · rcases List.mem_cons.mp hδ' with rfl | hδ'
        · exact ⟨.and _ _, List.mem_cons_self, by
            rw [designated_and]; simp [hvd, hvd']⟩
        · exact ⟨δ', List.mem_cons_of_mem _ hδ', hvd'⟩
      · exact ⟨δ, List.mem_cons_of_mem _ hδ, hvd⟩
  | orL _ _ ihφ ihψ =>
      intro v hΓ
      have hφψ := hΓ (.or _ _) (List.mem_cons_self)
      rw [designated_or] at hφψ
      simp only [Bool.or_eq_true] at hφψ
      rcases hφψ with hφ | hψ
      · exact ihφ v (fun γ hγ => by
          rcases List.mem_cons.mp hγ with rfl | hγ'
          · exact hφ
          · exact hΓ γ (List.mem_cons_of_mem _ hγ'))
      · exact ihψ v (fun γ hγ => by
          rcases List.mem_cons.mp hγ with rfl | hγ'
          · exact hψ
          · exact hΓ γ (List.mem_cons_of_mem _ hγ'))
  | orR _ ih =>
      intro v hΓ
      rcases ih v hΓ with ⟨δ, hδ, hvd⟩
      -- hδ : δ ∈ φ :: ψ :: Δ. We case on where δ is.
      rcases List.mem_cons.mp hδ with hδφ | hδtail
      · -- δ = φ: then φ is designated, so φ ∨ ψ is designated
        subst hδφ
        exact ⟨.or _ _, List.mem_cons_self, by rw [designated_or]; simp [hvd]⟩
      · rcases List.mem_cons.mp hδtail with hδψ | hδrest
        · subst hδψ
          exact ⟨.or _ _, List.mem_cons_self, by rw [designated_or]; simp [hvd]⟩
        · exact ⟨δ, List.mem_cons_of_mem _ hδrest, hvd⟩
  | negnegL _ ih =>
      intro v hΓ
      apply ih v
      intro γ hγ
      rcases List.mem_cons.mp hγ with rfl | hγ'
      · have h := hΓ (.neg (.neg _)) List.mem_cons_self
        rwa [designated_negneg] at h
      · exact hΓ γ (List.mem_cons_of_mem _ hγ')
  | negnegR _ ih =>
      intro v hΓ
      rcases ih v hΓ with ⟨δ, hδ, hvd⟩
      rcases List.mem_cons.mp hδ with rfl | hδ'
      · exact ⟨.neg (.neg _), List.mem_cons_self, by rwa [designated_negneg]⟩
      · exact ⟨δ, List.mem_cons_of_mem _ hδ', hvd⟩
  | negandL _ _ ihφ ihψ =>
      intro v hΓ
      have h := hΓ (.neg (.and _ _)) (List.mem_cons_self)
      rw [designated_neg_and] at h
      simp only [Bool.or_eq_true] at h
      rcases h with h | h
      · exact ihφ v (fun γ hγ => by
          rcases List.mem_cons.mp hγ with rfl | hγ'
          · exact h
          · exact hΓ γ (List.mem_cons_of_mem _ hγ'))
      · exact ihψ v (fun γ hγ => by
          rcases List.mem_cons.mp hγ with rfl | hγ'
          · exact h
          · exact hΓ γ (List.mem_cons_of_mem _ hγ'))
  | negandR _ ih =>
      intro v hΓ
      rcases ih v hΓ with ⟨δ, hδ, hvd⟩
      rcases List.mem_cons.mp hδ with hδφ | hδtail
      · subst hδφ
        exact ⟨.neg (.and _ _), List.mem_cons_self, by
          rw [designated_neg_and]; simp [hvd]⟩
      · rcases List.mem_cons.mp hδtail with hδψ | hδrest
        · subst hδψ
          exact ⟨.neg (.and _ _), List.mem_cons_self, by
            rw [designated_neg_and]; simp [hvd]⟩
        · exact ⟨δ, List.mem_cons_of_mem _ hδrest, hvd⟩
  | negorL _ ih =>
      intro v hΓ
      apply ih v
      intro γ hγ
      have h := hΓ (.neg (.or _ _)) (List.mem_cons_self)
      rw [designated_neg_or] at h
      simp only [Bool.and_eq_true] at h
      rcases List.mem_cons.mp hγ with rfl | hγ'
      · exact h.1
      · rcases List.mem_cons.mp hγ' with rfl | hγ''
        · exact h.2
        · exact hΓ γ (List.mem_cons_of_mem _ hγ'')
  | negorR _ _ ihφ ihψ =>
      intro v hΓ
      rcases ihφ v hΓ with ⟨δ, hδ, hvd⟩
      rcases ihψ v hΓ with ⟨δ', hδ', hvd'⟩
      rcases List.mem_cons.mp hδ with hδφ | hδrest
      · subst hδφ
        rcases List.mem_cons.mp hδ' with hδ'ψ | hδ'rest
        · subst hδ'ψ
          exact ⟨.neg (.or _ _), List.mem_cons_self, by
            rw [designated_neg_or]; simp [hvd, hvd']⟩
        · exact ⟨δ', List.mem_cons_of_mem _ hδ'rest, hvd'⟩
      · exact ⟨δ, List.mem_cons_of_mem _ hδrest, hvd⟩

/-- Soundness for a single formula: a derivable `⇒ φ` is designated under every valuation. -/
theorem sound_formula {φ : Formula} (h : ⊢ₛ ⟨[], [φ]⟩) : ∀ v, (eval v φ).designated := by
  intro v
  rcases h.sound v (fun γ hγ => by cases hγ) with ⟨δ, hδ, hvd⟩
  rcases List.mem_singleton.mp hδ with rfl
  exact hvd

end FDE
