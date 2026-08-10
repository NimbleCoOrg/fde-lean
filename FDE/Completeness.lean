import FDE.Soundness

/-!
# Completeness of the FDE sequent calculus

Every valid sequent is derivable: `Sequent.Valid S → ⊢ₛ S`.

## Strategy

The calculus is *invertible*: every rule's conclusion is valid iff all its premises are.
We exploit this via **proof search**. Define, by well-founded recursion on a measure that
decreases at each step, a search procedure that either derives the sequent or bottoms out at
a **saturated** sequent — one to which no logical rule applies and which is not an initial
sequent. From a saturated sequent we read off a **refuting valuation**: send atom `p` to
- `b` if `atom p` is on both sides,
- `t` if only on the left,
- `f` if only on the right,
- `n` if on neither.

Saturation guarantees this valuation designates every antecedent formula and no succedent
formula — contradicting validity. Hence a valid sequent cannot be saturated, so search
derives it.

## Status

The two hard lemmas are (1) termination of the search and (2) the saturation→refuting-valuation
construction. Both are proved here, along with the supporting inversion lemmas (each rule is
valid backwards). `completeness` is discharged at the end of this file (strong induction on
the negation-weighted measure over the 12-way `decompose` disjunction); the module builds
with zero sorries. See `FDE.Soundness` for the other direction.
-/

namespace FDE

/-! ## Inversion lemmas: each rule is valid backwards (premise valid → conclusion valid) -/

/-- Backward `andL`: if `φ ∧ ψ, Γ ⇒ Δ` is valid then `φ, ψ, Γ ⇒ Δ` is valid. -/
theorem andL_inv {Γ Δ φ ψ} (h : Sequent.Valid ⟨.and φ ψ :: Γ, Δ⟩) :
    Sequent.Valid ⟨φ :: ψ :: Γ, Δ⟩ := by
  intro v hv
  apply h v
  intro γ hγ
  have hφ : (eval v φ).designated := hv φ (by simp)
  have hψ : (eval v ψ).designated := hv ψ (by simp)
  rcases List.mem_cons.mp hγ with rfl | hγ'
  · rw [designated_and]; simp [hφ, hψ]
  · exact hv γ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hγ'))

/-- Backward `orR`: if `Γ ⇒ Δ, φ ∨ ψ` valid then `Γ ⇒ Δ, φ, ψ` valid. -/
theorem orR_inv {Γ Δ φ ψ} (h : Sequent.Valid ⟨Γ, .or φ ψ :: Δ⟩) :
    Sequent.Valid ⟨Γ, φ :: ψ :: Δ⟩ := by
  intro v hv
  rcases h v hv with ⟨δ, hδ, hvd⟩
  rcases List.mem_cons.mp hδ with rfl | hδ'
  · rw [designated_or] at hvd
    simp only [Bool.or_eq_true] at hvd
    rcases hvd with h | h
    · exact ⟨φ, by simp, h⟩
    · exact ⟨ψ, by simp, h⟩
  · exact ⟨δ, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hδ'), hvd⟩

/-- Backward `andR`: valid conclusion implies both valid premises. -/
theorem andR_inv {Γ Δ φ ψ} (h : Sequent.Valid ⟨Γ, .and φ ψ :: Δ⟩) :
    Sequent.Valid ⟨Γ, φ :: Δ⟩ ∧ Sequent.Valid ⟨Γ, ψ :: Δ⟩ := by
  constructor
  · intro v hv
    rcases h v hv with ⟨δ, hδ, hvd⟩
    rcases List.mem_cons.mp hδ with rfl | hδ'
    · rw [designated_and] at hvd
      simp only [Bool.and_eq_true] at hvd
      exact ⟨φ, by simp, hvd.1⟩
    · exact ⟨δ, List.mem_cons_of_mem _ hδ', hvd⟩
  · intro v hv
    rcases h v hv with ⟨δ, hδ, hvd⟩
    rcases List.mem_cons.mp hδ with rfl | hδ'
    · rw [designated_and] at hvd
      simp only [Bool.and_eq_true] at hvd
      exact ⟨ψ, by simp, hvd.2⟩
    · exact ⟨δ, List.mem_cons_of_mem _ hδ', hvd⟩

/-- Backward `orL`. -/
theorem orL_inv {Γ Δ φ ψ} (h : Sequent.Valid ⟨.or φ ψ :: Γ, Δ⟩) :
    Sequent.Valid ⟨φ :: Γ, Δ⟩ ∧ Sequent.Valid ⟨ψ :: Γ, Δ⟩ := by
  constructor
  · intro v hv
    apply h v
    intro γ hγ
    rcases List.mem_cons.mp hγ with rfl | hγ'
    · rw [designated_or]; simp [hv φ (by simp)]
    · exact hv γ (List.mem_cons_of_mem _ hγ')
  · intro v hv
    apply h v
    intro γ hγ
    rcases List.mem_cons.mp hγ with rfl | hγ'
    · rw [designated_or]; simp [hv ψ (by simp)]
    · exact hv γ (List.mem_cons_of_mem _ hγ')

/-- Backward `negnegL`. -/
theorem negnegL_inv {Γ Δ φ} (h : Sequent.Valid ⟨.neg (.neg φ) :: Γ, Δ⟩) :
    Sequent.Valid ⟨φ :: Γ, Δ⟩ := by
  intro v hv
  apply h v
  intro γ hγ
  rcases List.mem_cons.mp hγ with rfl | hγ'
  · rw [designated_negneg]; exact hv φ (by simp)
  · exact hv γ (List.mem_cons_of_mem _ hγ')

/-- Backward `negnegR`. -/
theorem negnegR_inv {Γ Δ φ} (h : Sequent.Valid ⟨Γ, .neg (.neg φ) :: Δ⟩) :
    Sequent.Valid ⟨Γ, φ :: Δ⟩ := by
  intro v hv
  rcases h v hv with ⟨δ, hδ, hvd⟩
  rcases List.mem_cons.mp hδ with rfl | hδ'
  · rw [designated_negneg] at hvd
    exact ⟨φ, by simp, hvd⟩
  · exact ⟨δ, List.mem_cons_of_mem _ hδ', hvd⟩

/-- Backward `negandL`. -/
theorem negandL_inv {Γ Δ φ ψ} (h : Sequent.Valid ⟨.neg (.and φ ψ) :: Γ, Δ⟩) :
    Sequent.Valid ⟨.neg φ :: Γ, Δ⟩ ∧ Sequent.Valid ⟨.neg ψ :: Γ, Δ⟩ := by
  constructor
  · intro v hv
    apply h v
    intro γ hγ
    have hφ : (eval v (.neg φ)).designated := hv (.neg φ) (by simp)
    rcases List.mem_cons.mp hγ with rfl | hγ'
    · rw [designated_neg_and]; simp [hφ]
    · exact hv γ (List.mem_cons_of_mem _ hγ')
  · intro v hv
    apply h v
    intro γ hγ
    have hψ : (eval v (.neg ψ)).designated := hv (.neg ψ) (by simp)
    rcases List.mem_cons.mp hγ with rfl | hγ'
    · rw [designated_neg_and]; simp [hψ]
    · exact hv γ (List.mem_cons_of_mem _ hγ')

/-- Backward `negandR`. -/
theorem negandR_inv {Γ Δ φ ψ} (h : Sequent.Valid ⟨Γ, .neg (.and φ ψ) :: Δ⟩) :
    Sequent.Valid ⟨Γ, .neg φ :: .neg ψ :: Δ⟩ := by
  intro v hv
  rcases h v hv with ⟨δ, hδ, hvd⟩
  rcases List.mem_cons.mp hδ with rfl | hδ'
  · rw [designated_neg_and] at hvd
    simp only [Bool.or_eq_true] at hvd
    rcases hvd with h | h
    · exact ⟨.neg φ, by simp, h⟩
    · exact ⟨.neg ψ, by simp, h⟩
  · exact ⟨δ, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hδ'), hvd⟩

/-- Backward `negorL`. -/
theorem negorL_inv {Γ Δ φ ψ} (h : Sequent.Valid ⟨.neg (.or φ ψ) :: Γ, Δ⟩) :
    Sequent.Valid ⟨.neg φ :: .neg ψ :: Γ, Δ⟩ := by
  intro v hv
  apply h v
  intro γ hγ
  have hφ : (eval v (.neg φ)).designated := hv (.neg φ) (by simp)
  have hψ : (eval v (.neg ψ)).designated := hv (.neg ψ) (by simp)
  -- hγ : γ ∈ ¬(φ ∨ ψ) :: Γ
  rcases List.mem_cons.mp hγ with rfl | hγ'
  · rw [designated_neg_or]; simp [hφ, hψ]
  · -- γ ∈ Γ, and hv expects membership in ¬φ :: ¬ψ :: Γ
    exact hv γ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hγ'))

/-- Backward `negorR`. -/
theorem negorR_inv {Γ Δ φ ψ} (h : Sequent.Valid ⟨Γ, .neg (.or φ ψ) :: Δ⟩) :
    Sequent.Valid ⟨Γ, .neg φ :: Δ⟩ ∧ Sequent.Valid ⟨Γ, .neg ψ :: Δ⟩ := by
  constructor
  · intro v hv
    rcases h v hv with ⟨δ, hδ, hvd⟩
    rcases List.mem_cons.mp hδ with rfl | hδ'
    · rw [designated_neg_or] at hvd
      simp only [Bool.and_eq_true] at hvd
      exact ⟨.neg φ, by simp, hvd.1⟩
    · exact ⟨δ, List.mem_cons_of_mem _ hδ', hvd⟩
  · intro v hv
    rcases h v hv with ⟨δ, hδ, hvd⟩
    rcases List.mem_cons.mp hδ with rfl | hδ'
    · rw [designated_neg_or] at hvd
      simp only [Bool.and_eq_true] at hvd
      exact ⟨.neg ψ, by simp, hvd.2⟩
    · exact ⟨δ, List.mem_cons_of_mem _ hδ', hvd⟩

/-! ## The refuting valuation -/

/-- Read a valuation off a *saturated* sequent: the standard FDE canonical model.
    Both support bits are read from the **antecedent**: truth-support of `p` := `atom p` ∈ Γ;
    falsity-support := `¬(atom p)` ∈ Γ. Mapping (ts,fs) ↦ value: (T,T)=b, (T,F)=t, (F,T)=f,
    (F,F)=n.
    Ground truth (verified by `#eval`): antecedent `atom p` designated ⟺ ts (t/b) ✓;
    antecedent `¬p` designated ⟺ fs (neg b = b, neg f = t) ✓. Reading falsity from the
    *succedent* instead is mathematically wrong: a saturated `{p, ¬p} ⇒ {}` would map `p`
    to `t`, leaving antecedent `¬p` undesignated. With falsity from the antecedent,
    saturation refutes the succedent: succedent `p` forces ts=F (hpos) → value n/f ✓;
    succedent `¬p` forces fs=F (hneg) → value t/n, and neg t = f, neg n = n ✓. -/
def Sequent.refutingVal (S : Sequent) : Valuation :=
  fun p =>
    let ts := S.antecedent.contains (.atom p)
    let fs := S.antecedent.contains (.neg (.atom p))
    match ts, fs with
    | true, true => .b
    | true, false => .t
    | false, true => .f
    | false, false => .n

/-- A literal is an atom or a negated atom. -/
def Formula.isLiteral : Formula → Prop
  | .atom _ => True
  | .neg (.atom _) => True
  | _ => False

/-- A sequent is *saturated* if it consists only of literals and contains no *complementary
    pair* that would make it an initial (valid-by-identity) sequent. The forbidden pairs are
    those that force some formula to be designated on both sides under every valuation:
    `p` left + `p` right; `¬p` left + `¬p` right; `p` left + `¬p` left is allowed (b);
    the cross pairs `p` left + `¬p` right and `¬p` left + `p` right are also allowed
    (they correspond to `t`/`f`, which don't designate the succedent from the antecedent). -/
def Sequent.Saturated (S : Sequent) : Prop :=
  (∀ φ ∈ S.antecedent, φ.isLiteral) ∧ (∀ δ ∈ S.succedent, δ.isLiteral) ∧
    (∀ p, ¬ ((.atom p) ∈ S.antecedent ∧ (.atom p) ∈ S.succedent)) ∧
    (∀ p, ¬ ((.neg (.atom p)) ∈ S.antecedent ∧ (.neg (.atom p)) ∈ S.succedent))

/-- A saturated sequent is refuted by its associated valuation: every antecedent formula is
    designated, no succedent formula is. Each direction is a 4-way case split on the
    (ts,fs) bits of the relevant atom; with the antecedent-only valuation every branch
    closes by computation plus the complementary-pair hypotheses. -/
theorem Saturated.refutes {S : Sequent} (h : S.Saturated) :
    (∀ γ ∈ S.antecedent, (eval (S.refutingVal) γ).designated) ∧
    (∀ δ ∈ S.succedent, ¬ (eval (S.refutingVal) δ).designated) := by
  obtain ⟨hlitL, hlitR, hpos, hneg⟩ := h
  refine ⟨?_, ?_⟩
  · -- antecedent literals are designated
    intro γ hγ
    have hlit := hlitL γ hγ
    cases γ with
    | atom p =>
        have hts : S.antecedent.contains (.atom p) = true :=
          List.contains_iff_mem.mpr hγ
        cases hfs : S.antecedent.contains (.neg (.atom p)) <;>
          simp only [eval, Sequent.refutingVal, hts, hfs, Val4.designated]
    | neg φ =>
        cases φ with
        | atom p =>
            have hfs : S.antecedent.contains (.neg (.atom p)) = true :=
              List.contains_iff_mem.mpr hγ
            cases hts : S.antecedent.contains (.atom p) <;>
              simp only [eval, Sequent.refutingVal, hts, hfs, Val4.neg, Val4.designated]
        | neg _ => simp [Formula.isLiteral] at hlit
        | and _ _ => simp [Formula.isLiteral] at hlit
        | or _ _ => simp [Formula.isLiteral] at hlit
    | and _ _ => simp [Formula.isLiteral] at hlit
    | or _ _ => simp [Formula.isLiteral] at hlit
  · -- succedent literals are NOT designated
    intro δ hδ hdes
    have hlit := hlitR δ hδ
    cases δ with
    | atom p =>
        have htsF : S.antecedent.contains (.atom p) = false := by
          cases hc : S.antecedent.contains (.atom p)
          · rfl
          · exact absurd ⟨List.contains_iff_mem.mp hc, hδ⟩ (hpos p)
        cases hfs : S.antecedent.contains (.neg (.atom p)) <;>
          simp only [eval, Sequent.refutingVal, htsF, hfs, Val4.designated] at hdes <;>
          contradiction
    | neg φ =>
        cases φ with
        | atom p =>
            have hfsF : S.antecedent.contains (.neg (.atom p)) = false := by
              cases hc : S.antecedent.contains (.neg (.atom p))
              · rfl
              · exact absurd ⟨List.contains_iff_mem.mp hc, hδ⟩ (hneg p)
            cases hts : S.antecedent.contains (.atom p) <;>
              simp only [eval, Sequent.refutingVal, hts, hfsF, Val4.neg, Val4.designated]
                at hdes <;>
              contradiction
        | neg _ => simp [Formula.isLiteral] at hlit
        | and _ _ => simp [Formula.isLiteral] at hlit
        | or _ _ => simp [Formula.isLiteral] at hlit
    | and _ _ => simp [Formula.isLiteral] at hlit
    | or _ _ => simp [Formula.isLiteral] at hlit

/-! ## Proof search infrastructure -/

/-- Total connectives in a formula, with negation weighted double. The weighting is what
    makes the De Morgan rules (`¬(φ∧ψ) → ¬φ, ¬ψ` etc.) *strictly* decrease the measure:
    raw connective count is preserved by De Morgan (1 neg + 1 and = 2 = 2 negs), so plain
    connective count does not terminate proof search. Weighted: `deg(¬(φ∧ψ)) = 1+2(1+φ+ψ)`
    vs premises `deg(¬φ)+deg(¬ψ) = (1+2φ)+(1+2ψ)` — decreases by 1. Double negation:
    `deg(¬¬φ) = 1+2(1+2φ) = 3+4φ > φ` ✓. All other rules already decrease under any
    positive weighting. -/
def Formula.degree : Formula → ℕ
  | .atom _ => 0
  | .neg φ => 1 + 2 * φ.degree
  | .and φ ψ => 1 + φ.degree + ψ.degree
  | .or φ ψ => 1 + φ.degree + ψ.degree

/-- Total connectives in a formula list. -/
def listDegree : List Formula → ℕ
  | [] => 0
  | φ :: Γ => φ.degree + listDegree Γ

/-- Sequent measure: total connectives on both sides. Every rule of the calculus strictly
    decreases this measure on each premise, so proof search terminates. -/
def Sequent.measure (S : Sequent) : ℕ := listDegree S.antecedent + listDegree S.succedent

/-- Root selection (succedent): any member can be moved to the head up to permutation. -/
theorem right_perm_of_mem {Δ : List Formula} {δ} (h : δ ∈ Δ) :
    ∃ Δ', List.Perm Δ (δ :: Δ') := by
  obtain ⟨l1, l2, rfl⟩ := List.append_of_mem h
  exact ⟨l1 ++ l2,
    List.Perm.trans List.perm_append_comm (List.Perm.cons δ List.perm_append_comm)⟩

/-- Root selection (antecedent). -/
theorem left_perm_of_mem {Γ : List Formula} {γ} (h : γ ∈ Γ) :
    ∃ Γ', List.Perm Γ (γ :: Γ') := right_perm_of_mem h

/-- The measure is permutation-invariant. -/
theorem listDegree_perm {Γ Γ' : List Formula} (h : List.Perm Γ Γ') :
    listDegree Γ = listDegree Γ' := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [listDegree, ih]
  | swap x y l => simp [listDegree, Nat.add_assoc, Nat.add_left_comm]
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

theorem measure_perm {Γ Γ' Δ Δ' : List Formula} (hΓ : List.Perm Γ Γ') (hΔ : List.Perm Δ Δ') :
    Sequent.measure ⟨Γ, Δ⟩ = Sequent.measure ⟨Γ', Δ'⟩ := by
  simp only [Sequent.measure, listDegree_perm hΓ, listDegree_perm hΔ]

/-! ### Per-rule measure decrease

Each is stated for a sequent already in root form (`Γ ~ root :: Γ₀`), matching how
`search` will use them after `left/right_perm_of_mem`. -/

theorem measure_andL {Γ Δ Γ₀} {φ ψ} (hΓ : List.Perm Γ (.and φ ψ :: Γ₀)) :
    Sequent.measure ⟨φ :: ψ :: Γ₀, Δ⟩ < Sequent.measure ⟨Γ, Δ⟩ := by
  rw [Sequent.measure, Sequent.measure, listDegree_perm hΓ]
  simp only [listDegree, Formula.degree]
  omega

theorem measure_andR {Γ Δ Δ₀} {φ ψ} (hΔ : List.Perm Δ (.and φ ψ :: Δ₀)) :
    Sequent.measure ⟨Γ, φ :: Δ₀⟩ < Sequent.measure ⟨Γ, Δ⟩ ∧
    Sequent.measure ⟨Γ, ψ :: Δ₀⟩ < Sequent.measure ⟨Γ, Δ⟩ := by
  rw [Sequent.measure, Sequent.measure, Sequent.measure, listDegree_perm hΔ]
  simp only [listDegree, Formula.degree]
  constructor <;> omega

theorem measure_orL {Γ Δ Γ₀} {φ ψ} (hΓ : List.Perm Γ (.or φ ψ :: Γ₀)) :
    Sequent.measure ⟨φ :: Γ₀, Δ⟩ < Sequent.measure ⟨Γ, Δ⟩ ∧
    Sequent.measure ⟨ψ :: Γ₀, Δ⟩ < Sequent.measure ⟨Γ, Δ⟩ := by
  rw [Sequent.measure, Sequent.measure, Sequent.measure, listDegree_perm hΓ]
  simp only [listDegree, Formula.degree]
  constructor <;> omega

theorem measure_orR {Γ Δ Δ₀} {φ ψ} (hΔ : List.Perm Δ (.or φ ψ :: Δ₀)) :
    Sequent.measure ⟨Γ, φ :: ψ :: Δ₀⟩ < Sequent.measure ⟨Γ, Δ⟩ := by
  rw [Sequent.measure, Sequent.measure, listDegree_perm hΔ]
  simp only [listDegree, Formula.degree]
  omega

theorem measure_negnegL {Γ Δ Γ₀} {φ} (hΓ : List.Perm Γ (.neg (.neg φ) :: Γ₀)) :
    Sequent.measure ⟨φ :: Γ₀, Δ⟩ < Sequent.measure ⟨Γ, Δ⟩ := by
  rw [Sequent.measure, Sequent.measure, listDegree_perm hΓ]
  simp only [listDegree, Formula.degree]
  omega

theorem measure_negnegR {Γ Δ Δ₀} {φ} (hΔ : List.Perm Δ (.neg (.neg φ) :: Δ₀)) :
    Sequent.measure ⟨Γ, φ :: Δ₀⟩ < Sequent.measure ⟨Γ, Δ⟩ := by
  rw [Sequent.measure, Sequent.measure, listDegree_perm hΔ]
  simp only [listDegree, Formula.degree]
  omega

theorem measure_negandL {Γ Δ Γ₀} {φ ψ} (hΓ : List.Perm Γ (.neg (.and φ ψ) :: Γ₀)) :
    Sequent.measure ⟨.neg φ :: Γ₀, Δ⟩ < Sequent.measure ⟨Γ, Δ⟩ ∧
    Sequent.measure ⟨.neg ψ :: Γ₀, Δ⟩ < Sequent.measure ⟨Γ, Δ⟩ := by
  rw [Sequent.measure, Sequent.measure, Sequent.measure, listDegree_perm hΓ]
  simp only [listDegree, Formula.degree]
  constructor <;> omega

theorem measure_negandR {Γ Δ Δ₀} {φ ψ} (hΔ : List.Perm Δ (.neg (.and φ ψ) :: Δ₀)) :
    Sequent.measure ⟨Γ, .neg φ :: .neg ψ :: Δ₀⟩ < Sequent.measure ⟨Γ, Δ⟩ := by
  rw [Sequent.measure, Sequent.measure, listDegree_perm hΔ]
  simp only [listDegree, Formula.degree]
  omega

theorem measure_negorL {Γ Δ Γ₀} {φ ψ} (hΓ : List.Perm Γ (.neg (.or φ ψ) :: Γ₀)) :
    Sequent.measure ⟨.neg φ :: .neg ψ :: Γ₀, Δ⟩ < Sequent.measure ⟨Γ, Δ⟩ := by
  rw [Sequent.measure, Sequent.measure, listDegree_perm hΓ]
  simp only [listDegree, Formula.degree]
  omega

theorem measure_negorR {Γ Δ Δ₀} {φ ψ} (hΔ : List.Perm Δ (.neg (.or φ ψ) :: Δ₀)) :
    Sequent.measure ⟨Γ, .neg φ :: Δ₀⟩ < Sequent.measure ⟨Γ, Δ⟩ ∧
    Sequent.measure ⟨Γ, .neg ψ :: Δ₀⟩ < Sequent.measure ⟨Γ, Δ⟩ := by
  rw [Sequent.measure, Sequent.measure, Sequent.measure, listDegree_perm hΔ]
  simp only [listDegree, Formula.degree]
  constructor <;> omega

/-- Proof-search decision step: every sequent is either derivable (an initial sequent up
    to permutation), saturated (hence refuted by `Saturated.refutes`), or has a compound
    formula at some position that can be moved to the head up to permutation, exposing the
    rule instance to apply. The twelve-way disjunction enumerates every rule-applicable
    shape on each side; the caller (`completeness`) recurses on the premises, whose measure
    strictly decreases by the `measure_*` lemmas above. -/
theorem decompose (S : Sequent) :
    (⊢ₛ S) ∨ S.Saturated ∨
    (∃ φ ψ Γ₀, List.Perm S.antecedent (.and φ ψ :: Γ₀)) ∨
    (∃ φ ψ Δ₀, List.Perm S.succedent (.and φ ψ :: Δ₀)) ∨
    (∃ φ ψ Γ₀, List.Perm S.antecedent (.or φ ψ :: Γ₀)) ∨
    (∃ φ ψ Δ₀, List.Perm S.succedent (.or φ ψ :: Δ₀)) ∨
    (∃ φ Γ₀, List.Perm S.antecedent (.neg (.neg φ) :: Γ₀)) ∨
    (∃ φ Δ₀, List.Perm S.succedent (.neg (.neg φ) :: Δ₀)) ∨
    (∃ φ ψ Γ₀, List.Perm S.antecedent (.neg (.and φ ψ) :: Γ₀)) ∨
    (∃ φ ψ Δ₀, List.Perm S.succedent (.neg (.and φ ψ) :: Δ₀)) ∨
    (∃ φ ψ Γ₀, List.Perm S.antecedent (.neg (.or φ ψ) :: Γ₀)) ∨
    (∃ φ ψ Δ₀, List.Perm S.succedent (.neg (.or φ ψ) :: Δ₀)) := by
  by_cases hL : ∀ γ ∈ S.antecedent, γ.isLiteral
  · by_cases hR : ∀ δ ∈ S.succedent, δ.isLiteral
    · -- All literals on both sides: either an identity pair or saturated.
      by_cases hid : ∃ p, (.atom p) ∈ S.antecedent ∧ (.atom p) ∈ S.succedent
      · obtain ⟨p, hpL, hpR⟩ := hid
        obtain ⟨Γ₀, hΓ⟩ := left_perm_of_mem hpL
        obtain ⟨Δ₀, hΔ⟩ := right_perm_of_mem hpR
        exact Or.inl (Deriv.ex hΓ.symm hΔ.symm (Deriv.id Γ₀ Δ₀ p))
      · by_cases hidn : ∃ p, (.neg (.atom p)) ∈ S.antecedent ∧ (.neg (.atom p)) ∈ S.succedent
        · obtain ⟨p, hpL, hpR⟩ := hidn
          obtain ⟨Γ₀, hΓ⟩ := left_perm_of_mem hpL
          obtain ⟨Δ₀, hΔ⟩ := right_perm_of_mem hpR
          exact Or.inl (Deriv.ex hΓ.symm hΔ.symm (Deriv.idNeg Γ₀ Δ₀ p))
        · exact Or.inr (Or.inl ⟨hL, hR, fun p hp => hid ⟨p, hp⟩, fun p hp => hidn ⟨p, hp⟩⟩)
    · -- Some succedent formula is not a literal.
      push_neg at hR
      obtain ⟨δ, hδ, hnotlit⟩ := hR
      obtain ⟨Δ₀, hΔ₀⟩ := right_perm_of_mem hδ
      cases δ with
      | atom p => simp [Formula.isLiteral] at hnotlit
      | neg φ =>
          cases φ with
          | atom p => simp [Formula.isLiteral] at hnotlit
          | neg ψ =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ψ, Δ₀, hΔ₀⟩)))))))
          | and ψ χ =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ψ, χ, Δ₀, hΔ₀⟩)))))))))
          | or ψ χ =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ψ, χ, Δ₀, hΔ₀⟩))))))))))
      | and φ ψ =>
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨φ, ψ, Δ₀, hΔ₀⟩)))
      | or φ ψ =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨φ, ψ, Δ₀, hΔ₀⟩)))))
  · -- Some antecedent formula is not a literal.
    push_neg at hL
    obtain ⟨γ, hγ, hnotlit⟩ := hL
    obtain ⟨Γ₀, hΓ₀⟩ := left_perm_of_mem hγ
    cases γ with
    | atom p => simp [Formula.isLiteral] at hnotlit
    | neg φ =>
        cases φ with
        | atom p => simp [Formula.isLiteral] at hnotlit
        | neg ψ =>
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ψ, Γ₀, hΓ₀⟩))))))
        | and ψ χ =>
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ψ, χ, Γ₀, hΓ₀⟩))))))))
        | or ψ χ =>
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ψ, χ, Γ₀, hΓ₀⟩))))))))))
    | and φ ψ =>
        exact Or.inr (Or.inr (Or.inl ⟨φ, ψ, Γ₀, hΓ₀⟩))
    | or φ ψ =>
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨φ, ψ, Γ₀, hΓ₀⟩))))

/-- Validity transports across permutation of either side (glue for `ex` + inversion). -/
theorem valid_of_perm {Γ Γ' Δ Δ' : List Formula}
    (hΓ : List.Perm Γ Γ') (hΔ : List.Perm Δ Δ')
    (h : Sequent.Valid ⟨Γ', Δ'⟩) : Sequent.Valid ⟨Γ, Δ⟩ := by
  intro v hv
  exact exists_designated_of_perm hΔ.symm v (h v (all_designated_of_perm hΓ.symm v hv))

/-- **Completeness**, packaged by measure for strong induction. Every valid sequent whose
    measure is `n` is derivable. -/
theorem completeness_aux : ∀ (n : ℕ) (S : Sequent), S.measure = n → S.Valid → ⊢ₛ S := by
  intro n
  induction' n using Nat.strong_induction_on with n ih
  intro S hmeas h
  obtain d | d | d | d | d | d | d | d | d | d | d | d := decompose S
  · exact d
  · -- saturated contradicts validity
    exfalso
    obtain ⟨hLdes, hRdes⟩ := Saturated.refutes d
    obtain ⟨δ, hδ, hδdes⟩ := h S.refutingVal hLdes
    exact hRdes δ hδ hδdes
  · -- andL
    obtain ⟨φ, ψ, Γ₀, hΓ⟩ := d
    have hv : Sequent.Valid ⟨.and φ ψ :: Γ₀, S.succedent⟩ :=
      valid_of_perm hΓ.symm (List.Perm.refl _) h
    have hlt : Sequent.measure ⟨φ :: ψ :: Γ₀, S.succedent⟩ < n := by
      rw [← hmeas]; exact measure_andL hΓ
    exact Deriv.ex hΓ.symm (List.Perm.refl _)
      (Deriv.andL (ih _ hlt _ rfl (andL_inv hv)))
  · -- andR
    obtain ⟨φ, ψ, Δ₀, hΔ⟩ := d
    have hv : Sequent.Valid ⟨S.antecedent, .and φ ψ :: Δ₀⟩ :=
      valid_of_perm (List.Perm.refl _) hΔ.symm h
    obtain ⟨hvφ, hvψ⟩ := andR_inv hv
    have hltφ : Sequent.measure ⟨S.antecedent, φ :: Δ₀⟩ < n := by
      rw [← hmeas]; exact (measure_andR hΔ).1
    have hltψ : Sequent.measure ⟨S.antecedent, ψ :: Δ₀⟩ < n := by
      rw [← hmeas]; exact (measure_andR hΔ).2
    exact Deriv.ex (List.Perm.refl _) hΔ.symm
      (Deriv.andR (ih _ hltφ _ rfl hvφ) (ih _ hltψ _ rfl hvψ))
  · -- orL
    obtain ⟨φ, ψ, Γ₀, hΓ⟩ := d
    have hv : Sequent.Valid ⟨.or φ ψ :: Γ₀, S.succedent⟩ :=
      valid_of_perm hΓ.symm (List.Perm.refl _) h
    obtain ⟨hvφ, hvψ⟩ := orL_inv hv
    have hltφ : Sequent.measure ⟨φ :: Γ₀, S.succedent⟩ < n := by
      rw [← hmeas]; exact (measure_orL hΓ).1
    have hltψ : Sequent.measure ⟨ψ :: Γ₀, S.succedent⟩ < n := by
      rw [← hmeas]; exact (measure_orL hΓ).2
    exact Deriv.ex hΓ.symm (List.Perm.refl _)
      (Deriv.orL (ih _ hltφ _ rfl hvφ) (ih _ hltψ _ rfl hvψ))
  · -- orR
    obtain ⟨φ, ψ, Δ₀, hΔ⟩ := d
    have hv : Sequent.Valid ⟨S.antecedent, .or φ ψ :: Δ₀⟩ :=
      valid_of_perm (List.Perm.refl _) hΔ.symm h
    have hlt : Sequent.measure ⟨S.antecedent, φ :: ψ :: Δ₀⟩ < n := by
      rw [← hmeas]; exact measure_orR hΔ
    exact Deriv.ex (List.Perm.refl _) hΔ.symm
      (Deriv.orR (ih _ hlt _ rfl (orR_inv hv)))
  · -- negnegL
    obtain ⟨φ, Γ₀, hΓ⟩ := d
    have hv : Sequent.Valid ⟨.neg (.neg φ) :: Γ₀, S.succedent⟩ :=
      valid_of_perm hΓ.symm (List.Perm.refl _) h
    have hlt : Sequent.measure ⟨φ :: Γ₀, S.succedent⟩ < n := by
      rw [← hmeas]; exact measure_negnegL hΓ
    exact Deriv.ex hΓ.symm (List.Perm.refl _)
      (Deriv.negnegL (ih _ hlt _ rfl (negnegL_inv hv)))
  · -- negnegR
    obtain ⟨φ, Δ₀, hΔ⟩ := d
    have hv : Sequent.Valid ⟨S.antecedent, .neg (.neg φ) :: Δ₀⟩ :=
      valid_of_perm (List.Perm.refl _) hΔ.symm h
    have hlt : Sequent.measure ⟨S.antecedent, φ :: Δ₀⟩ < n := by
      rw [← hmeas]; exact measure_negnegR hΔ
    exact Deriv.ex (List.Perm.refl _) hΔ.symm
      (Deriv.negnegR (ih _ hlt _ rfl (negnegR_inv hv)))
  · -- negandL
    obtain ⟨φ, ψ, Γ₀, hΓ⟩ := d
    have hv : Sequent.Valid ⟨.neg (.and φ ψ) :: Γ₀, S.succedent⟩ :=
      valid_of_perm hΓ.symm (List.Perm.refl _) h
    obtain ⟨hvφ, hvψ⟩ := negandL_inv hv
    have hltφ : Sequent.measure ⟨.neg φ :: Γ₀, S.succedent⟩ < n := by
      rw [← hmeas]; exact (measure_negandL hΓ).1
    have hltψ : Sequent.measure ⟨.neg ψ :: Γ₀, S.succedent⟩ < n := by
      rw [← hmeas]; exact (measure_negandL hΓ).2
    exact Deriv.ex hΓ.symm (List.Perm.refl _)
      (Deriv.negandL (ih _ hltφ _ rfl hvφ) (ih _ hltψ _ rfl hvψ))
  · -- negandR
    obtain ⟨φ, ψ, Δ₀, hΔ⟩ := d
    have hv : Sequent.Valid ⟨S.antecedent, .neg (.and φ ψ) :: Δ₀⟩ :=
      valid_of_perm (List.Perm.refl _) hΔ.symm h
    have hlt : Sequent.measure ⟨S.antecedent, .neg φ :: .neg ψ :: Δ₀⟩ < n := by
      rw [← hmeas]; exact measure_negandR hΔ
    exact Deriv.ex (List.Perm.refl _) hΔ.symm
      (Deriv.negandR (ih _ hlt _ rfl (negandR_inv hv)))
  · -- negorL
    obtain ⟨φ, ψ, Γ₀, hΓ⟩ := d
    have hv : Sequent.Valid ⟨.neg (.or φ ψ) :: Γ₀, S.succedent⟩ :=
      valid_of_perm hΓ.symm (List.Perm.refl _) h
    have hlt : Sequent.measure ⟨.neg φ :: .neg ψ :: Γ₀, S.succedent⟩ < n := by
      rw [← hmeas]; exact measure_negorL hΓ
    exact Deriv.ex hΓ.symm (List.Perm.refl _)
      (Deriv.negorL (ih _ hlt _ rfl (negorL_inv hv)))
  · -- negorR
    obtain ⟨φ, ψ, Δ₀, hΔ⟩ := d
    have hv : Sequent.Valid ⟨S.antecedent, .neg (.or φ ψ) :: Δ₀⟩ :=
      valid_of_perm (List.Perm.refl _) hΔ.symm h
    obtain ⟨hvφ, hvψ⟩ := negorR_inv hv
    have hltφ : Sequent.measure ⟨S.antecedent, .neg φ :: Δ₀⟩ < n := by
      rw [← hmeas]; exact (measure_negorR hΔ).1
    have hltψ : Sequent.measure ⟨S.antecedent, .neg ψ :: Δ₀⟩ < n := by
      rw [← hmeas]; exact (measure_negorR hΔ).2
    exact Deriv.ex (List.Perm.refl _) hΔ.symm
      (Deriv.negorR (ih _ hltφ _ rfl hvφ) (ih _ hltψ _ rfl hvψ))

/-- **Completeness.** Every valid sequent is derivable. -/
theorem completeness {S : Sequent} (h : S.Valid) : ⊢ₛ S :=
  completeness_aux S.measure S rfl h

end FDE
