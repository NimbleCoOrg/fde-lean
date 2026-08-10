# fde-lean

A Lean 4 formalization of **First-Degree Entailment (FDE / Belnap–Dunn four-valued logic)**:
a G3-style invertible sequent calculus with **soundness and completeness** proved against the
four-valued semantics, plus the corollaries that fall out of the pair.

## Status: metatheorems + corollaries verified, zero sorries

| Theorem | Statement | Axioms |
|---|---|---|
| Soundness | `Deriv.sound : ⊢ₛ S → S.Valid` | `propext` |
| Completeness | `completeness : S.Valid → ⊢ₛ S` | `propext, Classical.choice, Quot.sound` |
| No theorems | `no_valid_formula : ¬ S.Valid ⟨[], [φ]⟩` | `propext` |
| Disjunction property (vacuous) | `disjunction_property` | `propext` |
| Decidability | `decidable_deriv : (⊢ₛ S) ∨ (¬ ⊢ₛ S)` | `propext, Classical.choice, Quot.sound` |
| Soundness+completeness iff | `deriv_iff_valid : (⊢ₛ S) ↔ S.Valid` | `propext, Classical.choice, Quot.sound` |

The disjunction property is stated **vacuously and honestly**: FDE has no theorems, so any
statement with `⊢ₛ ⟨[], [φ ∨ ψ]⟩` as antecedent holds trivially. The substantive
sequent-level disjunction property is `disjunction_property_sequent` (= `orR_inv`: `Γ ⇒ Δ,
φ ∨ ψ` is valid iff `Γ ⇒ Δ, φ, ψ` is valid). Decidability is proved as a Prop disjunction
(the `Or`/`∃` from `decompose` eliminate only into `Prop`); a `Decidable` instance is
recovered from it via `Classical.choice`.

**Correction (2026-08-11, external review):** an earlier draft claimed the `Classical.choice`
in `decidable_deriv` came *solely* from that `Decidable` lift. That is wrong, and the axiom
report contradicts it: `derivable_or_not` — the pure Prop proof, before any lift — already
carries `[propext, Classical.choice, Quot.sound]`, because its negative branches call
`completeness`, which carries the same three. The lift adds nothing. The choice axiom is
inherited from `completeness`, not introduced by the `Decidable` instance.

**What "decidable" means here (precision, not oversell):** the artifact is *decidability as a
theorem* — `decidable_deriv : (⊢ₛ S) ∨ (¬ ⊢ₛ S)` in `Prop`, plus a `Classical.choice`-lifted
`Decidable` instance. It is **not** an executable `Bool`-valued proof-search function; the
`Decidable` instance is `noncomputable` (verified: `decide (⊢ₛ ⟨[atom 0],[atom 0]⟩)` fails to
compile with `dependsOnNoncomputable`), and `Deriv` is `Prop`-valued, so no search is
extractable. A runnable checker would require `Deriv` in `Type` with its own termination
proof — future work, not claimed here.

Verification recipe (reproducible):

```bash
export PATH=<elan>/bin:$PATH && cd fde-lean
lake build FDE.Corollaries        # module-targeted — do NOT trust bare `lake build`
grep -nE ":= *(by *)?sorry|admit|sorryAx|native_decide" FDE/*.lean   # → empty
# #print axioms decidable_deriv → [propext, Classical.choice, Quot.sound]
```

Toolchain: `leanprover/lean4:nightly-2026-07-14`. mathlib: pinned `f566658afd`
(nightly-testing). Platform: aarch64-linux.

**Provenance:** formalized by the Matilde research agent (Hermes stack); the completeness
assembly and repair sessions ran on **Kimi K3 (open-weight, Moonshot AI)** via OpenRouter,
with earlier sessions on Claude. The Catuṣkoṭi formalization (`catuskoti-verified/`) is a
separate replication project — this FDE work is original to this repo.

## Reproducibility and the open-model claim

The artifact (this repo) is what the Lean kernel checks — that assurance is
model-independent. The open-weight claim is about **provenance and rerunnability**, not
proof strength: a closed-model Lean artifact is equally kernel-checkable. What open weights
make possible is pinning the exact prover:

- **Model / checkpoint:** `moonshotai/kimi-k3` (open weights), via OpenRouter. The weights
  are downloadable, so this exact prover can be re-run; a frontier closed model cannot be
  pinned this way (no checkpoint to fetch).
- **Harness:** Hermes Agent (Nous Research), `github.com/NimbleCoAI/Matilde`, running the
  `lean4-formalization` skill.
- **Build pin:** toolchain `leanprover/lean4:nightly-2026-07-14`; mathlib `f566658afd`
  (nightly-testing); platform aarch64-linux. Both pinned in `lean-toolchain` and
  `lakefile.toml` / `lake-manifest.json`.
- **Conversation traces:** the proving sessions ran in Discord threads; the structured
  session logs are the durable record. (PROMPTS/TRACES: to be archived alongside this repo
  before the VibeMathed submission — the claim "the process is rerunnable" is only as
  strong as the traces being inspectable.)

The honest scope: kernel acceptance is *not* evidence the model "understands" logic, and
open weights do not raise proof assurance. They raise the auditability of how the proof was
produced. Those are different claims and this repo argues only the second.

## Layout

- `FDE/Basic.lean` — `Val4 = {t, b, n, f}`, neg/conjunction/disjunction tables
  (`#eval`-ground-truthed against the Belnap–Dunn matrix; non-obvious entries
  `and(b,n)=f`, `or(b,n)=t`), `eval`, designated = has truth-support (`t`/`b`).
- `FDE/Sequent.lean` — two-sided sequents (lists + exchange via `List.Perm`), the NNF-based
  invertible calculus: atomic `id`, negated-atomic `idNeg`, and invertible ∧/∨/¬ rules
  including De Morgan (`¬(φ∧ψ)` → `¬φ,¬ψ` left-pair / right-pair etc.).
- `FDE/Soundness.lean` — `Deriv.sound` by induction on the derivation; designated-value
  algebra lemmas; validity transport across permutation.
- `FDE/Completeness.lean` — 10 inversion lemmas (each rule valid backwards), the canonical
  **antecedent-only** refuting valuation (`ts := p∈Γ`, `fs := ¬p∈Γ` ↦ (T,T)=b,(T,F)=t,
  (F,T)=f,(F,F)=n), `Saturated` (forbids exactly the identity pairs `p∈Γ∧p∈Δ`,
  `¬p∈Γ∧¬p∈Δ`), `Saturated.refutes`, the negation-weighted measure
  (`deg ¬φ = 1+2·deg φ` — plain connective count does NOT decrease under De Morgan), and
  `completeness` by strong induction on the measure over the 12-way `decompose` disjunction.
- `FDE/Corollaries.lean` — the downstream results: `no_valid_formula` (FDE has no theorems,
  constant-n valuation), the disjunction property (vacuous; the substantive sequent-level
  one is `orR_inv`), and **decidability** (`decidable_deriv`) — proof search by strong
  induction on the measure, with the underivable branches closed by the sound→invert→complete
  loop (no cut-admissibility needed). A `Decidable` instance is recovered via `Classical.choice`.

## Design notes (the non-obvious parts)

- **The canonical valuation reads from the antecedent only.** Reading falsity-support from
  the succedent is mathematically wrong: the saturated sequent `{p, ¬p} ⇒ {}` would map `p`
  to `t` and leave antecedent `¬p` undesignated. Re-confirmed twice by exhaustive `#eval`
  over all four (ts,fs) cells; do not re-litigate.
- **Cross-pair literal sequents are invalid.** `p ⇒ ¬p` and `¬p ⇒ p` have countermodels
  (`p=t`, `p=f`); only same-literal identities are initial. Hence `idNeg` was added as a
  constructor — `¬p ⇒ ¬p` is valid but was underivable without it.
- **The measure must weight negation double.** De Morgan preserves raw connective count
  (1 neg + 1 and = 2 negs), so an unweighted size does not terminate the NNF descent.

## Caveat (standing)

"Kernel verifies these proofs" ≠ "the encoding faithfully captures the source theory."
The encoding choices (designated = truth-support, NNF calculus, list-based sequents with
explicit exchange) are documented above and in the source docstrings; the audit question is
separate from the build status.
