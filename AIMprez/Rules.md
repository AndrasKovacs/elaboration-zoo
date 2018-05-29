
Syntax of terms and contexts

    A, B, t, u ::=
      λx. t | t u | x | (x : A) → B | U | let x = t : A in u

    Γ, Δ, Σ ::= ∙              -- empty context
              | Γ , x = t : A  -- defined name
              | Γ , x : A      -- bound variable
              | Γ , x = ? : A  -- metavariable binding

Presyntax

    A, B, t, u ::=
      λx. t | t u | x | (x : A) → B | U | let x = t : A in u | _

Conversion and typing rules for let and metas

    ───────────────────────────────────  let conversion
    Γ ⊢ (let x = t : A in u) ≡ u[x ↦ t]

          ───────────────────────  δ-conversion
          Γ, x = t : A, Δ ⊢ x ≡ t

      Γ ⊢ t : A   Γ, x = t : A ⊢ u : B
      ────────────────────────────────  let typing
        Γ ⊢ (let x = t : A in u) : B

          ───────────────────────  meta typing
          Γ, x = ? : A, Δ ⊢ x : A

Strengthening

  If `Γ, Δ ⊢ t : A` then we may write `Γ ⊢ t : A` if such strengthening
  is possible.

  Strengthening may involve unfolding definitions from `Δ`,
  or adding them as `let`-s.

  For example: if `Γ, x = t : A ⊢ x : B`, then two possible `Γ-`strengthenings of `x` are:
    + `Γ ⊢ t : B[x ↦ t]`
    + `Γ ⊢ (let x = t : A in x) : (let x = t : A in B)`

  Strengthening may fail in elab. operations

Unification

  Judgement: Γ ⊢ t =? u ⊣ Δ

  Unifying `t` and `u` terms, returning `Δ` such that `Γ ≤ Δ` and `Δ ⊢
  t ≡ u`. The sides must have the same type, but unification is *not*
  type-directed.

  Since unification is not type-directed, we omit types of bound variables
  whenever we go under binders.

  For λ, Π, application, U: unification is structural.
