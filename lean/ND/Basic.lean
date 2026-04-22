/-
  ND/Basic.lean -- Dedução Natural para Lógica Proposicional
  DCC638 ILC, aula prática 2026-04-22.

  Definimos:
    - o tipo `Form` de fórmulas proposicionais
    - o tipo `Proof : List Form → Form → Prop` codificando as
      10 regras de dedução natural vistas em `05-proofs-nd.pdf`.

  Notação das regras segue os slides da disciplina:
    andI, andEd (elim direita -- dá o operando esquerdo),
    andEe (elim esquerda -- dá o operando direito),
    orId, orIe, orE, impI, impE, notI, notE, absurd (red. ao absurdo).
-/
namespace ND

/-! ## Fórmulas -/

inductive Form : Type
  | var : Nat  → Form
  | and : Form → Form → Form
  | or  : Form → Form → Form
  | imp : Form → Form → Form
  | neg : Form → Form
  | bot : Form
  deriving Repr, DecidableEq

/-! ## Notação

Abreviações para os conectivos, usadas tanto na definição do sistema
dedutivo quanto em qualquer arquivo que faça `open ND.Notation`.
-/

namespace Notation
  scoped infixr:35 " ∧ "  => Form.and
  scoped infixr:30 " ∨ "  => Form.or
  scoped infixr:25 " ⇒ " => Form.imp
  scoped prefix:max "¬" => Form.neg
  scoped notation "⊥ₚ"    => Form.bot
end Notation

open Notation

/-! ## Dedução Natural

`Proof Γ φ` significa "a partir do contexto Γ, deriva-se φ".
Cada construtor corresponde a uma regra de inferência nos slides.
-/
inductive Proof : List Form → Form → Prop
  -- Usar uma hipótese do contexto.
  | hyp    {Γ φ}     : φ ∈ Γ → Proof Γ φ

  -- Conjunção.
  | andI   {Γ φ ψ}   : Proof Γ φ → Proof Γ ψ → Proof Γ (φ ∧ ψ)
  | andEd  {Γ φ ψ}   : Proof Γ (φ ∧ ψ) → Proof Γ φ
  | andEe  {Γ φ ψ}   : Proof Γ (φ ∧ ψ) → Proof Γ ψ

  -- Disjunção.
  | orId   {Γ φ ψ}   : Proof Γ φ → Proof Γ (φ ∨ ψ)
  | orIe   {Γ φ ψ}   : Proof Γ ψ → Proof Γ (φ ∨ ψ)
  | orE    {Γ φ ψ χ} : Proof Γ (φ ∨ ψ)
                    → Proof (φ :: Γ) χ
                    → Proof (ψ :: Γ) χ
                    → Proof Γ χ

  -- Implicação.
  | impI   {Γ φ ψ}   : Proof (φ :: Γ) ψ → Proof Γ (φ ⇒ ψ)
  | impE   {Γ φ ψ}   : Proof Γ (φ ⇒ ψ) → Proof Γ φ → Proof Γ ψ

  -- Negação e absurdo.
  | notI   {Γ φ}     : Proof (φ :: Γ) ⊥ₚ → Proof Γ (¬ φ)
  | notE   {Γ φ}     : Proof Γ (¬ φ) → Proof Γ φ → Proof Γ ⊥ₚ
  | absurd {Γ φ}     : Proof ((¬ φ) :: Γ) ⊥ₚ → Proof Γ φ

/-! ## Primeiro exemplo da aula: ⊢ (φ ⋀ ψ) → φ -/
open Proof

abbrev p : Form := Form.var 0
abbrev q : Form := Form.var 1
abbrev r : Form := Form.var 2

example : Proof [] ((p ∧ q) ⇒ p) := by
  apply impI
  apply andEd (ψ := q)
  apply hyp
  simp

example (a b : Prop) : a ∧ b → a := by
  intro h      --  impI
  exact h.left -- andEd, Hyp

example : Proof [] ((p ⇒ (q ∧ r)) ⇒ ((p ⇒ q) ∧ (p ⇒ r))) := by
  apply impI
  apply andI
  · apply impI
    apply andEd (ψ := r)
    apply impE (φ := p)
    · apply hyp
      simp
    · apply hyp
      simp
  · apply impI
    apply andEe (φ := q)
    apply impE (φ := p)
    · apply hyp
      simp
    · apply hyp
      simp

example (p q r : Prop) : (p → (q ∧ r)) → ((p → q) ∧ (p → r)) := by
  intro h              -- impI
  constructor          -- andI
  · intro hp           -- impI
    exact (h hp).left  -- impE, andEd
  · intro hp           -- impI
    exact (h hp).right -- impE, andEe

example : Proof [] ((p ⇒ q) ⇒ (p ⇒ (q ∨ r))) := by
  apply impI
  apply impI
  apply orId
  apply impE (φ := p)
  · apply hyp
    simp
  · apply hyp
    simp

example (p q r: Prop) : (p → q) → (p → (q ∨ r)) := by
  intro h       -- impI
  intro hp      -- impI
  apply Or.inl  -- orId
  exact h hp    -- impE

example : Proof [] ((p ∧ q) ∨ (p ∧ r) ⇒ p) := by
  apply impI
  apply orE (φ := p ∧ q) (ψ := p ∧ r)
  · apply hyp
    simp
  · apply andEd (ψ := q)
    apply hyp
    simp
  · apply andEd (ψ := r)
    apply hyp
    simp

example (p q r: Prop): (p ∧ q) ∨ (p ∧ r) → p := by
  intro h         -- impI
  apply Or.elim h -- orE
  · intro hpq
    exact hpq.left -- andEd
  · intro hpr
    exact hpr.left -- andEd

end ND
