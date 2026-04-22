/-
  ND/Exercicio.lean -- Exercício 4 (12 pontos) da prova.

  Objetivo: provar em Lean, **interativamente**, que

    ((ψ₁ ∨ ψ₂) ∧ ((ψ₁ ∧ ψ₃) ∨ (ψ₁ ∧ ψ₃))) → ((ψ₁ ∨ ψ₂) ∧ ψ₃)

-/

import ND.Basic

namespace ND
open Proof
open Notation

@[simp]
theorem exercicio_prova : Proof [] (((p ∨ q) ∧ ((p ∧ r) ∨ (p ∧ r))) ⇒ ((p ∨ q) ∧ r))  := by
  apply Proof.impI
  apply Proof.andI
  -- Dois goals:
  · apply Proof.andEd (ψ := (p ∧ r) ∨ (p ∧ r))
    apply Proof.hyp
    simp
  · apply Proof.orE (φ := p ∧ r) (ψ := p ∧ r)
    -- Três goals:
    · apply Proof.andEe (φ := p ∨ q)
      apply Proof.hyp
      simp
    · apply Proof.andEe (φ := p)
      apply Proof.hyp
      simp
    · apply Proof.andEe (φ := p)
      apply Proof.hyp
      simp

example : Proof [] (((p ∨ q) ∧ ((p ∧ r) ∨ (p ∧ r))) ⇒ ((p ∨ q) ∧ r)) := by
  simp

theorem exercicio_prova' (p q r: Prop): (p ∨ q) ∧ ((p ∧ r) ∨ (p ∧ r)) → (p ∨ q)  ∧ r := by
  intro h             -- impI
  constructor         -- andI
  · exact h.left      -- andEd
  · have h' := h.right
    apply Or.elim h'  -- orE
    · intro hpr       -- impI
      exact hpr.right -- andEe
    · intro hpr       -- impI
      exact hpr.right -- andEe
end ND
