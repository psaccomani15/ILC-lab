/-
  ND/Exercicio.lean -- Exercício 4 (12 pontos) da prova.

  Objetivo: provar em Lean, **interativamente**, que

    ((ψ₁ ∨ ψ₂) ∧ ((ψ₁ ∧ ψ₃) ∨ (ψ₁ ∧ ψ₃))) → ((ψ₁ ∨ ψ₂) ∧ ψ₃)

-/

import ND.Basic

namespace ND

abbrev p : Form := Form.var 0
abbrev q : Form := Form.var 1
abbrev r : Form := Form.var 2

open Proof
open Notation
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
end ND
