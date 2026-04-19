/-
  ND/Exercicio.lean -- Exercício 4 (12 pontos) da prova.

  Objetivo: provar em Lean, **interativamente**, que

    ((ψ₁ ∨ ψ₂) ∧ ((ψ₁ ∧ ψ₃) ∨ (ψ₁ ∧ ψ₃))) → ((ψ₁ ∨ ψ₂) ∧ ψ₃)

  Usamos o modo tático (`by ...`): cada `apply` aplica uma regra de
  dedução natural, e o InfoView do VSCode mostra o **estado do goal**
  se transformando passo a passo -- exatamente como desenhar a árvore
  de dedução de baixo para cima (da conclusão rumo às hipóteses).

  Neste arquivo, usamos apenas abreviações para as *variáveis* do
  exercício (`p1`, `Or12`, `H`, ...); os conectivos são escritos na
  forma construtor (`Form.and`, `Form.or`, `Form.imp`).
-/

import ND.Basic

namespace ND

/-! ## Abreviações para o exercício. -/

abbrev p1 : Form := Form.var 1
abbrev p2 : Form := Form.var 2
abbrev p3 : Form := Form.var 3

abbrev Or12  : Form := Form.or p1 p2           -- ψ₁ ∨ ψ₂
abbrev And13 : Form := Form.and p1 p3          -- ψ₁ ∧ ψ₃
abbrev D     : Form := Form.or And13 And13     -- (ψ₁ ∧ ψ₃) ∨ (ψ₁ ∧ ψ₃)
abbrev H     : Form := Form.and Or12 D         -- antecedente
abbrev C     : Form := Form.and Or12 p3        -- consequente
abbrev Teorema : Form := Form.imp H C

/-
  Cada linha do `by` corresponde a uma regra de dedução natural.
  Posicione o cursor **entre** dois `apply` consecutivos para ver
  no InfoView o goal sendo reescrito -- p.ex., antes de `apply Proof.impI`
  o goal é `Proof [] (H → C)`, depois vira `Proof [H] C`.
-/

theorem exercicio_prova : Proof [] Teorema := by
  -- Goal: Proof [] (H → C)
  apply Proof.impI
  -- Goal: Proof [H] C    (onde C = Or12 ∧ p3)
  apply Proof.andI
  -- Dois goals:
  --   (1) Proof [H] Or12
  --   (2) Proof [H] p3

  -- (1) Or12 segue de H por ∧Ed.
  · apply Proof.andEd (ψ := D)
    -- Goal: Proof [H] H    (H = Or12 ∧ D)
    apply Proof.hyp
    -- Goal: H ∈ [H]
    exact List.Mem.head _

  -- (2) p3 segue de D = And13 ∨ And13 por análise de casos (∨E).
  · apply Proof.orE (φ := And13) (ψ := And13)
    -- Três goals:
    --   (2a) Proof [H] D
    --   (2b) Proof (And13 :: [H]) p3
    --   (2c) Proof (And13 :: [H]) p3

    -- (2a) D segue de H por ∧Ee.
    · apply Proof.andEe (φ := Or12)
      apply Proof.hyp
      exact List.Mem.head _

    -- (2b) p3 segue de And13 = p1 ∧ p3 por ∧Ee (caso 1).
    · apply Proof.andEe (φ := p1)
      apply Proof.hyp
      exact List.Mem.head _

    -- (2c) idem (caso 2 é idêntico).
    · apply Proof.andEe (φ := p1)
      apply Proof.hyp
      exact List.Mem.head _

#check @exercicio_prova

end ND
