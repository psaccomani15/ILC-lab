/-
  ND/Automacao.lean -- Apendice sobre automacao em Lean 4.

  Nosso `Proof` e um **sistema deductivo customizado**: a unica maneira
  de construir `Proof Γ φ` e aplicar as 10 regras da aula. O Lean NAO
  automatiza isso sozinho -- e esse e precisamente o ponto pedagogico.

  Mas Lean tambem oferece uma logica classica "de fabrica" (o `Prop`
  interno), e para formulas _nessa_ logica, ha varias taticas que
  fecham provas automaticamente. Este apendice contrasta os dois
  mundos.
-/

import ND.Basic
import ND.Exercicio

namespace ND

/-! ## 1. A mesma formula, provada em `Prop` diretamente. -/

/-
  Se substituirmos nosso `Form` pela logica nativa do Lean, a formula
  do exercicio vira uma proposicao `Prop` sobre variaveis
  `(q1 q2 q3 : Prop)`. Com alguns `intro` e um `rcases`, o Lean fecha
  sozinho -- sem invocar nossas 10 regras explicitas.
-/
example (q1 q2 q3 : Prop) :
    ((q1 ∨ q2) ∧ ((q1 ∧ q3) ∨ (q1 ∧ q3))) → ((q1 ∨ q2) ∧ q3) := by
  intro h
  rcases h with ⟨hor, hd⟩
  rcases hd with ⟨_, h3⟩ | ⟨_, h3⟩
  · exact ⟨hor, h3⟩
  · exact ⟨hor, h3⟩

/-
  Alternativamente, formulas booleanas finitas sao **decidiveis**:
  `decide` avalia a tabela-verdade por forca bruta.
-/
example :
    ∀ (b1 b2 b3 : Bool),
      ((b1 || b2) && ((b1 && b3) || (b1 && b3))) = true
    → ((b1 || b2) && b3) = true := by
  decide

/-! ## 2. Por que nosso `Proof` nao "se prova sozinho". -/

/-
  `tauto` so resolve formulas de `Prop` (a logica interna do Lean).
  Nosso `Proof [] Teorema` vive num tipo diferente -- um sistema
  dedutivo indutivo definido por nos. Por isso, cada passo precisa ser
  uma aplicacao explicita das 10 regras.

  Isto nao e uma limitacao: e o que torna nosso sistema **didatico**.
  O aluno ve cada regra sendo usada; o Lean garante que nao ha saltos.
-/

#check @exercicio_prova
-- exercicio_prova : Proof [] Teorema

/-! ## 3. Mini-automacao com `constructor` e `assumption`. -/

/-
  Ainda assim, dentro do nosso sistema podemos usar taticas gerais do
  Lean para simplificar passos mecanicos:
    - `constructor` tenta aplicar o construtor apropriado;
    - `assumption` fecha goals triviais do tipo `x ∈ (x :: _)`.
-/

example : Proof [] (Form.imp (Form.and p1 p2) p1) := by
  apply Proof.impI
  apply Proof.andEd (ψ := p2)
  apply Proof.hyp
  exact List.Mem.head _

/-
  Com `simp` e `decide` podemos fechar as provas de pertinencia
  automaticamente (em vez de `List.Mem.head _`):
-/

example : Proof [] (Form.imp (Form.and p1 p2) p1) := by
  apply Proof.impI
  apply Proof.andEd (ψ := p2)
  apply Proof.hyp
  simp

end ND
