/*
 * predicados.c -- Exercício de predicados (Lista 3, Rosen 1.4.11 item (e)).
 *
 * Enunciado:
 *   "Todo professor que já foi perguntado por algum estudante
 *    foi questionado pelo Prof. Marcos."
 *
 * Predicados:
 *   S(x)    : x é estudante
 *   F(x)    : x é professor
 *   A(x, y) : x fez uma pergunta a y
 *   m       : a constante "Prof. Marcos"
 *
 * Dois alunos entregam formalizações diferentes:
 *
 *   Codificação A (antecedente em conjunção):
 *     ∀x. (F(x) ∧ ∃y. (S(y) ∧ A(y, x))) → A(m, x)
 *
 *   Codificação B (implicações encadeadas):
 *     ∀x. F(x) → (∃y. (S(y) ∧ A(y, x)) → A(m, x))
 *
 * Atestamos a equivalência (A ↔ B) assertando NOT(A ↔ B) e
 * verificando que o resultado é UNSAT.
 *
 * Compilar: gcc predicados.c -lcvc5 -o predicados
 */

#include <cvc5/c/cvc5.h>
#include <stdio.h>

int main(void) {
    Cvc5TermManager *tm = cvc5_term_manager_new();
    Cvc5 *slv = cvc5_new(tm);
    cvc5_set_logic(slv, "UF");

    /* ---------- Sorts e símbolos ---------- */
    Cvc5Sort pessoa    = cvc5_mk_uninterpreted_sort(tm, "Pessoa");
    Cvc5Sort bool_sort = cvc5_get_boolean_sort(tm);

    /* S, F : Pessoa → Bool */
    Cvc5Sort pred1 = cvc5_mk_fun_sort(tm, 1, (Cvc5Sort[]){pessoa}, bool_sort);
    Cvc5Term S = cvc5_mk_const(tm, pred1, "S");
    Cvc5Term F = cvc5_mk_const(tm, pred1, "F");

    /* A : Pessoa × Pessoa → Bool */
    Cvc5Sort pred2 = cvc5_mk_fun_sort(tm, 2, (Cvc5Sort[]){pessoa, pessoa}, bool_sort);
    Cvc5Term A = cvc5_mk_const(tm, pred2, "A");

    /* Constante: Prof. Marcos. */
    Cvc5Term m = cvc5_mk_const(tm, pessoa, "marcos");

    /* ---------- Variáveis ---------- */
    Cvc5Term x = cvc5_mk_var(tm, pessoa, "x");
    Cvc5Term y = cvc5_mk_var(tm, pessoa, "y");

    /* F(x), S(y), A(y, x), A(m, x) */
    Cvc5Term Fx  = cvc5_mk_term(tm, CVC5_KIND_APPLY_UF, 2, (Cvc5Term[]){F, x});
    Cvc5Term Sy  = cvc5_mk_term(tm, CVC5_KIND_APPLY_UF, 2, (Cvc5Term[]){S, y});
    Cvc5Term Ayx = cvc5_mk_term(tm, CVC5_KIND_APPLY_UF, 3, (Cvc5Term[]){A, y, x});
    Cvc5Term Amx = cvc5_mk_term(tm, CVC5_KIND_APPLY_UF, 3, (Cvc5Term[]){A, m, x});

    /* ∃y. S(y) ∧ A(y, x) -- mesmo sub-termo nas duas codificações */
    Cvc5Term SyAyx  = cvc5_mk_term(tm, CVC5_KIND_AND, 2, (Cvc5Term[]){Sy, Ayx});
    Cvc5Term y_vlist = cvc5_mk_term(tm, CVC5_KIND_VARIABLE_LIST, 1, (Cvc5Term[]){y});
    Cvc5Term ex_y   = cvc5_mk_term(tm, CVC5_KIND_EXISTS, 2, (Cvc5Term[]){y_vlist, SyAyx});

    /* Lista de variáveis para o ∀, reusada nas duas codificações. */
    Cvc5Term x_vlist = cvc5_mk_term(tm, CVC5_KIND_VARIABLE_LIST, 1, (Cvc5Term[]){x});

    /* ---------- Codificação A:
     *   ∀x. (F(x) ∧ ex_y) → A(m, x)                           ---------- */
    Cvc5Term antA  = cvc5_mk_term(tm, CVC5_KIND_AND, 2, (Cvc5Term[]){Fx, ex_y});
    Cvc5Term implA = cvc5_mk_term(tm, CVC5_KIND_IMPLIES, 2, (Cvc5Term[]){antA, Amx});
    Cvc5Term encA  = cvc5_mk_term(tm, CVC5_KIND_FORALL, 2, (Cvc5Term[]){x_vlist, implA});

    /* ---------- Codificação B:
     *   ∀x. F(x) → (ex_y → A(m, x))                           ---------- */
    Cvc5Term inner = cvc5_mk_term(tm, CVC5_KIND_IMPLIES, 2, (Cvc5Term[]){ex_y, Amx});
    Cvc5Term outer = cvc5_mk_term(tm, CVC5_KIND_IMPLIES, 2, (Cvc5Term[]){Fx, inner});
    Cvc5Term encB  = cvc5_mk_term(tm, CVC5_KIND_FORALL, 2, (Cvc5Term[]){x_vlist, outer});

    /* ---------- Teste: ¬(A ↔ B). Se UNSAT, são equivalentes. ------ */
    Cvc5Term iff     = cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, (Cvc5Term[]){encA, encB});
    Cvc5Term neg_iff = cvc5_mk_term(tm, CVC5_KIND_NOT,   1, (Cvc5Term[]){iff});
    cvc5_assert_formula(slv, neg_iff);

    Cvc5Result r = cvc5_check_sat(slv);
    printf("Verificando equivalência entre Codificações A e B.\n");
    printf("  A: ∀x. (F(x) ∧ ∃y. (S(y) ∧ A(y,x))) → A(m, x)\n");
    printf("  B: ∀x. F(x) → (∃y. (S(y) ∧ A(y,x)) → A(m, x))\n");
    printf("esperado: unsat  (se A e B são equivalentes)\n");
    printf("cvc5    : %s\n", cvc5_result_to_string(r));

    cvc5_delete(slv);
    cvc5_term_manager_delete(tm);
    return 0;
}
