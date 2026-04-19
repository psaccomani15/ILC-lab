/*
 * hello.c -- primeiro contato com a API C do cvc5.
 *
 * Asserta a fórmula (x AND NOT x) e espera UNSAT.
 * Compilar: gcc hello.c -lcvc5 -o hello
 */

#include <cvc5/c/cvc5.h>
#include <stdio.h>

int main(void) {
    Cvc5TermManager *tm = cvc5_term_manager_new();
    Cvc5 *slv           = cvc5_new(tm);

    cvc5_set_logic(slv, "QF_UF");

    Cvc5Sort bool_sort = cvc5_get_boolean_sort(tm);
    Cvc5Term x         = cvc5_mk_const(tm, bool_sort, "x");

    Cvc5Term not_x   = cvc5_mk_term(tm, CVC5_KIND_NOT, 1, (Cvc5Term[]){x});
    Cvc5Term formula = cvc5_mk_term(tm, CVC5_KIND_AND, 2, (Cvc5Term[]){x, not_x});

    cvc5_assert_formula(slv, formula);

    Cvc5Result r = cvc5_check_sat(slv);
    printf("fórmula : (x AND NOT x)\n");
    printf("esperado: unsat\n");
    printf("cvc5    : %s\n", cvc5_result_to_string(r));

    cvc5_delete(slv);
    cvc5_term_manager_delete(tm);
    return 0;
}
