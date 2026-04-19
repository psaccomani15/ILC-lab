/*
 * send_more_money.c -- SEND + MORE = MONEY (apêndice).
 *
 * Atribuir dígitos distintos 0-9 a S, E, N, D, M, O, R, Y tais que
 *   SEND + MORE = MONEY
 * com S != 0 e M != 0.
 *
 * Solução única clássica: 9567 + 1085 = 10652.
 * Compilar: gcc send_more_money.c -lcvc5 -o send_more_money
 */

#include <cvc5/c/cvc5.h>
#include <stdio.h>

int main(void) {
    Cvc5TermManager *tm = cvc5_term_manager_new();
    Cvc5 *slv           = cvc5_new(tm);
    cvc5_set_logic(slv, "QF_LIA");
    cvc5_set_option(slv, "produce-models", "true");

    Cvc5Sort int_sort = cvc5_get_integer_sort(tm);
    Cvc5Term zero = cvc5_mk_integer_int64(tm, 0);
    Cvc5Term nine = cvc5_mk_integer_int64(tm, 9);

    /* Variáveis: uma por letra. */
    const char *names[8] = {"S","E","N","D","M","O","R","Y"};
    Cvc5Term v[8];
    for (int i = 0; i < 8; i++) {
        v[i] = cvc5_mk_const(tm, int_sort, names[i]);
        cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_LEQ, 2, (Cvc5Term[]){zero, v[i]}));
        cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_LEQ, 2, (Cvc5Term[]){v[i], nine}));
    }
    /* Todas distintas. */
    cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_DISTINCT, 8, v));

    Cvc5Term S = v[0], E = v[1], N = v[2], D = v[3];
    Cvc5Term M = v[4], O = v[5], R = v[6], Y = v[7];

    /* S != 0  e  M != 0 (sem zeros à esquerda). */
    cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_DISTINCT, 2, (Cvc5Term[]){S, zero}));
    cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_DISTINCT, 2, (Cvc5Term[]){M, zero}));

    /* Pesos decimais como constantes. */
    Cvc5Term t10    = cvc5_mk_integer_int64(tm, 10);
    Cvc5Term t100   = cvc5_mk_integer_int64(tm, 100);
    Cvc5Term t1000  = cvc5_mk_integer_int64(tm, 1000);
    Cvc5Term t10000 = cvc5_mk_integer_int64(tm, 10000);

    /* SEND = 1000*S + 100*E + 10*N + D */
    Cvc5Term mS = cvc5_mk_term(tm, CVC5_KIND_MULT, 2, (Cvc5Term[]){t1000, S});
    Cvc5Term mE = cvc5_mk_term(tm, CVC5_KIND_MULT, 2, (Cvc5Term[]){t100,  E});
    Cvc5Term mN = cvc5_mk_term(tm, CVC5_KIND_MULT, 2, (Cvc5Term[]){t10,   N});
    Cvc5Term send  = cvc5_mk_term(tm, CVC5_KIND_ADD, 4, (Cvc5Term[]){mS, mE, mN, D});

    /* MORE = 1000*M + 100*O + 10*R + E */
    Cvc5Term mM = cvc5_mk_term(tm, CVC5_KIND_MULT, 2, (Cvc5Term[]){t1000, M});
    Cvc5Term mO = cvc5_mk_term(tm, CVC5_KIND_MULT, 2, (Cvc5Term[]){t100,  O});
    Cvc5Term mR = cvc5_mk_term(tm, CVC5_KIND_MULT, 2, (Cvc5Term[]){t10,   R});
    Cvc5Term more = cvc5_mk_term(tm, CVC5_KIND_ADD, 4, (Cvc5Term[]){mM, mO, mR, E});

    /* MONEY = 10000*M + 1000*O + 100*N + 10*E + Y */
    Cvc5Term mMy = cvc5_mk_term(tm, CVC5_KIND_MULT, 2, (Cvc5Term[]){t10000, M});
    Cvc5Term mOy = cvc5_mk_term(tm, CVC5_KIND_MULT, 2, (Cvc5Term[]){t1000,  O});
    Cvc5Term mNy = cvc5_mk_term(tm, CVC5_KIND_MULT, 2, (Cvc5Term[]){t100,   N});
    Cvc5Term mEy = cvc5_mk_term(tm, CVC5_KIND_MULT, 2, (Cvc5Term[]){t10,    E});
    Cvc5Term money = cvc5_mk_term(tm, CVC5_KIND_ADD, 5, (Cvc5Term[]){mMy, mOy, mNy, mEy, Y});

    /* SEND + MORE = MONEY */
    Cvc5Term sum = cvc5_mk_term(tm, CVC5_KIND_ADD,   2, (Cvc5Term[]){send, more});
    cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, (Cvc5Term[]){sum, money}));

    Cvc5Result r = cvc5_check_sat(slv);
    printf("cvc5: %s\n", cvc5_result_to_string(r));
    if (cvc5_result_is_sat(r)) {
        for (int i = 0; i < 8; i++) {
            Cvc5Term val = cvc5_get_value(slv, v[i]);
            printf("  %s = %ld\n", names[i], (long) cvc5_term_get_int64_value(val));
        }
    }

    cvc5_delete(slv);
    cvc5_term_manager_delete(tm);
    return 0;
}
