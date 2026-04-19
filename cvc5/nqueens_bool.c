/*
 * nqueens_bool.c -- Codificação booleana do problema das N-rainhas.
 *
 * Variáveis: p[i][j] é verdadeira se há uma rainha na linha i, coluna j.
 * Restrições (seguindo os slides 03-prop-logic-sat, Q1-Q5):
 *   Q1: pelo menos uma rainha por linha.
 *   Q2: no máximo uma rainha por linha.
 *   Q3: no máximo uma rainha por coluna.
 *   Q4: não há rainhas na mesma diagonal (descendente).
 *   Q5: não há rainhas na mesma diagonal (ascendente).
 *
 * Compilar: gcc nqueens_bool.c -lcvc5 -o nqueens_bool
 */

#include <cvc5/c/cvc5.h>
#include <stdio.h>
#include <stdbool.h>

#ifndef N
#define N 8
#endif

int main(void) {
    Cvc5TermManager *tm = cvc5_term_manager_new();
    Cvc5 *slv           = cvc5_new(tm);
    cvc5_set_logic(slv, "QF_UF");
    cvc5_set_option(slv, "produce-models", "true");

    Cvc5Sort bool_sort = cvc5_get_boolean_sort(tm);
    Cvc5Term p[N][N];

    char name[32];
    for (int i = 0; i < N; i++) {
        for (int j = 0; j < N; j++) {
            snprintf(name, sizeof(name), "p_%d_%d", i, j);
            p[i][j] = cvc5_mk_const(tm, bool_sort, name);
        }
    }

    /* Q1: pelo menos uma rainha por linha. */
    for (int i = 0; i < N; i++) {
        Cvc5Term row[N];
        for (int j = 0; j < N; j++) row[j] = p[i][j];
        cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_OR, N, row));
    }

    /* Q2: no máximo uma rainha por linha (pairwise). */
    for (int i = 0; i < N; i++) {
        for (int j = 0; j < N; j++) {
            for (int k = j + 1; k < N; k++) {
                Cvc5Term not_pik = cvc5_mk_term(tm, CVC5_KIND_NOT, 1, (Cvc5Term[]){p[i][k]});
                cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_IMPLIES, 2,
                                                      (Cvc5Term[]){p[i][j], not_pik}));
            }
        }
    }

    /* Q3: no máximo uma rainha por coluna (pairwise). */
    for (int j = 0; j < N; j++) {
        for (int i = 0; i < N; i++) {
            for (int k = i + 1; k < N; k++) {
                Cvc5Term not_pkj = cvc5_mk_term(tm, CVC5_KIND_NOT, 1, (Cvc5Term[]){p[k][j]});
                cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_IMPLIES, 2,
                                                      (Cvc5Term[]){p[i][j], not_pkj}));
            }
        }
    }

    /* Q4/Q5: diagonais. */
    for (int i = 0; i < N; i++) {
        for (int j = 0; j < N; j++) {
            /* diagonal descendente para direita: (i+k, j+k) */
            for (int k = 1; i + k < N && j + k < N; k++) {
                Cvc5Term np = cvc5_mk_term(tm, CVC5_KIND_NOT, 1, (Cvc5Term[]){p[i+k][j+k]});
                cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_IMPLIES, 2,
                                                      (Cvc5Term[]){p[i][j], np}));
            }
            /* diagonal ascendente para direita: (i+k, j-k) */
            for (int k = 1; i + k < N && j - k >= 0; k++) {
                Cvc5Term np = cvc5_mk_term(tm, CVC5_KIND_NOT, 1, (Cvc5Term[]){p[i+k][j-k]});
                cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_IMPLIES, 2,
                                                      (Cvc5Term[]){p[i][j], np}));
            }
        }
    }

    Cvc5Result r = cvc5_check_sat(slv);
    printf("N = %d (codificação booleana)\n", N);
    printf("cvc5: %s\n", cvc5_result_to_string(r));

    if (cvc5_result_is_sat(r)) {
        printf("\nTabuleiro:\n");
        for (int i = 0; i < N; i++) {
            for (int j = 0; j < N; j++) {
                Cvc5Term v = cvc5_get_value(slv, p[i][j]);
                bool has_queen = cvc5_term_get_boolean_value(v);
                putchar(has_queen ? 'Q' : '.');
                putchar(' ');
            }
            putchar('\n');
        }
    }

    cvc5_delete(slv);
    cvc5_term_manager_delete(tm);
    return 0;
}
