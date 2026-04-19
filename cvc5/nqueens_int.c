/*
 * nqueens_int.c -- Codificação aritmética do problema das N-rainhas.
 *
 * Ideia: em vez de n² variáveis booleanas, usamos n variáveis inteiras.
 *   col[i] ∈ {0, ..., N-1}  -- coluna da rainha na linha i.
 *
 * Restrições:
 *   (domínio)   0 <= col[i] < N
 *   (coluna)    col[i] distintos entre si
 *   (diag. ↘)   col[i] - i distintos (i.e., col[i] - col[j] != i - j)
 *   (diag. ↖)   col[i] + i distintos (i.e., col[i] - col[j] != j - i)
 *
 * Uma rainha por linha é garantida por construção (uma variável por linha).
 * O encoding usa teoria de aritmética linear inteira (LIA) -- fora de SAT puro.
 *
 * Compilar: gcc nqueens_int.c -lcvc5 -o nqueens_int
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
    cvc5_set_logic(slv, "QF_LIA");
    cvc5_set_option(slv, "produce-models", "true");

    Cvc5Sort int_sort = cvc5_get_integer_sort(tm);
    Cvc5Term col[N];
    Cvc5Term zero  = cvc5_mk_integer_int64(tm, 0);
    Cvc5Term n_val = cvc5_mk_integer_int64(tm, N);

    char name[16];
    for (int i = 0; i < N; i++) {
        snprintf(name, sizeof(name), "col_%d", i);
        col[i] = cvc5_mk_const(tm, int_sort, name);

        cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_LEQ, 2, (Cvc5Term[]){zero, col[i]}));
        cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_LT,  2, (Cvc5Term[]){col[i], n_val}));
    }

    /* col[i] todos distintos: nenhuma rainha compartilha coluna. */
    cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_DISTINCT, N, col));

    /* col[i] - i distintos: nenhuma rainha compartilha diagonal principal. */
    Cvc5Term main_diag[N];
    for (int i = 0; i < N; i++) {
        main_diag[i] = cvc5_mk_term(tm, CVC5_KIND_SUB, 2,
                                    (Cvc5Term[]){col[i], cvc5_mk_integer_int64(tm, i)});
    }
    cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_DISTINCT, N, main_diag));

    /* col[i] + i distintos: nenhuma rainha compartilha anti-diagonal. */
    Cvc5Term anti_diag[N];
    for (int i = 0; i < N; i++) {
        anti_diag[i] = cvc5_mk_term(tm, CVC5_KIND_ADD, 2,
                                    (Cvc5Term[]){col[i], cvc5_mk_integer_int64(tm, i)});
    }
    cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_DISTINCT, N, anti_diag));

    Cvc5Result r = cvc5_check_sat(slv);
    printf("N = %d (codificação aritmética)\n", N);
    printf("cvc5: %s\n", cvc5_result_to_string(r));

    if (cvc5_result_is_sat(r)) {
        int c[N];
        for (int i = 0; i < N; i++) {
            Cvc5Term v = cvc5_get_value(slv, col[i]);
            c[i] = (int) cvc5_term_get_int64_value(v);
        }
        printf("\nTabuleiro:\n");
        for (int i = 0; i < N; i++) {
            for (int j = 0; j < N; j++) {
                putchar(c[i] == j ? 'Q' : '.');
                putchar(' ');
            }
            putchar('\n');
        }
    }

    cvc5_delete(slv);
    cvc5_term_manager_delete(tm);
    return 0;
}
