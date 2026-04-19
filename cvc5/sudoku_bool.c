/*
 * sudoku_bool.c -- Sudoku 9x9 via codificação booleana pura (SAT).
 *
 * Variáveis: x[i][j][v] é verdadeira sse a célula (i,j) contém o valor v+1.
 * Restrições:
 *   - Cada célula tem exatamente um valor.
 *   - Cada linha  tem cada valor ao menos uma vez (consequentemente, exatamente).
 *   - Cada coluna tem cada valor ao menos uma vez.
 *   - Cada bloco  tem cada valor ao menos uma vez.
 *   - Pistas fixam x[i][j][v] quando o puzzle tem v+1 na célula (i,j).
 *
 * Fora do domínio SAT-puro, a codificação inteira (sudoku_int.c) é ordens
 * de grandeza menor. Este arquivo existe para contrastar as duas codificações.
 *
 * Compilar: gcc sudoku_bool.c -lcvc5 -o sudoku_bool
 */

#include <cvc5/c/cvc5.h>
#include <stdio.h>
#include <stdbool.h>

static const char *PUZZLE =
    "53..7...."
    "6..195..."
    ".98....6."
    "8...6...3"
    "4..8.3..1"
    "7...2...6"
    ".6....28."
    "...419..5"
    "....8..79";

static void assert_exactly_one(Cvc5TermManager *tm, Cvc5 *slv,
                               Cvc5Term *vars, int n) {
    /* pelo menos um */
    cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_OR, n, vars));
    /* no máximo um (pairwise) */
    for (int a = 0; a < n; a++) {
        for (int b = a + 1; b < n; b++) {
            Cvc5Term not_b = cvc5_mk_term(tm, CVC5_KIND_NOT, 1, (Cvc5Term[]){vars[b]});
            cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_IMPLIES, 2,
                                                  (Cvc5Term[]){vars[a], not_b}));
        }
    }
}

int main(void) {
    Cvc5TermManager *tm = cvc5_term_manager_new();
    Cvc5 *slv           = cvc5_new(tm);
    cvc5_set_logic(slv, "QF_UF");
    cvc5_set_option(slv, "produce-models", "true");

    Cvc5Sort bool_sort = cvc5_get_boolean_sort(tm);
    Cvc5Term x[9][9][9];
    char name[32];
    for (int i = 0; i < 9; i++)
        for (int j = 0; j < 9; j++)
            for (int v = 0; v < 9; v++) {
                snprintf(name, sizeof(name), "x_%d_%d_%d", i, j, v);
                x[i][j][v] = cvc5_mk_const(tm, bool_sort, name);
            }

    /* Cada célula tem exatamente um valor. */
    for (int i = 0; i < 9; i++)
        for (int j = 0; j < 9; j++) {
            Cvc5Term cell[9];
            for (int v = 0; v < 9; v++) cell[v] = x[i][j][v];
            assert_exactly_one(tm, slv, cell, 9);
        }

    /* Cada linha tem cada valor. */
    for (int i = 0; i < 9; i++)
        for (int v = 0; v < 9; v++) {
            Cvc5Term row[9];
            for (int j = 0; j < 9; j++) row[j] = x[i][j][v];
            cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_OR, 9, row));
        }

    /* Cada coluna tem cada valor. */
    for (int j = 0; j < 9; j++)
        for (int v = 0; v < 9; v++) {
            Cvc5Term col[9];
            for (int i = 0; i < 9; i++) col[i] = x[i][j][v];
            cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_OR, 9, col));
        }

    /* Cada bloco 3x3 tem cada valor. */
    for (int bi = 0; bi < 3; bi++)
        for (int bj = 0; bj < 3; bj++)
            for (int v = 0; v < 9; v++) {
                Cvc5Term block[9];
                int k = 0;
                for (int di = 0; di < 3; di++)
                    for (int dj = 0; dj < 3; dj++)
                        block[k++] = x[3*bi + di][3*bj + dj][v];
                cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_OR, 9, block));
            }

    /* Pistas iniciais. */
    for (int k = 0; k < 81; k++) {
        char ch = PUZZLE[k];
        if (ch >= '1' && ch <= '9') {
            int i = k / 9, j = k % 9;
            int v = ch - '1';
            cvc5_assert_formula(slv, x[i][j][v]);
        }
    }

    Cvc5Result r = cvc5_check_sat(slv);
    printf("cvc5: %s\n\n", cvc5_result_to_string(r));

    if (cvc5_result_is_sat(r)) {
        for (int i = 0; i < 9; i++) {
            if (i > 0 && i % 3 == 0) printf("------+-------+------\n");
            for (int j = 0; j < 9; j++) {
                if (j > 0 && j % 3 == 0) printf("| ");
                for (int v = 0; v < 9; v++) {
                    Cvc5Term val = cvc5_get_value(slv, x[i][j][v]);
                    if (cvc5_term_get_boolean_value(val)) {
                        printf("%d ", v + 1);
                        break;
                    }
                }
            }
            printf("\n");
        }
    }

    cvc5_delete(slv);
    cvc5_term_manager_delete(tm);
    return 0;
}
