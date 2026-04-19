/*
 * sudoku_int.c -- Sudoku 9x9 via aritmética inteira + distinct.
 *
 * Variáveis: c[i][j] inteira, com 1 <= c[i][j] <= 9.
 * Restrições:
 *   - Cada linha tem todos os valores distintos.
 *   - Cada coluna tem todos os valores distintos.
 *   - Cada bloco 3x3 tem todos os valores distintos.
 *   - Pistas iniciais fixam o valor de algumas células.
 *
 * Puzzle hardcoded (string de 81 chars, '.' ou '0' para vazio).
 * Compilar: gcc sudoku_int.c -lcvc5 -o sudoku_int
 */

#include <cvc5/c/cvc5.h>
#include <stdio.h>
#include <stdbool.h>
#include <string.h>

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

int main(void) {
    Cvc5TermManager *tm = cvc5_term_manager_new();
    Cvc5 *slv           = cvc5_new(tm);
    cvc5_set_logic(slv, "QF_LIA");
    cvc5_set_option(slv, "produce-models", "true");

    Cvc5Sort int_sort = cvc5_get_integer_sort(tm);
    Cvc5Term one  = cvc5_mk_integer_int64(tm, 1);
    Cvc5Term nine = cvc5_mk_integer_int64(tm, 9);

    Cvc5Term c[9][9];
    char name[16];
    for (int i = 0; i < 9; i++) {
        for (int j = 0; j < 9; j++) {
            snprintf(name, sizeof(name), "c_%d_%d", i, j);
            c[i][j] = cvc5_mk_const(tm, int_sort, name);

            /* 1 <= c[i][j] <= 9 */
            cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_LEQ, 2, (Cvc5Term[]){one,     c[i][j]}));
            cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_LEQ, 2, (Cvc5Term[]){c[i][j], nine}));
        }
    }

    /* Linhas: distinct. */
    for (int i = 0; i < 9; i++) {
        Cvc5Term row[9];
        for (int j = 0; j < 9; j++) row[j] = c[i][j];
        cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_DISTINCT, 9, row));
    }

    /* Colunas: distinct. */
    for (int j = 0; j < 9; j++) {
        Cvc5Term col[9];
        for (int i = 0; i < 9; i++) col[i] = c[i][j];
        cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_DISTINCT, 9, col));
    }

    /* Blocos 3x3: distinct. */
    for (int bi = 0; bi < 3; bi++) {
        for (int bj = 0; bj < 3; bj++) {
            Cvc5Term block[9];
            int k = 0;
            for (int di = 0; di < 3; di++) {
                for (int dj = 0; dj < 3; dj++) {
                    block[k++] = c[3*bi + di][3*bj + dj];
                }
            }
            cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_DISTINCT, 9, block));
        }
    }

    /* Pistas iniciais. */
    if (strlen(PUZZLE) != 81) {
        fprintf(stderr, "puzzle deve ter 81 caracteres\n");
        return 1;
    }
    for (int k = 0; k < 81; k++) {
        char ch = PUZZLE[k];
        if (ch >= '1' && ch <= '9') {
            int i = k / 9, j = k % 9;
            Cvc5Term clue = cvc5_mk_integer_int64(tm, ch - '0');
            cvc5_assert_formula(slv, cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2,
                                                  (Cvc5Term[]){c[i][j], clue}));
        }
    }

    Cvc5Result r = cvc5_check_sat(slv);
    printf("cvc5: %s\n\n", cvc5_result_to_string(r));

    if (cvc5_result_is_sat(r)) {
        for (int i = 0; i < 9; i++) {
            if (i > 0 && i % 3 == 0) printf("------+-------+------\n");
            for (int j = 0; j < 9; j++) {
                if (j > 0 && j % 3 == 0) printf("| ");
                Cvc5Term v = cvc5_get_value(slv, c[i][j]);
                int64_t val = cvc5_term_get_int64_value(v);
                printf("%ld ", (long) val);
            }
            printf("\n");
        }
    }

    cvc5_delete(slv);
    cvc5_term_manager_delete(tm);
    return 0;
}
