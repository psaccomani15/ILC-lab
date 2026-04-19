CC       ?= gcc
CFLAGS   ?= -O2 -Wall -Wextra -std=c11
LDLIBS   ?= -lcvc5

# Em algumas instalacoes (ex. Fedora), libcvc5 fica em /usr/local/lib64
# e nao esta no ld.so cache por padrao.  Descomentar se necessario:
LDFLAGS += -L/usr/local/lib64 -Wl,-rpath,/usr/local/lib64

PROGS = hello predicados nqueens_bool nqueens_int sudoku_bool sudoku_int send_more_money

all: $(PROGS)

%: %.c
	$(CC) $(CFLAGS) $(LDFLAGS) $< -o $@ $(LDLIBS)

run-hello: hello
	LD_LIBRARY_PATH=/usr/local/lib64:$$LD_LIBRARY_PATH ./hello

clean:
	rm -f $(PROGS)

.PHONY: all clean run-hello
