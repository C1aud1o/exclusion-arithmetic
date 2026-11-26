# Optional C accelerator.  `make` builds with OpenMP; `make OPENMP=` without.
CC      ?= cc
OPENMP  ?= -fopenmp
CFLAGS  ?= -std=c11 -O3 -Wall -Wextra

count_composites: count_composites.c
	$(CC) $(CFLAGS) $(OPENMP) $< -o $@

clean:
	rm -f count_composites

.PHONY: clean
