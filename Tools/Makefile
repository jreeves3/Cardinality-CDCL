all: pooled knf2cnf knf2cnf+ pairwise derivation konly

knf2cnf: knf2cnf.c
	gcc knf2cnf.c -DLINEAR -std=c99 -O2 -o knf2cnf
	
pooled: knf2cnf.c
	gcc knf2cnf.c -std=c99 -O2 -o pooled

knf2cnf+: knf2cnf.c
	gcc knf2cnf.c -DLINEAR -DCNFPLUS -std=c99 -O2 -o knf2cnf+

pairwise: knf2cnf.c
	gcc knf2cnf.c -DPAIRWISE -std=c99 -O2 -o pairwise
	
derivation: knf2cnf.c
	gcc knf2cnf.c -DLINEAR -DDERIVATION -std=c99 -O2 -o derivation

konly: knf2cnf.c
	gcc knf2cnf.c -DLINEAR -DKONLY -std=c99 -O2 -o konly

clean:
	rm knf2cnf knf2cnf+ pairwise derivation pooled konly
