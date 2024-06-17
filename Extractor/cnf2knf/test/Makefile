INTERP = python3
TOOLDIR = ../../tools
K2C = $(TOOLDIR)/knf2cnf
TBUDDYDIR = ../tbuddy
C2KK = $(TBUDDYDIR)/ktest
GEN = genknf.py
VERB=1

N=5
NMAX=$(N)
NMIN=0

k: k$(N)-$(NMAX)-$(NMIN).knf k$(N)-$(NMAX)-$(NMIN).cnf k$(N)-$(NMAX)-$(NMIN).kknf

k$(N)-$(NMAX)-$(NMIN).knf: $(GEN)
	$(INTERP) $(GEN) $(N) $(NMAX) $(NMIN) > k$(N)-$(NMAX)-$(NMIN).knf

.SUFFIXES: .knf .cnf .kknf

.knf.cnf:
	$(K2C) $< > $@

.cnf.kknf:
	$(C2KK) -v $(VERB) $(N) $< | tee $@

