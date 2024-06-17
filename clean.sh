#!/bin/sh
rm -r tmp
(cd Tools; make clean)
(cd Tools/cadical; make clean)
(cd Tools/drat-trim; make clean)
(cd Extractor/cnf2knf; sh clean.sh)
(cd cardinality-cadical; make clean)
rm Tools/check-sat/check-sat
