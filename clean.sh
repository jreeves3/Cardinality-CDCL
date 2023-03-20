#!/bin/sh
rm -r tmp
(cd tools; make clean)
(cd cadical; make clean)
(cd cardinality-cadical; make clean)
(cd drat-trim; make clean)
