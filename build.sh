#!/bin/sh

mkdir tmp
(cd cardinality-cadical; ./configure && make)
(cd Extractor/cnf2knf; sh build.sh)
(cd Tools; sh build.sh)
