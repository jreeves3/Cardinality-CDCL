#!/bin/sh

mkdir tmp
(cd tools; make)
(cd cadical; ./configure && make)
(cd cardinality-cadical; ./configure && make)
(cd drat-trim; make)
