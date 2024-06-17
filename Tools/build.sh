#!/bin/sh

make
(cd drat-trim; make)
(cd cadical; ./configure && make)
(cd check-sat; sh build.sh)
