#!/bin/sh

make
(cd drat-trim; make)
(cd cadical; ./configure && make)
(cd check-sat; sh build.sh)
(cd proximity; g++ --std=c++11 main.cpp -o proximity )
