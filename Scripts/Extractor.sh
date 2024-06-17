#!bin/bash

CADICAL="Tools/cadical/build/cadical"
EXTRACTOR="Extractor/cnf2knf/src/cnf2knf"

# tmp directory for output files
TMP=tmp
mkdir $TMP
TIMEOUT=5000

INPUTFORMULA=$1
OUTPUTFORMULA=$2

./$CADICAL $INPUTFORMULA -c 0 -f -o $TMP/prop.cnf > /dev/null

echo "Start Extraction"

./$EXTRACTOR $TMP/prop.cnf > $2

INPUTKNF=$2

grep "^c" $INPUTKNF

echo "End Extraction"

