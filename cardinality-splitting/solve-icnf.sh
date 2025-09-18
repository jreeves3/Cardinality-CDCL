#! /bin/bash

ICNF=$1
SPLIT=$2
SOLVER=$3
TIMEOUT=1800

# if fourth argument is given, use as timeout
if [ ! -z "$4" ]; then TIMEOUT=$4; fi


ICNF_SOLVE=../../scripts/split-and-solve-icnf.sh

TMPFOLDER=tmp/`basename $ICNF .icnf`-cubes
mkdir -p $TMPFOLDER

cp $ICNF $TMPFOLDER

cd $TMPFOLDER

sh $ICNF_SOLVE $ICNF $SPLIT $SOLVER $TIMEOUT > tmp.log 2>&1

wait

echo "c Cube Runtimes"

cat tmp.log

echo "c Sum"
cat tmp.log | awk 'BEGIN{s=0;i=0} /SAT/ {s=s+$4;i=i+1} END{print s" "s/i" "i}'

cat tmp.log | sort -n -k 4

nUNSAT=`cat tmp.log | grep -c "UNSAT"`

# number expected is 2 to power number of cubes
nExpected=$((2**nCubes))
if [ "$nUNSAT" -eq "$nExpected" ]; then
  echo "c UNSAT"
else 
  echo "c Failed Cubes"
fi

# Remove temporary folder
# cd ../../
# rm -r $TMPFOLDER