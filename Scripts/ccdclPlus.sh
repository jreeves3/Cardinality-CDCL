#!bin/bash

#!bin/bash

DERIVATION=Tools/derivation
CHECK=Tools/check-sat/check-sat
PROCESSASS=Tools/process-assignment.py
CCDCL="cardinality-cadical/build/cadical"
CADICAL="Tools/cadical/build/cadical"
DRAT="Tools/drat-trim/drat-trim"
KNF2CNF="Tools/knf2cnf"
KONLY="Tools/konly"
EXTRACTOR="Extractor/cnf2knf/src/cnf2knf"

# tmp directory for output files
TMP=tmp
mkdir $TMP
TIMEOUT=5000

INPUTFORMULA=$1
PROOFCHECKING=$2


## Option CNF or KNF input
if [  "${INPUTFORMULA: -4}" == ".cnf" ]
then # CNF input formula

  # Propagate any units in the formula
  ./$CADICAL $INPUTFORMULA -c 0 -f -o $TMP/prop.cnf > /dev/null

  echo "Start Extraction"

  ./$EXTRACTOR $TMP/prop.cnf > $TMP/extracted.knf

  INPUTKNF=$TMP/extracted.knf

  grep "^c" $INPUTKNF

  echo "End Extraction"

  AUX=$(grep "p knf" $INPUTKNF | awk '{print $3}')

  ./$KONLY $TMP/extracted.knf > $TMP/encode.cnf

  cat $TMP/extracted.knf $TMP/encode.cnf > $TMP/full.knf

  VAR=$(grep "p cnf" $TMP/encode.cnf | awk '{print $3}')
  CLS1=$(grep "p cnf" $TMP/encode.cnf | awk '{print $4}')
  CLS2=$(grep "p knf" $TMP/extracted.knf | awk '{print $4}')
  grep -v "p cnf \|p knf" $TMP/full.knf > $TMP/full-nohead.knf
  CLS=$(($CLS1+$CLS2))
  printf 'p knf %s %s\n' "$VAR $CLS" > $TMP/temp1.txt
  cat $TMP/temp1.txt $TMP/full-nohead.knf > $TMP/full.knf
  rm $TMP/temp1.txt $TMP/full-nohead.knf

  echo "Start Cadical"

  # Run cadical on the propagated CNF, with a 5000 second timeout
  ./$CCDCL $TMP/full.knf -t $TIMEOUT $TMP/solve.drat --no-binary --ccdclMode=1  --ccdclAuxCut=$AUX --ccdclStabLim=1  > $TMP/cadical.out

  echo "End Cadical"

  # Output solver runtime information
  cat $TMP/cadical.out

  # Check the proof
  if [ $PROOFCHECKING -gt 0 ]
  then 

    # Check if formula was satisfiable or unsatisfiable
    p=$(grep "s SATISFIABLE" $TMP/cadical.out | wc | awk '{print  $1}')
      
    if [ $p -gt 0 ]
    then
      # SAT case
      echo "Start SAT Checking"

      ./$CCDCL $INPUTFORMULA -c 0 --printUnits=1 > $TMP/prop.out

      # get units from assignment
      grep "^v " $TMP/cadical.out | tr " " "\n"  | grep -v -e "v" -e "^0" | awk '{print $1" 0"}' > $TMP/tmp-assignment-units.out
      
      # check if any variables were eliminated
      head -n 30 $INPUTKNF | grep "c Eliminated variables IDs:" | tr " " "\n"  | grep -v -e "c" -e "Eliminated" -e "variables" -e "IDs:" > $TMP/eliminatedVars.txt

      grep "Eliminated Variables " $TMP/prop.out | tr " " "\n" | grep -v -e "Eliminated" -e "Variables" > $TMP/EliminatedUnits.txt

      cat $TMP/EliminatedUnits.txt >> $TMP/eliminatedVars.txt
      
      p=$( wc $TMP/eliminatedVars.txt | awk '{print  $1}')
      if [ $p -gt 0 ]
      then # remove eliminated encoding variables from the assignment
        python3 $PROCESSASS -i $TMP/tmp-assignment-units.out -e $TMP/eliminatedVars.txt -o $TMP/assignment-units.out
      else # no encoding variables eliminated
        mv $TMP/tmp-assignment-units.out $TMP/assignment-units.out
      fi
      
      # add units to original CNF formula
      cat $INPUTFORMULA $TMP/assignment-units.out > $TMP/cnf-with-units.cnf
      # check by running cadical with units
      ./$CADICAL -f $TMP/cnf-with-units.cnf > $TMP/sat-check.out
      
      # if cadical returns satisfiable, units satisfied formula
      p=$(grep "s SATISFIABLE" $TMP/sat-check.out | wc | awk '{print  $1}')
      if [ $p -gt 0 ]
      then
        echo "Verified SAT by propagating assignment on reencoded formula"
      fi
      echo "End SAT Checking"
        
    else
      p=$(grep "s UNSATISFIABLE" $TMP/cadical.out | wc | awk '{print  $1}')
      if [ $p -gt 0 ]
      then
        # UNSAT case
        echo "Start UNSAT Checking"
        ./$DERIVATION $INPUTKNF > $TMP/deriv.drat

        cat $TMP/deriv.drat $TMP/solve.drat > $TMP/proof.drat

        ./$DRAT $INPUTFORMULA $TMP/proof.drat > $TMP/drat-check.out
        # cat $TMP/drat-check.out | grep -v "WARNING"
        
        p=$(grep "s VERIFIED" $TMP/drat-check.out | wc | awk '{print  $1}')
        if [ $p -gt 0 ]
        then
          echo "Verfied UNSAT with drat-trim on original formula"
        fi

        echo "End UNSAT Checking"
      else
        # Uknown case
        echo "Incomplete, Value Unknown"
      fi
    fi
  fi
    
else # KNF input formula

  AUX=$(grep "p knf" $INPUTFORMULA | awk '{print $3}')

  ./$KONLY $INPUTFORMULA > $TMP/encode.cnf

  cat $INPUTFORMULA $TMP/encode.cnf > $TMP/full.knf

  VAR=$(grep "p cnf" $TMP/encode.cnf | awk '{print $3}')
  CLS1=$(grep "p cnf" $TMP/encode.cnf | awk '{print $4}')
  CLS2=$(grep "p knf" $INPUTFORMULA | awk '{print $4}')
  grep -v "p cnf \|p knf" $TMP/full.knf > $TMP/full-nohead.knf
  CLS=$(($CLS1+$CLS2))
  printf 'p knf %s %s\n' "$VAR $CLS" > $TMP/temp1.txt
  cat $TMP/temp1.txt $TMP/full-nohead.knf > $TMP/full.knf
  rm $TMP/temp1.txt $TMP/full-nohead.knf

  echo "Start Cadical"

  # Run cadical on the propagated CNF, with a 5000 second timeout
  ./$CCDCL $TMP/full.knf -t $TIMEOUT $TMP/solve.drat --no-binary --ccdclMode=1  --ccdclAuxCut=$AUX --ccdclStabLim=1  > $TMP/cadical.out

  echo "End Cadical"

  # Output solver runtime information
  cat $TMP/cadical.out

  # Check the proof
  if [ $PROOFCHECKING -gt 0 ]
  then 

    # Check if formula was satisfiable or unsatisfiable
    p=$(grep "s SATISFIABLE" $TMP/cadical.out | wc | awk '{print  $1}')
      
    if [ $p -gt 0 ]
    then
      # SAT case
      echo "Start SAT Checking"
      
      grep "^v " $TMP/cadical.out > $TMP/orig_solve.sol
      ./$CHECK $INPUTFORMULA $TMP/orig_solve.sol
    else
      p=$(grep "s UNSATISFIABLE" $TMP/cadical.out | wc | awk '{print  $1}')
      if [ $p -gt 0 ]
      then
      # UNSAT case
        echo "Start UNSAT Checking"

        ./$KNF2CNF $INPUTFORMULA > $TMP/encoded.cnf
        ./$DERIVATION $INPUTKNF > $TMP/deriv.drat

        cat $TMP/deriv.drat $TMP/solve.drat > $TMP/proof.drat

        ./$DRAT $TMP/encoded.cnf $TMP/proof.drat > $TMP/drat-check.out
        # cat $TMP/drat-check.out | grep -v "WARNING"
        
        p=$(grep "s VERIFIED" $TMP/drat-check.out | wc | awk '{print  $1}')
        if [ $p -gt 0 ]
        then
          echo "Verfied UNSAT with drat-trim on reencoded formula"
        fi

        echo "End UNSAT Checking"
      else
        # Uknown case
        echo "Incomplete, Value Unknown"
      fi
    fi
  fi
fi
