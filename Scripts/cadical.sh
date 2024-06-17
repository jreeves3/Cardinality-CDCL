#!/bin/sh

CADICAL="Tools/cadical/build/cadical"
DRAT="Tools/drat-trim/drat-trim"
KNF2CNF="Tools/knf2cnf"

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

  echo "Start Cadical"

  # Run cadical on the propagated CNF, with a 5000 second timeout
  ./$CADICAL $TMP/prop.cnf $TMP/solve.drat --no-binary -t $TIMEOUT > $TMP/cadical.out

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
      echo "No SAT checking"
    else
      p=$(grep "s UNSATISFIABLE" $TMP/cadical.out | wc | awk '{print  $1}')
      if [ $p -gt 0 ]
      then
        # UNSAT case
        echo "Start UNSAT Checking"
        ./$DRAT $INPUTFORMULA $TMP/solve.drat > $TMP/drat-check.out
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

  ./$KNF2CNF $INPUTFORMULA > $TMP/encoded.cnf

  echo "Start Cadical"
  
  # Run cadical on propagated CNF, with a 5000 second timeout
  ./$CADICAL $TMP/encoded.cnf $TMP/solve.drat --no-binary -t $TIMEOUT > $TMP/cadical.out

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
      
      # get units from assignment
      grep "^v " $TMP/cadical.out | tr " " "\n"  | grep -v -e "v" -e "^0" | awk '{print $1" 0"}' > $TMP/assignment-units.out
        
      # add units to original CNF formula
      cat $TMP/encoded.cnf $TMP/assignment-units.out > $TMP/cnf-with-units.cnf
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

        ./$DRAT $TMP/encoded.cnf $TMP/solve.drat > $TMP/drat-check.out
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

