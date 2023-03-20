#!/bin/sh

## Option CNF or KNF input
if [  "${1: -4}" == ".cnf" ]
then # CNF input formula

  # Propagate any units in the formula
  ./tools/cleanup-small $1 > tmp/propagated.cnf
  
  # Permute propagated formula
  python3 tools/permute.py -c tmp/propagated.cnf -o tmp/permuted.cnf

  echo "Start Cardinality"

  # Extract cardinality constraints
  #   1,000 second timeout for direct and 1,000 timeout for encoded constraints
  python3 tools/card_extractor.py -i tmp/propagated.cnf -T 1000 -o tmp/card.knf

  echo "End Cardinality"

  # Output cardinality extraction stats
  head -n 30 tmp/card.knf

  # Permute extracted KNF
  python3 tools/permute.py -c tmp/card.knf -o tmp/permuted.knf

  echo "Start Cadical"
  
  # Run cardinality cadical on the permuted KNF, with a 5000 second timeout
  ./cardinality-cadical/build/cadical tmp/permuted.knf tmp/solve.drat --no-binary -t 5000 > tmp/cadical.out

  echo "End Cadical"

  # Output solver runtime information
  cat tmp/cadical.out

  # Check if formula was satisfiable or unsatisfiable
  p=$(grep "s SATISFIABLE" tmp/cadical.out | wc | awk '{print  $1}')
    
  if [ $p -gt 0 ]
  then
    # SAT case
    echo "Start SAT Checking"
    
    # get units from assignment
    grep "^v " tmp/cadical.out | tr " " "\n"  | grep -v -e "v" -e "^0" | awk '{print $1" 0"}' > tmp/tmp-assignment-units.out
    
    # check if any variables were eliminated
    head -n 30 tmp/card.knf | grep "c Eliminated variables IDs:" | tr " " "\n"  | grep -v -e "c" -e "Eliminated" -e "variables" -e "IDs:" > tmp/eliminatedVars.txt
    
    p=$( wc tmp/eliminatedVars.txt | awk '{print  $1}')
    if [ $p -gt 0 ]
    then # remove eliminated encoding variables from the assignment
      python3 tools/process-assignment.py -i tmp/tmp-assignment-units.out -e tmp/eliminatedVars.txt -o tmp/assignment-units.out
    else # no encoding variables eliminated
      mv tmp/tmp-assignment-units.out tmp/assignment-units.out
    fi
      
    # add units to original CNF formula
    cat $1 tmp/assignment-units.out > tmp/cnf-with-units.cnf
    # check by running cadical with units
    ./cadical/build/cadical -f tmp/cnf-with-units.cnf > tmp/sat-check.out
    
    # if cadical returns satisfiable, units satisfied formula
    p=$(grep "s SATISFIABLE" tmp/sat-check.out | wc | awk '{print  $1}')
    if [ $p -gt 0 ]
    then
      echo "Verified SAT by propagating assignment on original formula"
    fi
    echo "End SAT Checking"
  else
    p=$(grep "s UNSATISFIABLE" tmp/cadical.out | wc | awk '{print  $1}')
    if [ $p -gt 0 ]
    then
    # UNSAT case
      echo "Start UNSAT Checking"

      echo "Start Drat Checking"
      ./drat-trim/drat-trim $1 tmp/solve.drat > tmp/drat-check.out
      cat tmp/drat-check.out | grep -v "WARNING"
      echo "End Drat Checking"
      
      p=$(grep "s VERIFIED" tmp/drat-check.out | wc | awk '{print  $1}')
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
    
else # KNF input formula

  # Permute input KNF formula
  python3 tools/permute.py -c $1 -o tmp/permuted.knf

  echo "Start Cadical"
  
  # Run cardinality cadical on the permuted KNF, with a 5000 second timeout
  ./cardinality-cadical/build/cadical tmp/permuted.knf tmp/solve.drat --no-binary -t 5000 > tmp/cadical.out

  echo "End Cadical"

  # Output solver runtime information
  cat tmp/cadical.out

  # Check if formula was satisfiable or unsatisfiable
  p=$(grep "s SATISFIABLE" tmp/cadical.out | wc | awk '{print  $1}')
    
  ./tools/knf2cnf $1 > tmp/encoded.cnf
    
  if [ $p -gt 0 ]
  then
    # SAT case
    echo "Start SAT Checking"
    
    # get units from assignment
    grep "^v " tmp/cadical.out | tr " " "\n"  | grep -v -e "v" -e "^0" | awk '{print $1" 0"}' > tmp/assignment-units.out
      
    # add units to original CNF formula
    cat tmp/encoded.cnf tmp/assignment-units.out > tmp/cnf-with-units.cnf
    # check by running cadical with units
    ./cadical/build/cadical -f tmp/cnf-with-units.cnf > tmp/sat-check.out
    
    # if cadical returns satisfiable, units satisfied formula
    p=$(grep "s SATISFIABLE" tmp/sat-check.out | wc | awk '{print  $1}')
    if [ $p -gt 0 ]
    then
      echo "Verified SAT by propagating assignment on reencoded formula"
    fi
    echo "End SAT Checking"
  else
    p=$(grep "s UNSATISFIABLE" tmp/cadical.out | wc | awk '{print  $1}')
    if [ $p -gt 0 ]
    then
    # UNSAT case
      echo "Start UNSAT Checking"

      echo "Start Drat Checking"
      ./drat-trim/drat-trim tmp/encoded.cnf tmp/solve.drat > tmp/drat-check.out
      cat tmp/drat-check.out | grep -v "WARNING"
      echo "End Drat Checking"
      
      p=$(grep "s VERIFIED" tmp/drat-check.out | wc | awk '{print  $1}')
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

