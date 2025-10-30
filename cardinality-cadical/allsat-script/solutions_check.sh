#!/bin/bash

# Input : Formula, List of Solutions, Checking Script


# For a formula encoding.knf, run with : 
#  ./allsat encoding.knf --printsolutions > temp_solutions.sol 
#  sh solutions_check.sh encoding.knf temp_solutions.sol ../../Tools/check-sat/check-sat 


FORMULA="$1"
SOLUTIONS_FILE="$2"
CHECK_SCRIPT="$3"

if [[ -z "$FORMULA" || -z "$SOLUTIONS_FILE" || -z "$CHECK_SCRIPT" ]]; then
    echo "Usage: $0 <formula> <solutions_file> <check_script>"
    exit 1
fi

# loop over each solution line that starts with a "v "
COUNTER=0
while IFS= read -r line; do
    if [[ $line == v* ]]; then
        # Extract the solution part (remove the leading 'v ')
        # SOLUTION="${line:2}"
        SOLUTION=temp.sol
        echo "$line" > $SOLUTION
        
        # Run the checking script with the formula and solution
        ./"$CHECK_SCRIPT" "$FORMULA" "$SOLUTION" > temp_check_output.txt 2>&1

        # cat temp_check_output.txt
        
        # Capture the exit status of the checking script
        STATUS=$(grep -q "c VERIFIED SATISFIABLE" temp_check_output.txt; echo $?)
        
        if [[ $STATUS -eq 0 ]]; then
            echo "Solution $COUNTER is valid"
        else
            echo "Solution $COUNTER is invalid"
            cat temp_check_output.txt
        fi
      ((COUNTER++))
    fi
    
done < "$SOLUTIONS_FILE"