
echo "\nTEST: Bad Header"
./../../../check-sat badHeader.knf satAssignment1.txt

echo "\nTEST: Out of bounds variable"
./../../../check-sat outOfBoundsVar.knf satAssignment1.txt

echo "\nTEST: Partial assignment"
./../../../check-sat test1.knf partialAssignment1.txt

echo "\nTEST: SAT assignment"
./../../../check-sat test1.knf satAssignment1.txt