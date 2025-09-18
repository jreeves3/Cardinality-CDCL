ICNF=$1
BASE=${ICNF%.*}
SPLIT=$2
SOLVER=$3
TIMEOUT=$4

SOLVERASSUME=../../scripts/solve-assume.sh

for (( i=0; i<$SPLIT; i++ ))
do
  cat $ICNF | awk 'BEGIN{l=1} !/a / {print $0} /a / {if ((l % '$SPLIT') == '$i') print $0; l=l+1}' > $BASE-x$i.icnf
done

for (( i=0; i<$SPLIT; i++ ))
do
  INIT=$i
  if [ "$INIT" -eq "0" ]; then INIT=$SPLIT; fi
  sh $SOLVERASSUME $BASE-x$i.icnf $INIT $SPLIT $SOLVER $TIMEOUT &
done
wait