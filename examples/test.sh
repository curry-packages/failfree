#!/bin/sh
# Script to test the set of current examples

VERBOSE=no
if [ "$1" = "-v" ] ; then
  VERBOSE=yes
fi

# Tool options:
OPTS=--contract

/bin/rm -rf .curry
ECODE=0
FAILEDTESTS=

for p in *.curry ; do
  if [ $VERBOSE = yes ] ; then
    curry-nonfail $OPTS $p | tee test.out
  else
    curry-nonfail $OPTS $p > test.out
  fi
  if [ "`tail -1 test.out`" != "NON-FAILURE VERIFICATION SUCCESSFUL!" ] ; then
    echo "$p: FULL VERIFICATION FAILED!"
    FAILEDTESTS="$FAILEDTESTS $p"
    ECODE=1
  fi
  rm test.out
done
if [ $ECODE -gt 0 ] ; then
  echo "FAILURES OCCCURRED IN SOME TESTS:$FAILEDTESTS"
  exit $ECODE
elif [ $VERBOSE = yes ] ; then
  echo "All tests successfully executed!"
fi
