#!/bin/bash

make all

# Would also work:
# ./reduce

time ./reduce unavoidable.conf

# Would also work:
# ./disharge present7
# ./disharge present8
# ./disharge present9
# ./disharge present10
# ./disharge present11

time ./discharge present7 unavoidable.conf rules
time ./discharge present8 unavoidable.conf rules
time ./discharge present9 unavoidable.conf rules
time ./discharge present10 unavoidable.conf rules
time ./discharge present11 unavoidable.conf rules

rm -f outlet.et

make clean
