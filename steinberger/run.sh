#!/bin/bash

make all

time ./reduce U_2822.conf

time ./discharge p5_2822 U_2822.conf L_42
time ./discharge p6_2822 U_2822.conf L_42
time ./discharge p7_2822 U_2822.conf L_42
time ./discharge p8_2822 U_2822.conf L_42
time ./discharge p9_2822 U_2822.conf L_42
time ./discharge p10_2822 U_2822.conf L_42
time ./discharge p11_2822 U_2822.conf L_42

make clean

rm -f outlet.et
