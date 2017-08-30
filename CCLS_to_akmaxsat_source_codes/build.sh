#!/bin/bash

cd akmaxsat_1.1/
make
cp akmaxsat ../
make clean
rm -f akmaxsat

cd ../CCLS2015_print_to_akmaxsat/
make
cp CCLS2015 ../
make cleanup

cd ../CCLS_to_akmaxsat_source/
make
cp CCLS_to_akmaxsat ../
make cleanup

