#!/bin/bash

cd akmaxsat_1.1/
make
cp akmaxsat ../
make clean
rm -f akmaxsat

cd ../CCEHC_print_to_akmaxsat/
make
cp CCEHC ../
make cleanup

cd ../CCEHC_to_akmaxsat_source/
make
cp CCEHC_to_akmaxsat ../
make cleanup

