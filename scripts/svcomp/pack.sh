#!/bin/sh

# make it right
ESBMC_SLHV_ROOT="../.."
EXEC_PATH="./exec"

WRAPPER_PATH="./esbmc-slhv-wrapper.py"

mkdir ${EXEC_PATH}

cp ${ESBMC_SLHV_ROOT}/build/src/esbmc/esbmc ${EXEC_PATH}/esbmc_slhv
cp ${WRAPPER_PATH} ${EXEC_PATH}/

zip -r esbmc-slhv.zip ${EXEC_PATH}

rm -r ${EXEC_PATH}