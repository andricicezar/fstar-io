#!/bin/bash

set -eux

ssh -p 5555 artifact@localhost 'rm -f *; rm -f .bash_history ; rm -rf secrefstar'

make -C .. package

scp -P 5555 README.md ../artifact.tar.gz artifact@localhost:

echo 'Done!'
