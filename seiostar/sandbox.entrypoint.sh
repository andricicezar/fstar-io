#!/bin/bash

set -euo pipefail

git config --global --add safe.directory /workspace
git config --global user.email "cezar.andrici@gmail.com"
git config --global user.name "Cezar Andrici"

echo "alias mycc='make verify -j 8 && claude --dangerously-skip-permissions'" > ~/.bashrc

exec "$@"