#!/bin/bash

set -euo pipefail

git config --global --add safe.directory /workspace
git config --global user.email $GIT_EMAIL 
git config --global user.name $GIT_USER_NAME 

ln -s /workspace/.github /workspace/.claude

echo "alias mycc='claude --dangerously-skip-permissions'" >> ~/.bashrc
echo "alias myco='copilot --yolo --model claude-opus-4.6'" >> ~/.bashrc
echo "alias mygem='gemini --yolo'" >> ~/.bashrc

rm -rf /workspace/seiostar/.build

exec "$@"
