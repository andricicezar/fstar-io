#!/bin/bash

set -eux

# Cache off since we pull from upstream branches that change
docker build --no-cache -f .devcontainer/minimal.Dockerfile -t mtzguido/steel-devcontainer .

docker push mtzguido/steel-devcontainer
