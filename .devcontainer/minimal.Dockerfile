# This file is used to build the steel-devcontainer image which we
# routinely push to DockerHub. It will not be rebuilt by rebuilding only
# the devcontainer. An alternative is replacing the "image" field in
# the devcontainer with a "build" field, but that would make everyone
# rebuild the container (and FStar, and Pulse) everytime, which is very
# expensive.

FROM ocaml/opam:debian-11-ocaml-4.14

RUN /bin/bash --login -o pipefail -c opam update -y && opam pin -y fstar z3 --dev-repo && opam clean -y -a -c -s --logs && eval $(opam env)
