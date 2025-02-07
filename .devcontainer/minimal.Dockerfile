# This file is used to build the steel-devcontainer image which we
# routinely push to DockerHub. It will not be rebuilt by rebuilding only
# the devcontainer. An alternative is replacing the "image" field in
# the devcontainer with a "build" field, but that would make everyone
# rebuild the container (and FStar, and Pulse) everytime, which is very
# expensive.

FROM ocaml/opam:debian-11-ocaml-4.14

USER root

RUN apt-get update \
    && apt-get install -y --no-install-recommends \
      libgmp-dev \
      pkg-config \
      python3 \
      python-is-python3 \
    && apt-get clean -y

RUN opam update -y && opam pin -y fstar --dev-repo && opam install z3 -y && opam clean -y -a -c -s --logs

# ENV FSTAR_HOME $HOME/FStar
