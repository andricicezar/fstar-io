FROM ocaml/opam:ubuntu-20.04-ocaml-4.12

RUN sudo apt-get update
RUN sudo apt-get install -qq -yy g++ libgmp-dev m4 python2.7 telnet
RUN opam depext conf-gmp z3.4.8.5 conf-m4

RUN opam pin -j 12 add fstar https://github.com/FStarLang/FStar/archive/refs/tags/v2023.09.03.tar.gz

RUN eval $(opam env)
COPY . sciostar/.
RUN sudo chown -R opam:opam sciostar
WORKDIR /home/opam/sciostar
RUN rm -rf .cache .depend.mk case-studies/webserver/.cache case-studies/webserver/.depend.mk
CMD /bin/bash