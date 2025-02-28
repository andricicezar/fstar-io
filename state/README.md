## SecRef★: Securely Sharing Mutable References Between Verified and Unverified Code in F★

This directory contains the artifact for SecRef★. The layour is as
follows:
- MST.Tot
- MST.Repr
- Examples.*
- misc/: dune configuration files for examples

- fstar-patches/: a set of patches needed for F*, to enable primitive
  extraction of reifiable effects (and fix two bugs).

- extraction/: The extraction plugin for SecRef★. Run `make` inside
  here to build it. It will also be built automatically by the `build-%`
  rule, but *not* rebuilt, so do it manually if you've changed anything
  here or if F* has changed.

You need F* version 2025.02.17 **with the patches** to run this artifact.
A way to get set up is:

  git clone https://github.com/FStarLang/FStar
  cd FStar
  git co v2025.02.17
  git am /path/to/artifact/fstar-patches/*.patch
  opam install --deps-only .
  make -j$(nproc) ADMIT=1

After a while, a built F* should be avaiable under in `FStar/bin/fstar.exe`. Add
this directory to your PATH and then run the Makefile here.

You also need Z3 version 4.13.3 in your PATH, named z3-4.13.3 so F* can find it.
The script in `FStar/.scripts/get_fstar_z3.sh` can be used to automatically set it up

  ./FStar/.scripts/get_fstar_z3.sh ~/bin

Should install z3-4.13.3 into your ~/bin (and Z3 4.8.5, though we do not use it).
