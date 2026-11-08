#!/bin/bash
# Install Rocq 9.2 + stdlib, built from source with Ubuntu's OCaml.
# Used by CI and by the cloud environment's setup script (where opam.ocaml.org
# is not reachable, but git clones from GitHub are).
set -euo pipefail
if ! command -v rocq >/dev/null 2>&1 || [ -n "${FORCE_ROCQ_BUILD:-}" ]; then
  export DEBIAN_FRONTEND=noninteractive
  apt-get update -q
  apt-get install -y -q ocaml-nox ocaml-dune libzarith-ocaml-dev ocaml-findlib libfindlib-ocaml-dev
  rm -rf /opt/rocq-src && mkdir -p /opt/rocq-src
  git clone -q --depth 1 -b V9.2.0 https://github.com/rocq-prover/rocq /opt/rocq-src/rocq
  git clone -q --depth 1 -b V9.2.0 https://github.com/rocq-prover/stdlib /opt/rocq-src/stdlib
  cd /opt/rocq-src/rocq
  ./configure -prefix /usr/local
  make dunestrap
  dune build -j "$(nproc)" -p rocq-runtime,coq-core,rocq-core
  dune install --prefix=/usr/local rocq-runtime coq-core rocq-core
  cd /opt/rocq-src/stdlib
  make -j "$(nproc)"
  make install
fi
rocq --version
