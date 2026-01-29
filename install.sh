#!/bin/sh

opam repo add coq-released https://rocq-prover.org/opam/released "$@"
opam pin rocq-prover 9.0.0 "$@"
opam install rocq-prover coq-stdpp rocq-equations "$@"
