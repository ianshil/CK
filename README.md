# Rocq library for intuitionistic modal logics between CK and IK

This library gathers results on intuitionistic modal logics, with both diamond and box, between CK and IK.
This far, it contains two distinct project:

- **Semantical Analysis of Intuitionistic Modal Logics between CK and IK:** This project formalises (non-)conservativity results between the intuitionistic modal logics CK and IK, via semantic means (see branch LICS2025). The results of this project were published in [a paper]((https://ieeexplore.ieee.org/document/11186337/) at LICS 2025.
- **Uniform interpolation for CK and WK**: This project formalises terminating calculi for CK and WK, and their exploitation in a proof of uniform interpolation for the two logics (see branch uniform_interpolation).

## Building
Compiling the project requires Rocq version 9.0.0 and may not compile on other versions. One may enforce this locally by running
`opam pin coq 9.0.0` in the project folder.

### Instruction

The proof library compiles with `make all`.
The documentation builds with `make doc`.
