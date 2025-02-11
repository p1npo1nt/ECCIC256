# ECCIC256 (Pronounced "Eekick256") -- An ECDLP formal verification system

(NOTE: We will be using the Bartzia-Stub elliptic curve library for ECCIC256 [1])

The goal of ECCIC256 is to provide a manner in which one can formally verify the security assumptions made for ECDSA algorithms such as the unfeasiblity of the discrete logarithm problem.

This package is being built in Coq. We formalize elliptic curves (ECs) over finite fields in Coq. We then provide proofs of algebraic properties ensuring the group structure. Then we outline the definition and verification of ECDLP assumptions.

This project is produced by Vasudevan Govardhanen -- A student of Manalapan High School, Manalapan, NJ. 

## References and tools 
[1] Evmorfia-Iro Bartzia, Pierre-Yves Strub. A Formal Library for Elliptic Curves in the Coq Proof
Assistant. Interactive Theorem Proving, Jul 2014, Vienna, Austria. pp.77-92, ff10.1007/978-3-319-
08970-6_6ff. ffhal-01102288f


## Interacting with the Basic Curve

To interact with the elliptic curve defined in this system, you can use the `Makefile` to automatically compile and run the Coq code. Follow these steps:

1. **Install Coq**: Ensure you have Coq installed. You can download it from [Coq's official website](https://coq.inria.fr/).

2. **Set up the Coq Environment**:
   - Ensure that your Coq project contains the necessary files and libraries, including the elliptic curve definitions.

3. **Using the `Makefile`**:
   - The provided `Makefile` automates the process of compiling and running the Coq code. To use it, open your terminal and navigate to the directory containing the `Makefile`.
   - To compile the Coq code, run the following command:
     ```bash
     make
     ```
   - This will compile all the necessary `.v` files in the `theories` directory and generate `.vo` files.

4. **Interacting with the Curve**:
   - After running the `make` command, the Coq code will be compiled and ready for interaction. You can now run the Coq environment using `coqtop` and load your files as follows:
     ```bash
     coqtop
     ```
     Once inside the Coq environment, load the necessary libraries and your elliptic curve file:
     ```coq
     Require Import ZArith.
     Require Import Znumtheory.
     Require Import Field.
     Require Import Field_theory.
     Require Import Setoid.
     Require Import Bool.Bool.

     Open Scope Z_scope.

     (* Define a prime modulus p and other necessary parameters *)
     Parameter p : Z.
     Axiom p_prime : prime p.

     (* Load and interact with elliptic curve definitions *)
     Require Import ECCIC256.ECC.
     ```

5. **Verifying Properties**:
   - You can now interact with the elliptic curve, perform operations, and verify key properties essential for the ECDSA security assumptions. For example:
     ```coq
     (* Example usage *)
     Eval compute in point_add (Point 2 3) (Point 5 6).
     Eval compute in scalar_mult 5 (Point 2 3).
     ```
   - The `point_add` function adds two points on the elliptic curve, while `scalar_mult` performs scalar multiplication.

6. **Cleaning Up**:
   - If you need to clean up generated files, such as `.vo` and `.glob` files, you can run the following command:
     ```bash
     make clean
     ```

This setup allows you to interact with the elliptic curve, perform operations, and verify important properties of the curve using the Coq environment and the `Makefile`.
