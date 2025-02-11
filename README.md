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

To interact with the elliptic curve defined in this system, you will need to run the Coq file that defines the elliptic curve and its operations. Follow the steps below to execute the file:

1. **Install Coq**: Ensure you have Coq installed. You can download it from [Coq's official website](https://coq.inria.fr/).

2. **Set up the Coq Environment**:
   - To run the Coq file, you will use `coqtop` (Coq's interactive shell) or `make` commands.

3. **Running the Coq File**:
   - If you are using `coqtop`, start it by running the following command in your terminal:
     ```bash
     coqtop
     ```
   - Once inside the Coq environment, load the necessary libraries and your Coq file:
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
   - Alternatively, if you are using `make`, create a `Makefile` to automate the build process. Here's an example of a simple Makefile:
     ```makefile
     .PHONY: all
     all:
         coqtop < your_file.v
     ```
     To run the file using `make`, simply run:
     ```bash
     make
     ```

4. **Interacting with the Curve**:
   - The elliptic curve operations, including addition, subtraction, and scalar multiplication, are defined in the Coq file. To add points, multiply them, or compute modular operations, you can invoke the corresponding functions directly within the Coq environment:
     ```coq
     (* Example usage *)
     Eval compute in point_add (Point 2 3) (Point 5 6).
     Eval compute in scalar_mult 5 (Point 2 3).
     ```
   - The `point_add` function adds two points on the elliptic curve, while `scalar_mult` performs scalar multiplication.

5. **Verifying Properties**:
   - You can also verify the properties of the curve, such as the non-singularity condition or the behavior of the modular arithmetic operations. For example:
     ```coq
     Axiom non_singular : mod_add (mod_mul 4 (mod_mul a (mod_mul a a))) (mod_mul 27 (mod_mul b b)) <> 0.
     ```

This setup allows you to interact with the elliptic curve, perform operations, and verify key properties essential for the ECDSA security assumptions in ECCIC256.
