# ECCIC256 (Pronounced "Eekick256") -- An ECDLP formal verification system

(NOTE: We will be using the Bartzia-Stub elliptic curve library for ECCIC256 [1])

The goal of ECCIC256 is to provide a manner in which one can formally verify the security assumptions made for ECDSA algorithms such as the unfeasiblity of the discrete logarithm problem.

This package is being built in Coq. We formalize elliptic curves (ECs) over finite fields in Coq. We then provide proofs of algebraic properties ensuring the group structure. Then we outline the definition and verification of ECDLP assumptions.

This project is produced by Vasudevan Govardhanen -- A student of Manalapan High School, Manalapan, NJ. 

## References and tools 
[1] Evmorfia-Iro Bartzia, Pierre-Yves Strub. A Formal Library for Elliptic Curves in the Coq Proof
Assistant. Interactive Theorem Proving, Jul 2014, Vienna, Austria. pp.77-92, ff10.1007/978-3-319-
08970-6_6ff. ffhal-01102288f

