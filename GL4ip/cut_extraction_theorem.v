Require Import GL4ip_cut_elim.

Require Import Extraction.
Extraction Language Haskell.

Unset Extraction Optimize.

Time Separate Extraction GL4ip_cut_elimination.
