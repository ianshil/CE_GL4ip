Require Import GL4ip_cut_elim.

Require Import Extraction.
Extraction Language Haskell.

(*
Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInt.
*)

Unset Extraction Optimize.

(* Time Separate Extraction GL4ip_cut_elimination.*)
Extraction "/Users/IanShillito/CoqForm/lol.hs" GL4ip_cut_elimination.

Print Assumptions GL4ip_cut_elimination.