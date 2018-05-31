# Referencing Variables Through Case Statements

What I dislike here is that TLC requires that variables are "defined" in order to use a case expression.
A lot of my gripes with TLC are to do with "undefined or not an operator" error messages.


```
---- MODULE Experiment ----

VARIABLES numA
        , numB

vars == << numA, numB >>

Names == { "A", "B" }

(***************************************************************************)
(* Grab a variable by name -- using a case                                 *)
(***************************************************************************)
Var(name) == CASE name = "A" -> numA
               [] name = "B" -> numB

(***************************************************************************)
(*                                                                         *)
(*   Initialise all variables (by name) to the same value                  *)
(*                                                                         *)
(*   This causes an error:                                                 *)
(*     In evaluation, the identifier numA is either undefined or not an operator. *)
(*     line 20, col 33 to line 20, col 36 of module Experiment             *)
(*                                                                         *)
(*                                                                         *)
(***************************************************************************)
Init == \A name \in Names :
          Var(name) = FALSE

Next == \/ \E name \in Names :
            /\ Var(name) = FALSE
            /\ Var(name)' = TRUE
        \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

================
```