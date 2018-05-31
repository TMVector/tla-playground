# Referencing Variables Through Case Statements

What I dislike here is that TLC requires that variables are "defined" in order to use a case expression.
A lot of my gripes with TLC are to do with "undefined or not an operator" error messages.


```
---- MODULE Experiment ----

VARIABLES varA
        , varB

vars == << varA, varB >>

Names == { "A", "B" }

(***************************************************************************)
(* Grab a variable by name -- using a case                                 *)
(***************************************************************************)
Var(name) == CASE name = "A" -> varA
               [] name = "B" -> varB


-----------------------------------------------------------------------------

(***************************************************************************)
(*                                                                         *)
(*   Spec1 : Use Var(_) to initialise variables                            *)
(*                                                                         *)
(*   This causes an error:                                                 *)
(*     In evaluation, the identifier varA is either undefined or not an operator. *)
(*     line 20, col 33 to line 20, col 36 of module Experiment             *)
(*                                                                         *)
(***************************************************************************)
Init1 == \A name \in Names :
           Var(name) = FALSE

Next1 == \/ \E name \in Names :
              /\ Var(name) = FALSE
              /\ Var(name)' = TRUE
              /\ \A uname \in Names \ {name} : UNCHANGED Var(uname)
         \/ UNCHANGED vars

Spec1 == Init1 /\ [][Next1]_vars


-----------------------------------------------------------------------------

(***************************************************************************)
(*                                                                         *)
(*   Spec2 : Use Var(_) to initialise variables after membership assertion *)
(*                                                                         *)
(*   This causes an error:                                                 *)
(*     In evaluation, the identifier varA is either undefined or not an operator. *)
(*     line 59, col 17 to line 59, col 20 of module Experiment             *)
(*                                                                         *)
(***************************************************************************)

WellTyped == /\ varA \in BOOLEAN
             /\ varB \in BOOLEAN

Init2 == /\ WellTyped
         /\ \A name \in Names :
              Var(name) = FALSE

Next2 == \/ /\ WellTyped'
            /\ \E name \in Names :
                /\ Var(name) = FALSE
                /\ Var(name)' = TRUE
                /\ \A uname \in Names \ {name} : UNCHANGED Var(uname)
         \/ UNCHANGED vars

Spec2 == Init2 /\ [][Next2]_vars


-----------------------------------------------------------------------------

(***************************************************************************)
(*                                                                         *)
(*   Spec3 : Use Var(_) to initialise variables after membership assertion *)
(*           and use a copy of WellTyped which is manually ticked in Next  *)
(*                                                                         *)
(*   This WORKS                                                            *)
(*                                                                         *)
(*                                                                         *)
(***************************************************************************)

WellTypedFuture == /\ varA' \in BOOLEAN
                   /\ varB' \in BOOLEAN

Init3 == /\ WellTyped
         /\ \A name \in Names :
              Var(name) = FALSE

Next3 == \/ /\ WellTypedFuture
            /\ \E name \in Names :
                /\ Var(name) = FALSE
                /\ Var(name)' = TRUE
                /\ \A uname \in Names \ {name} : UNCHANGED Var(uname)
         \/ UNCHANGED vars

Spec3 == Init3 /\ [][Next3]_vars


-----------------------------------------------------------------------------

(***************************************************************************)
(*                                                                         *)
(*   Spec4 : Spec3, but with Nat domains                                   *)
(*                                                                         *)
(*   This causes an error:                                                 *)
(*     In computing initial states, the right side of \IN is not enumerable. *)
(*     line 119, col 18 to line 119, col 29 of module Experiment           *)
(*                                                                         *)
(***************************************************************************)

LOCAL INSTANCE Naturals

WellTyped4 == /\ varA \in Nat
              /\ varB \in Nat

WellTypedFuture4 == /\ varA' \in Nat
                    /\ varB' \in Nat

Init4 == /\ WellTyped4
         /\ \A name \in Names :
              Var(name) = 0

Next4 == \/ /\ WellTypedFuture4
            /\ \E name \in Names :
                /\ Var(name) = 0
                /\ Var(name)' = 1
                /\ \A uname \in Names \ {name} : UNCHANGED Var(uname)
         \/ UNCHANGED vars

Spec4 == Init4 /\ [][Next4]_vars

================
```