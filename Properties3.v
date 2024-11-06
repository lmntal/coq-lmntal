Require Import String.
Open Scope string_scope.
Require Import List.
Import ListNotations.
Open Scope list_scope.

Require Import ListSet.

From LMNTAL Require Export LMNtalSyntax.
From LMNTAL Require Export LMNtalGraph2.
From LMNTAL Require Export Util.


Theorem congn_iso: forall g1 g2
  normal g1 -> normal g2 -> 
  g1 ==n g2 -> .
