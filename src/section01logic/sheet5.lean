/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `refl`
* `rw`

-/

variables (P Q R S : Prop)

example : P ↔ P :=
begin
refl,
end

example : (P ↔ Q) → (Q ↔ P) :=
begin
intro q,rw q,
end

example : (P ↔ Q) ↔ (Q ↔ P) :=
begin
  split,intro q, rw q,intro q,rw q,
end

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
  intros q w,
  rwa q, 
end

example : P ∧ Q ↔ Q ∧ P :=
begin
  split;
  {rintro ⟨q, w⟩,exact ⟨w, q⟩
  }
end

example : ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R)) :=
begin
  split,intro q,cases q,cases q_left,split,assumption,split,assumption,assumption,
  intro q,cases q,cases q_right,split,split,assumption,assumption,assumption,
end

example : P ↔ (P ∧ true) :=
begin
  split,
  {intro q,split,assumption,triv,},
  {intro q,cases q,assumption,}
end

example : false ↔ (P ∧ false) :=
begin
  split,
  {intro q,split,by_contra,triv,triv,},
  {intro q,cases q, assumption}
end

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) :=
begin
  intros q w,split,
  {intro e,split,cases q,apply q_mp,cases e,assumption,cases w,apply w_mp,cases e,assumption,},
  {intro e,split,cases q,apply q_mpr,cases e,assumption,cases w,cases e,apply w_mpr,assumption,},
end

example : ¬ (P ↔ ¬ P) :=
begin
intro q,cases q,change (P->(P->false)) at q_mp,apply q_mp,apply q_mpr,change P ->false,intro e,apply q_mp,assumption,assumption,apply q_mpr,change P->false,intro q, apply q_mp,exact q,exact q,
end
