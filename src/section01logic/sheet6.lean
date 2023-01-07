/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases` (new functionality)

-/

-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.

variables (P Q R S : Prop)

example : P → P ∨ Q :=
begin
  intro q,left,assumption,
end

example : Q → P ∨ Q :=
begin
  intro q, right,assumption,
end

example : P ∨ Q → (P → R) → (Q → R) → R :=
begin
  intros q w e,cases q,
  {apply w, assumption},
  {apply e,assumption}, 
end

-- symmetry of `or`
example : P ∨ Q → Q ∨ P :=
begin
  intro q,cases q with w e,right,assumption,left,assumption,
end

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) :=
begin
  split,intro q,cases q with w e,{cases w,{left,assumption,},{right,left,assumption,}},
  {right,right,assumption,},
  intro q,cases q,left,left,assumption,cases q,left,right, assumption,right,assumption,
end

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S :=
begin
  rintro q w e,cases e,{left,apply q, assumption,},
  {right,apply w,assumption},
end

example : (P → Q) → P ∨ R → Q ∨ R :=
begin
  intros q w,cases w,left,apply q, assumption,right,assumption,
end

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) :=
begin
  intros q w,split,intro e,cases e,{cases q,left,apply q_mp,assumption,},{cases w,right,apply w_mp,assumption,},
  intro e,cases w,cases e,cases q,left,apply q_mpr,assumption,right,apply w_mpr,assumption,
end

-- de Morgan's laws
example : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q :=
begin
  split,intro q,change (P∨Q)->false at q,split,intro w,apply q,left,assumption,intro w,apply q,right,assumption,
  intro q,change (P∨Q)->false,intro w,change (P->false)∧(Q->false) at q,cases q,cases w,apply q_left,assumption,apply q_right,assumption,
end

example : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  split,intro q,{by_cases Q,left,change (P∧ Q)->false at q,change P->false,intro w,apply q,split,assumption,assumption,right,assumption},
  {intro q,change(P∧Q)->false, intro w,by_cases P,cases q,apply q,assumption,apply q,cases w,assumption,apply h,cases w,assumption,},
end
