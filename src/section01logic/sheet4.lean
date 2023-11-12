/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases`
* `split`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variables (P Q R : Prop)

example : P ∧ Q → P :=
begin
  intro c, cases c, exact c_left,
end

example : P ∧ Q → Q :=
begin
  intro c, cases c, exact c_right,
end

example : (P → Q → R) → (P ∧ Q → R) :=
begin
  intros imp c, cases c, apply imp,exact c_left, exact c_right, 
end

example : P → Q → P ∧ Q :=
begin
  intros p q, split, exact p, exact q,
end

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P :=
begin
  intro c, split,cases c,exact c_right, cases c, exact c_left,
end

example : P → P ∧ true :=
begin
  intro p, split, exact p, triv,
end

example : false → P ∧ false :=
begin
  intro f, split, exfalso, exact f, exact f,
end

/-- `∧` is transitive -/
example : (P ∧ Q) → (Q ∧ R) → (P ∧ R) :=
begin
  intros imp1 imp2,cases imp1, cases imp2, split, exact imp1_left,
  exact imp2_right, 
end

example : ((P ∧ Q) → R) → (P → Q → R) :=
begin
  intros imp p q,apply imp, split, exact p, exact q,
end



