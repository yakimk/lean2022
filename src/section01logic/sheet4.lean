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
  intro q,cases q,assumption,
end

example : P ∧ Q → Q :=
begin
  intro q,cases q,assumption,
end

example : (P → Q → R) → (P ∧ Q → R) :=
begin
  intros q w,apply q,cases w,assumption,cases w, assumption,
end

example : P → Q → P ∧ Q :=
begin
  intros q w, split, assumption,assumption,
end

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P :=
begin
  intro q,cases q,split ,assumption, assumption,
end

example : P → P ∧ true :=
begin
  intro q,split,assumption,triv,
end

example : false → P ∧ false :=
begin
  intro q,split ,by_contra,triv,triv,
end

/-- `∧` is transitive -/
example : (P ∧ Q) → (Q ∧ R) → (P ∧ R) :=
begin
  intros q w,split, cases q,assumption,cases w,assumption,
end

example : ((P ∧ Q) → R) → (P → Q → R) :=
begin
  intros q w e,apply q,split, assumption ,assumption,
end



