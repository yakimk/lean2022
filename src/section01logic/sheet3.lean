/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`) 

We learn about how to manipulate `¬ P` in Lean.

# Important : the definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part B of the course notes.

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variables (P Q R : Prop)

example : ¬ true → false :=
begin
  intro q, change true->false at q,apply q,triv,
end

example : false → ¬ true :=
begin
  intro q, by_contra, triv,
end

example : ¬ false → true :=
begin
  intro q,triv,
end

example : true → ¬ false :=
begin
  intros q w,triv,
end

example : false → ¬ P :=
begin
  intro q,change P->false,intro w,triv,
end

example : P → ¬ P → false :=
begin
  intro q, triv,
end

example : P → ¬ (¬ P) :=
begin
  intro q,change ¬ P ->false,triv,
end

example : (P → Q) → (¬ Q → ¬ P) :=
begin
  intros q w e, apply w,apply q,assumption,
end

example : ¬ ¬ false → false :=
begin
  intro q, apply q,intro w,triv,
end

example : ¬ ¬ P → P :=
begin
  intro q,by_contra,apply q,triv,
end

example : (¬ Q → ¬ P) → (P → Q) :=
begin
  intro q,intro w,by_cases Q,{assumption},{by_contra, apply q,{assumption},{assumption}}
end