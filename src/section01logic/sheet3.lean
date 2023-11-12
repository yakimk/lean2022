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
  intro nt, change true -> false at nt, apply nt, trivial, 
end

example : false → ¬ true :=
begin
  intro f, change true -> false, intro t, exact f,
end

example : ¬ false → true :=
begin
  intro nf, trivial, 
end

example : true → ¬ false :=
begin
  intro t, change false->false,intro f, exact f, 
end

example : false → ¬ P :=
begin
  intro f, change P -> false, intro P, exact f,
end

example : P → ¬ P → false :=
begin
  intros hp nhp, apply nhp,  exact hp,
end

example : P → ¬ (¬ P) :=
begin
  intro hp, change ¬P -> false, intro nhp, apply nhp, exact hp,   
end

example : (P → Q) → (¬ Q → ¬ P) :=
begin
  intros imp nq, change P -> false,intro hp, apply nq,apply imp, exact hp, 
end

example : ¬ ¬ false → false :=
begin
  intro f, change ¬false -> false at f, apply f, change false -> false, intro fh, exact fh, 
end

example : ¬ ¬ P → P :=
begin
  intro p, change ¬P -> false at p, by_cases P, 
  {exact h},
  {by_contra,apply p, exact h,}
end

example : (¬ Q → ¬ P) → (P → Q) :=
begin
  intros imp hp, by_cases Q, {exact h},{by_contra,apply imp, {exact h},{exact hp}}
end