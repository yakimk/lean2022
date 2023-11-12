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
  intro p, left, assumption,
end

example : Q → P ∨ Q :=
begin
  intro p, right, assumption,
end

example : P ∨ Q → (P → R) → (Q → R) → R :=
begin
  intros imp1 imp2 imp3, cases imp1, apply imp2, assumption, apply imp3, assumption,
end

-- symmetry of `or`
example : P ∨ Q → Q ∨ P :=
begin
  intro q, cases q, right, assumption, left, assumption
end

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) :=
begin
  split, intro imp, cases imp, cases imp, left, assumption, right, left, assumption, 
  right, right, assumption,
  intro imp, cases imp, left, left, assumption, cases imp,  left, right,  assumption, 
  right,  assumption,
end

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S :=
begin
  intros imp1 imp2 h, cases h, left, apply imp1, assumption,
  right, apply imp2, assumption
end

example : (P → Q) → P ∨ R → Q ∨ R :=
begin
  intros imp1 imp2, cases imp2, left, apply imp1, assumption, right, assumption
end

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) :=
begin
  intros q w, rw q, rw w, 
end

-- de Morgan's laws
example : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q :=
begin
  split, intro q,
  change (P ∨ Q ) -> false at q , change (P -> false) ∧ (Q -> false) ,
  split, intro p, apply q, left, assumption,intro p, apply q, right, assumption,
  intro q, change (P ∨ Q ) -> false, change (P -> false) ∧ (Q -> false) at q,
  intro p, cases q, cases p, apply q_left, assumption, apply q_right, assumption,
end

example : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  split, intro q,
  by_cases hp : P, right, change Q->false, intro r, change  (P ∧ Q) -> false at q, apply q, exact ⟨hp, r⟩,
  left, assumption,
  intro q, change (P ∧ Q) -> false, intro w, change (P->false) ∨ (Q -> false) at q, cases q,by_cases hp : P,
  apply q, assumption, cases w;{apply hp, assumption,},
  {cases w, apply q, assumption,}

end
