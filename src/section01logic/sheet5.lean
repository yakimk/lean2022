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
  intro imp, rw imp, 
end

example : (P ↔ Q) ↔ (Q ↔ P) :=
begin
  split;
  {intro h, rw h,}
end

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
  intros q w ,
  rwa q, 
end

example : P ∧ Q ↔ Q ∧ P :=
begin
  split;
  { rintro ⟨h1, h2⟩,
    exact ⟨h2, h1⟩ }
end


example : ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R)) :=
begin
  split,{ rintro ⟨h1, h2⟩, cases h1 with q w, exact ⟨q, w, h2⟩, },
  { rintro ⟨h1, h2⟩, cases h2 with q w, split, exact ⟨h1, q⟩, exact w,  }
end

example : P ↔ (P ∧ true) :=
begin
  split, intro p, split, exact p, triv, intro q, cases q, exact q_left,
end

example : false ↔ (P ∧ false) :=
begin
  split, intro f, exfalso, assumption, 
  intro f, cases f, assumption,
end

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) :=
begin
  intros eq1 eq2, rw eq1, rw eq2,   
end

example : ¬ (P ↔ ¬ P) :=
begin
  change (P ↔ ¬ P) -> false, intro eq, change (P ↔ P -> false) at eq,
  cases eq, apply eq_mp, apply eq_mpr, intro p, apply eq_mp, exact p, exact p, apply eq_mpr, intro p, apply eq_mp, exact p, exact p, 
end
