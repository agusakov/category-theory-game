import category_theory.category.default

universes v u  -- The order in this declaration matters: v often needs to be explicitly specified while u often can be omitted

namespace category_theory

variables (C : Type u) [category.{v} C]

/-
# Category world

## Level 3: The `specialize` tactic
-/

/-So recall that, in the Natural Number Game, we learned a tactic called `simp` that uses the lemmas and theorems to try to simplify the goal. Now we are going to learn `simpa`.

`simpa [rules, ...]` will simplify the goal and the type of a hypothesis this if present in the context, then try to close the goal using the assumption tactic.

-/

/-Try your hand at proving these next few lemmas using `simpa`.-/

/- Lemma
If $$f : X ⟶ Y$$ and $$g : X ⟶ Y$$ are morphisms such that $$f = g$$, then $$f ≫ h = g ≫ h$$.
-/
lemma eq_of_comp_left_eq'' (X Y : C) {f g : X ⟶ Y} (w : ∀ {Z : C} (h : Y ⟶ Z), f ≫ h = g ≫ h) : f = g :=
begin
    specialize w (𝟙 Y),
    rw ← category.comp_id f,
    rw ← category.comp_id g,
    exact w,
end

end category_theory

/- Tactic : specialize
## Summary
fill in summary
## Details
fill in details
-/