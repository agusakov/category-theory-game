import category_theory.category.default
import game.world1.level4

universes v u  -- The order in this declaration matters: v often needs to be explicitly specified while u often can be omitted

namespace category_theory

variables (C : Type u) [category.{v} C]

/-
# Category world

## Level 5: More tactic reviews
-/

/-blah blah

-/

/- Lemma
If $$f : X ⟶ Y$$ and $$g : X ⟶ Y$$ are morphisms such that $$f = g$$, then $$f ≫ h = g ≫ h$$.
-/
lemma id_of_comp_right_id' (X : C) (f : X ⟶ X) (w : ∀ {Y : C} (g : Y ⟶ X), g ≫ f = g) : f = 𝟙 X :=
begin
    apply eq_of_comp_right_eq'',
    intros Z h,
    rw category.comp_id h,
    apply w,
end

end category_theory