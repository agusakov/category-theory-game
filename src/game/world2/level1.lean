import category_theory.category.default
import category_theory.isomorphism

universes v u  -- The order in this declaration matters: v often needs to be explicitly specified while u often can be omitted

namespace category_theory

variables (C : Type u) [category.{v} C]

--rewrite this

/-
# Category world

## Level 1: Isomorphisms

An isomorphism `f : X ⟶ Y` is a morphism for which there exists a morphism `g : Y ⟶ X`, such that `f ≫ g = 𝟙 X` and `g ≫ f = 𝟙 Y`.
-/


/- Lemma
If $$f : X ⟶ Y$$ and $$g : X ⟶ Y$$ are morphisms such that $$f = g$$, then $$f ≫ h = g ≫ h$$.
-/
lemma cancel_left_iso' {X Y Z : C} (f : X ⟶ Y) [is_iso f] {g h : Z ⟶ X} : (g ≫ f = h ≫ f) ↔ g = h :=
begin
    split,

    intro hyp,
    rw ← category.comp_id g,
    rw ← category.comp_id h,
    rw ← is_iso.hom_inv_id f,
    rw ← category.assoc,
    rw hyp,
    rw category.assoc,

    intro hyp,
    rw hyp,
end

end category_theory