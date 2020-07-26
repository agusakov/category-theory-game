import category_theory.category.default
import category_theory.functor
import category_theory.isomorphism


universes v₁ v₂ u₁ u₂  -- The order in this declaration matters: v often needs to be explicitly specified while u often can be omitted

namespace category_theory

variables (C : Type u₁) [category.{v₁} C]
variables (D : Type u₂) [category.{v₂} D]

/-
# Naturality world

## Level 1: Definition of natural transformation

Given categories `C` and `D` and functors `F G : C ⥤ D`, a natural transformation α consists of
  * an arrow `α.app X : F.obj X ⟶ G.obj X` for each object `X` in `C`.

In other words, a functor consists of a mapping on objects and a mapping on morphisms that preserves all of the structure of a category, namely domains and codomains, composition, and identities.
  -/

  /- Axiom : 
    F.map f ≫ F.map g = F.map (f ≫ g)-/
  /- Axiom:
    F.map (𝟙 X) : 𝟙 (F.obj X)-/

/-- A functor `F : C ⥤ D` sends isomorphisms `i : X ≅ Y` to isomorphisms `F.obj X ≅ F.obj Y` -/
def map_iso (F : C ⥤ D) {X Y : C} (i : X ≅ Y) : F.obj X ≅ F.obj Y :=
{ hom := F.map i.hom,
  inv := F.map i.inv,
  hom_inv_id' := by rw [←map_comp, iso.hom_inv_id, ←map_id],
  inv_hom_id' := by rw [←map_comp, iso.inv_hom_id, ←map_id] }

end category_theory