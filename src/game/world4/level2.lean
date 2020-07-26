import category_theory.category.default
import category_theory.functor
import category_theory.isomorphism


universes v₁ v₂ u₁ u₂  -- The order in this declaration matters: v often needs to be explicitly specified while u often can be omitted

namespace category_theory

variables (C : Type u₁) [category.{v₁} C]
variables (D : Type u₂) [category.{v₂} D]

/-
# Functor world

## Level 1: Definition of functor

A functor `F : C ⥤ D` between categories `C` and `D` consists of
  * an object `F.obj X ∈ D` for all objects `X ∈ C`
  * a morphism `Ff : F.obj X ⟶ F.obj Y` for each morphism `f : X ⟶ Y`, where the domain and codomain of `Ff` are, respectively, equal to `F` applied to the domain and codomain of `f`.
The assignments are required to satisfy the following two functoriality axioms:
  * for any composable pair of morphisms `f, g` in `C`, `F.map f ≫ F.map g = F.map (f ≫ g)`.
  * for each object `X` in `C`, `F.map (𝟙 X) : 𝟙 (F.obj X)`.
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