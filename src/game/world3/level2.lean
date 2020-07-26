import category_theory.category.default
import game.world1.level3

universes v u  -- The order in this declaration matters: v often needs to be explicitly specified while u often can be omitted

namespace category_theory

variables (C : Type u) [category.{v} C]

--rewrite this

/-
# Category world

## Level 7: Monomorphisms & epimorphisms

A monomorphism `f : Y ⟶ Z` is a morphism such that, for all pairs `g h : X ⟶ Y`, if `h ≫ f = g ≫ f`, 
then ` h = g`.

Similarly, an epimorphism `f : X ⟶ Y` is a morphism such that, for all pairs `g h : Y ⟶ Z`, if `f ≫ h = f ≫ g`, then ` h = g`.

Category theorists commonly refer to monomorphisms and epimorphisms as `mono` and `epi` respectively, and this is the case in Lean as well. 

So this gives us axioms
-/

/- Axiom:
    mono f, g h : Y ⟶ Z, f ≫ g = f ≫ h → g = h-/ --figure out how to phrase these axioms jeez

/-We will now prove that, if `f` is mono, then f ≫ g = f ≫ h ↔ g = h so we can use `rw`.-/

/- Lemma
If $$f : X ⟶ Y$$ and $$g : X ⟶ Y$$ are morphisms such that $$f = g$$, then $$f ≫ h = g ≫ h$$.
-/
lemma cancel_epi' {X Y Z : C} {f : X ⟶ Y} [epi f] {g h : Y ⟶ Z} : (f ≫ g = f ≫ h) ↔ g = h :=
begin
    split,
    
    intro hyp,
    apply epi.left_cancellation g h hyp,

    intro hyp,
    rw hyp,
end

end category_theory