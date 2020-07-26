import category_theory.category.default

universes v u  -- The order in this declaration matters: v often needs to be explicitly specified while u often can be omitted

namespace category_theory

variables (C : Type u) [category.{v} C]

--rewrite this

/-
# Category world

## Level 7: Cancellations

With monomorphisms and epimorphisms, we get some new useful cancellation laws. You will notice that the following two lemmas are pretty similar to the lemma we had in level 5 of world 1. See if you can spot the difference.
-/

/- Lemma
If $$f : X ⟶ Y$$ and $$g : X ⟶ Y$$ are morphisms such that $$f = g$$, then $$f ≫ h = g ≫ h$$.
-/
lemma cancel_mono_id' (X Y : C) (f : X ⟶ Y) [mono f] {g : X ⟶ X} : (g ≫ f = f) ↔ g = 𝟙 X :=
begin
    split,
    
    intro hyp,
    rw ← category.id_comp f at hyp,
    rw ← category.assoc at hyp,
    rw category.comp_id at hyp,
    rw ← cancel_mono f,
    exact hyp,

    intro hyp,
    rw hyp,
    exact category.id_comp f,
end

end category_theory