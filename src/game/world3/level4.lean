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
lemma cancel_epi_id' (X Y : C) (f : X ⟶ Y) [epi f] {h : Y ⟶ Y} : (f ≫ h = f) ↔ h = 𝟙 Y :=
begin
    split,
    intro hyp,
    rw ← category.comp_id f at hyp,
    rw category.assoc at hyp,
    rw category.id_comp at hyp,
    rw ← cancel_epi f,
    exact hyp,

    intro hyp,
    rw hyp,
    exact category.comp_id f,
end

end category_theory