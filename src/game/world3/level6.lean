import category_theory.category.default

universes v u  -- The order in this declaration matters: v often needs to be explicitly specified while u often can be omitted

namespace category_theory

variables (C : Type u) [category.{v} C]

--rewrite this

/-
# Category world

## Level 7: Composition of monomorphisms

Now we show that the composition of two monomorphisms produces another monomorphism.-/

/- Lemma
If $$f : X ⟶ Y$$ and $$g : X ⟶ Y$$ are monomorphisms, then $$f ≫ g : X ⟶ Z$$ is a monomorphism.
-/
lemma epi_comp' {X Y Z : C} (f : X ⟶ Y) [epi f] (g : Y ⟶ Z) [epi g] : epi (f ≫ g) :=
begin
    split,
    intros Z h l hyp,
    rw ← cancel_epi g,
    rw ← cancel_epi f,
    rw ← category.assoc,
    rw ← category.assoc,
    exact hyp,
end

end category_theory