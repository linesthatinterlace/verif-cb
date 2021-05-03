import tactic

-- Lean already has `eq` so let's make `eq2` for this exercise
inductive eq2 {X : Type} : X → X → Prop
| refl (a : X) : eq2 a a

/-
Lean already has `=` so I've used `∼` (type with `\sim`) as notation for eq2.
The 50 is the "binding power", something the parser needs to know.
-/

infix ` ∼ `:50 := eq2

namespace eq2

-- Let `X` be a type/set, and let a,b,c be terms/elements
variables {X : Type} {a b c : X}

-- Let's first establish the theorem we will need, using the recursor.

/-- If `a ∼ b`, and if `R` is a binary relation on `X` such that `R x x`
  is true for all `x`, then `R a b` is true  -/
theorem ind (hab : a ∼ b) (R : X → X → Prop) (h : ∀ x, R x x) :
  R a b := eq2.rec h hab
  -- don't worry about the proof


-- reflexivity is no problem -- indeed it's a constructor.
example : a ∼ a :=
begin
  exact refl a
end

theorem reflex : a ∼ a := refl a

/-
The game: using only `ind` and `refl`, prove `symm` and `trans`!
-/


-- level 1
theorem symm (hab : a ∼ b) : b ∼ a :=
begin
  have f := ind hab (λ x y : X, y ∼ x) (λ x : X, (refl x : (λ x y : X, y ∼ x) x x)),
  exact f,
end

-- boss level
theorem trans (hab : a ∼ b) (hbc : b ∼ c) : a ∼ c :=
  (ind hab (λ x y : X, x ∼ c ↔ y ∼ c) (λ x, ⟨id, id⟩)).mpr hbc

end eq2