import tactic group_theory.perm.cycles order.well_founded_set

namespace equiv.perm

-- This lemma is going to be a PR at some point.

@[simp]
theorem same_cycle_apply' {δ : Type*} {f : equiv.perm δ} {x y : δ} :
  f.same_cycle (f x) y ↔ f.same_cycle x y :=
⟨λ h, (same_cycle_apply.1 (h.symm _)).symm _,
 λ h, (same_cycle_apply.2 (h.symm _)).symm _⟩

end equiv.perm

open equiv equiv.perm set set.finite nat function

section part_two

variables {α : Type*} [linear_order α] [is_well_order α (<)]
variables {β : Type*} [linear_order β]
variables {γ : Type*} [has_lt γ] [h : is_well_order γ (<)] 
variables {δ : Type*}

  /-
    This brief lemma lets us conclude that if a type is well-ordered, 
    sets of that type are well-founded.
  -/

@[simp]
lemma wo_set_is_wf (t : set γ) : t.is_wf := well_founded.is_wf h.wf t

  -- Definition 2.1

def cycle (π : perm δ) (x : δ) : set δ := π.same_cycle x

  -- Which isn't empty...

lemma cycle_nonempty (π : perm δ) (x : δ)
  : (cycle π x).nonempty := (range_nonempty (λ (y : ℤ), (π ^ y) x))

  -- Theorem 2.2

theorem cycle_pi_x_eq_x (π : perm δ) (x : δ)
  : cycle π (π x) = cycle π x := ext (λ z, same_cycle_apply')

  -- Definition 2.3

noncomputable def cyclemin (π : perm α) (x : α) : α :=
  (wo_set_is_wf _).min (cycle_nonempty π x)

lemma cyclemin_le {π : perm α} {x y : α} (hy : y ∈ cycle π x)
  : cyclemin π x ≤ y := set.is_wf.min_le _ _ hy

lemma cyclemin_invariant_pi (π : perm α) (x : α)
  : cyclemin π (π x) = cyclemin π x :=
begin
  apply le_antisymm,
  { apply is_wf.min_le_min_of_subset,
    rintros y ⟨k, hk⟩,
    use k - 1,
    rwa [gpow_sub, mul_apply, gpow_one, equiv.perm.inv_apply_self],
  },
  { apply is_wf.min_le_min_of_subset,
    rintros y ⟨k, hk⟩,
    use k + 1,
    rwa [gpow_add, mul_apply, gpow_one],
  },
end

  /-
  A succesion of lemmas about cycle sections, which are used for Theorems 2.4
  and 2.5.
  -/


def cycle_section (π : perm δ) (x : δ) (r : ℤ) : set δ :=
  { a : δ | ∃ k : ℤ, k ∈ (Ico 0 r) ∧ (π^k) x = a }

lemma cycle_section_in_cycle (π : perm δ) (x : δ) (r : ℤ) :
  cycle_section π x r ⊆ cycle π x := λ y ⟨k, ⟨_, _⟩, hy⟩, ⟨k, hy⟩

lemma cycle_section_is_image (π : perm δ) (x : δ) (r : ℤ) :
  cycle_section π x r = image (λ k : ℤ, (π^k) x) (Ico 0 r) := rfl

lemma cycle_section_finite (π : perm δ) (x : δ) (r : ℤ) :
  (cycle_section π x r).finite := finite.image _ (Ico_ℤ_finite _ _)

lemma cycle_section_has_x (π : perm δ) (x : δ) {r : ℤ} (h : 0 < r)
  : x ∈ (cycle_section π x r) := 
⟨0, ⟨le_refl _, h⟩, (by simp [gpow_zero, equiv.perm.coe_one])⟩

lemma cycle_section_nonempty (π : perm δ) (x : δ) {r : ℤ} (h : 0 < r) 
  : (cycle_section π x r).nonempty := ⟨x, cycle_section_has_x _ _ h⟩

lemma cycle_section_one_singleton (π : perm δ) (x : δ)
  : cycle_section π x 1 = {x} :=
begin
  apply set.ext, intro _, rw mem_singleton_iff, split,
  { rintros ⟨k, ⟨k_lb, k_ub⟩, hy⟩,
    simp [ ← hy, ((le_antisymm_iff.mpr ⟨k_lb,
    (int.le_sub_one_iff.mpr k_ub)⟩).symm) ],
  },
  { rintros rfl, exact cycle_section_has_x _ _ (zero_lt_one) }
end

noncomputable def cycle_section_min (π : perm α) (x : α) { r : ℤ }
  (h : 0 < r) : α :=
(wo_set_is_wf (cycle_section π x r)).min (cycle_section_nonempty π x h)

lemma cycle_section_union (π : perm δ) (x : δ) {r s : ℤ} (ha : 0 ≤ r)
  (hb : 0 ≤ s) : (cycle_section π x r) ∪ (cycle_section π ( (π^r) x) s) = 
    (cycle_section π x (r + s)) :=
begin
  apply set.ext, intro y, split,
  { rintros (h | ⟨k, ⟨k_lb, k_ub⟩, hy⟩),
    { rcases h with ⟨k, ⟨k_lb, k_ub⟩, hy⟩,
      exact ⟨k, ⟨k_lb, lt_of_lt_of_le k_ub (le_add_of_nonneg_right hb)⟩, hy⟩
    },
    { refine ⟨r + k, ⟨add_nonneg ha k_lb, add_lt_add_left k_ub r⟩, _⟩,
      rwa [add_comm, gpow_add, mul_apply],
    },
  },
  { rintros ⟨k, ⟨k_lb, k_ub⟩, hy⟩,
    cases (lt_or_le k r) with h,
    { left, exact ⟨k, ⟨k_lb, h⟩, hy⟩, },
    { right,
      refine ⟨k - r, ⟨sub_nonneg_of_le h, sub_lt_iff_lt_add'.mpr k_ub⟩, _⟩,
      rwa [←mul_apply, ←gpow_add, sub_add_cancel],
    },
  },
end

lemma cycle_section_trivial_min (π : perm α) (x : α)
  : x = cycle_section_min π x (zero_lt_one) :=
begin
  conv begin
    to_lhs,
    rw ← @is_wf_min_singleton _ _ x (is_wf_singleton x) (singleton_nonempty x),
  end,
  rw [cycle_section_min, le_antisymm_iff],
  split;
  { apply (is_wf.min_le_min_of_subset _),
    rw cycle_section_one_singleton,
  },
end

  --Theorem 2.4 (Definition of c_i.)

def fast_cyclemin : ℕ → perm β → β → β
  | 0 _ x := x
  | (i+1) π x := min  (fast_cyclemin i π x)
                      (fast_cyclemin i π ((π ^ (2^i : ℤ)) x))

  --Theorem 2.4 (Content of theorem.)

theorem fast_cyclemin_eq_section (i : ℕ) (π : perm α) (x : α)
  : fast_cyclemin i π x = cycle_section_min π x (pow_pos zero_lt_two i) := 
begin
  induction i with i hi generalizing x,
  { simp only [nat.nat_zero_eq_zero, pow_zero],
    rw [fast_cyclemin, ← cycle_section_trivial_min π x],
  },
  { rw [ fast_cyclemin, hi, hi, cycle_section_min, cycle_section_min,
    cycle_section_min, ← is_wf.min_union, le_antisymm_iff ],
    split;
    { apply (is_wf.min_le_min_of_subset _),
      rw cycle_section_union π x (pow_nonneg zero_le_two _)
      (pow_nonneg zero_le_two _),
      rw [pow_succ, two_mul],
    }
  }
end

  -- Some lemmas about perms that are useful for rewriting.

lemma perm_iterate_fixed_point {π : perm δ} {x : δ} {p q: ℤ}
  (h : (π ^ p) x = x ) : ((π ^ p) ^ q) x = x := 
begin
  rcases q with (q | q); induction q,
  { simp },
  { simpa [gpow_add, mul_apply, gpow_one, h] },
  { rw [← h, gpow_neg_succ_of_nat, pow_one, inv_apply_self, h], },
  { rwa [← h, int.neg_succ_of_nat_eq', gpow_sub, mul_apply, gpow_one,
    inv_apply_self, h] },
end

lemma perm_mod_fixed_point {π : perm δ} {x : δ} {p q r : ℤ} (h : (π ^ r) x = x)
  : (π ^ (p + r*q)) x = (π ^ p) x := 
(by { rwa [gpow_add, mul_apply, gpow_mul, perm_iterate_fixed_point] } )

  -- Theorem 2.5

theorem fast_cyclemin_eq_cyclemin {π : perm α} {i : ℕ} (x : α)
  { h₁ : (cycle π x).finite } ( h₂ : h₁.to_finset.card ≤ 2^i )
    : fast_cyclemin i π x = cyclemin π x := 
begin
  have  section_card_ub : (cycle_section_finite π x (2^i + 1)).to_finset.card <
        (finset.range (2 ^ i + 1)).card,
  { refine lt_of_le_of_lt (le_trans (
    finset.card_le_of_subset (finite.to_finset_mono.mpr
    (cycle_section_in_cycle _ _ _))) h₂) (_),
    simp [finset.card_range (2 ^ i + 1)],
  },
  have full_pidge :
    ∀ k ∈ finset.range (2 ^ i + 1), 
      (λ k, (π^k) x) k ∈ (cycle_section_finite π x (2 ^ i + 1)).to_finset,
  { have fix_pow : (2 ^ i + 1 : ℤ)= ↑(2 ^ i + 1: ℕ) := (by simp),
    dsimp, rw fix_pow,
    intro k, rw [finset.mem_range, finite.mem_to_finset],
    exact λ hk, ⟨k, ⟨int.coe_nat_nonneg _,
    (int.coe_nat_lt_coe_nat_iff _ _).mpr hk⟩, rfl⟩,
  },
  have cycle_finite : ∃ t : ℕ, (0 < t) ∧ (t ≤ 2^i) ∧ ((π^t) x = x),
  { rcases (finset.exists_ne_map_eq_of_card_lt_of_maps_to (section_card_ub)
    full_pidge) with ⟨a, ha, b, hb, aneb, hab⟩, dsimp at hab,
    rw [finset.mem_range, nat.lt_succ_iff] at ha hb,
    rcases (lt_trichotomy a b) with _ | h | h, rotate,
    { exfalso, contradiction },
    use (a - b), rotate, use (b - a),
    all_goals { refine ⟨nat.sub_pos_of_lt h, ⟨le_trans (nat.sub_le _ _) _, _⟩⟩,
              assumption },
    apply equiv.injective (π^a), rotate, apply equiv.injective (π^b),
    all_goals { rw [ ←equiv.perm.mul_apply, ←pow_add,
              ←nat.add_sub_assoc (le_of_lt h), nat.add_sub_cancel_left, hab ] }
  },
  rw [fast_cyclemin_eq_section, le_antisymm_iff],
  split; apply is_wf.min_le_min_of_subset,
  { rintros y ⟨k, hk⟩,
    rcases cycle_finite with ⟨t, ⟨ht₁, ⟨ht₂, ht₃⟩⟩⟩,
    cases k, use k % t, rotate, use (t - ((k % t) + 1)),
    all_goals { split, split },
    { simp [ ← int.coe_nat_mod, sub_sub, le_sub_left_of_add_le, int.coe_nat_lt],
        exact ((int.coe_nat_lt.mpr) (nat.mod_lt k ht₁)),
    },
    { have fix_pow : (2 ^ i : ℤ)= ↑(2 ^ i : ℕ) := (by simp), rw fix_pow,
        refine lt_of_lt_of_le _ (int.coe_nat_le.mpr ht₂),
        simp [← int.coe_nat_mod],
    },
    { have rearrange :  (↑t - (↑k - ↑t * (↑k / ↑t) + 1))
                          = ((-↑k - 1) + ↑t*(1 + (↑k / ↑t)) : ℤ) := (by ring),
        rw [ ← hk, int.mod_def, int.neg_succ_of_nat_coe', rearrange],
        exact perm_mod_fixed_point ht₃
    },
    { rw ← int.coe_nat_mod, apply int.coe_nat_nonneg },
    { have fix_pow : (2 ^ i : ℤ)= ↑(2 ^ i : ℕ), simp, rw fix_pow,
        exact (int.coe_nat_lt.mpr (lt_of_lt_of_le (nat.mod_lt k ht₁) ht₂)),
    },
      { have rearrange :  (↑k - ↑t * (↑k / ↑t))
                          = (↑k + ↑t * (-(↑k / ↑t)) : ℤ) := (by ring),
        rw [←hk, int.mod_def, int.of_nat_eq_coe, rearrange],
        exact perm_mod_fixed_point ht₃
    }
  },
  { apply cycle_section_in_cycle }
end

end part_two

section part_three

  /-
    Much of the work of this part is in carefully defining arithmetic operations
    and xor on the finite types we will work with later. There are a lot of
    subtle properties we require!
  -/

variables {b : ℕ}

  -- We define xor in a simple, boring way.

def xor_one (b : ℕ) (x : fin (2*b + 2)) : fin (2*b + 2) :=
  ite (even x.val) (x + 1) (x - 1)

  /-
    To avoid confusions with coercion and overloading, we define mul, mod and
    div ops in a special way between specific types.
  -/

def fin.div_two  (x : fin (2*b + 2)) :  fin (b + 1) :=
begin
  refine ⟨x/2, _⟩,
  rw [nat.div_lt_iff_lt_mul _ _ (zero_lt_two), nat.mul_comm _ 2,
  mul_add, mul_one, ← fin.val_eq_coe],
  exact x.property,
end

def fin.mul_two (y : fin (b + 1)) : fin (2*b + 2) :=
begin
  refine ⟨2*y, _⟩,
  rw ← nat.mul_succ,
  exact nat.mul_lt_mul' (le_refl _) y.property (zero_lt_two),
end

def fin.mod_two {n : ℕ} (z : fin n) : fin 2 :=
begin
  refine ⟨z % 2, _⟩,
  exact nat.mod_lt _ (zero_lt_two),
end 

  -- "Even numbers aren't odd."

lemma two_mul_neq_two_mul_add_one (m : ℕ) (n : ℕ) : 2*m ≠ 2*n + 1 :=
begin
  intro contra,
  have h_e : even (2*m), use m,
  have h_o : odd (2*m), rw contra, use n,
  rw odd_iff_not_even at h_o, contradiction,
end

  /-
    The following pair of lemmas are incredibly ugly, but they are constantly
    useful when proving these utility proofs.
  -/

lemma fiddly_even_mod {b : ℕ} {x : fin (2*b + 2)} (h : even x.val)
  : (x.val + 1) % (2 * b + 2) = x.val + 1 := 
begin
  rcases h with ⟨k, hk⟩, rw hk,
  cases le_iff_eq_or_lt.mp (nat.succ_le_iff.mpr x.property),
  { exfalso,
    apply two_mul_neq_two_mul_add_one b.succ k,
    rw [← hk, add_one, h, mul_succ],
  },
  { rw [← hk, add_one, nat.mod_eq_of_lt h] }
end

lemma fiddly_odd_mod {b : ℕ} {x : fin (2*b + 2)} (h : ¬even x.val)
  : (x.val + (2 * b + 2 - 1)) % (2 * b + 2) = x.val - 1 :=
begin
  rw ← odd_iff_not_even at h,
  rcases h with ⟨k, hk⟩,
  rw [hk, add_succ_sub_one, add_assoc,  ← add_assoc 1,  add_comm 1, add_assoc,
  nat.add_mod_right, nat.mod_eq_of_lt, add_succ_sub_one, add_zero],
  refine lt_of_le_of_lt _ x.property,
  rw hk, exact le_succ _
end

  /-
    It's useful to think of the control bits as numbers in fin 2, which is to
    say, naturals mod 2. We could use bools, but it makes some calculation later
    more fiddly. Not sure which is better!
  -/

lemma fin_two_not_one_iff_zero : ∀ y : fin 2, ¬ y = 1 ↔ y = 0 :=
begin
  intro y, split; intro hy,
  { rw fin.eq_iff_veq at hy ⊢, rw fin.val_one at hy, rw fin.val_zero,
    exact le_antisymm (le_of_succ_le_succ
    (lt_of_le_of_ne (le_of_succ_le_succ y.property) hy)) (nat.zero_le _),
  },
  { rw hy, exact fin.zero_ne_one }
end

  -- An obvious fact : 2*x = 0 mod 2.

lemma mul_two_mod_two_eq_zero (y : fin (b + 1)) : y.mul_two.mod_two = 0 :=
begin
  unfold fin.mul_two fin.mod_two, rw ← fin.mk_zero,
  rw subtype.mk_eq_mk, rw fin.coe_mk, rw nat.mul_mod_right,
end

  -- If x is even, its xor is not.

lemma val_even_iff_val_xor_one_odd (x : fin (2*b + 2))
  : (even x.val) ↔ ¬(even (xor_one b x).val) :=
begin
  split; intro h,
  { unfold xor_one,
    rw if_pos h,
    rw ← odd_iff_not_even,
    rcases (id h) with ⟨k, hk⟩,
    use k,
    rw [fin.add_def, fin.val_one, fiddly_even_mod h, hk],
  },
  { unfold xor_one at h,
    rcases even_or_odd (x.val) with h' | h',
    { exact h' },
    { rw odd_iff_not_even at h',
      rw if_neg h' at h,
      rw ← odd_iff_not_even at h,
      rcases h with ⟨k, hk⟩,
      rw [fin.sub_def, fin.val_one, fiddly_odd_mod h'] at hk,
      use k + 1,
      rcases (nat.eq_zero_or_eq_succ_pred x.val) with xv_eq | xv_eq,
      { exfalso,
        apply nat.succ_ne_zero (2*k),
        rw xv_eq at hk, rw nat.zero_sub at hk, rw add_one at hk,
        rw hk,
      },
      { rw xv_eq, rw mul_add, rw mul_one, congr,
        rwa nat.pred_eq_sub_one,
      }
    }
  }
end

  -- If x is odd, its xor by one is not.

lemma val_odd_iff_val_xor_one_even (x : fin (2*b + 2))
  : (odd x.val) ↔ ¬(odd (xor_one b x).val) :=
begin
  split; intro h; rw odd_iff_not_even at h ⊢,
  { rwa (not_iff_not).mpr (val_even_iff_val_xor_one_odd _) at h },
  { rwa (not_iff_not).mpr (val_even_iff_val_xor_one_odd _) }
end

  -- x is never its own xor by one.

lemma ne_xor_one  (x : fin (2*b + 2)) : x ≠ (xor_one b) x :=
begin
  intro contra,
  rcases even_or_odd (x.val) with h | h,
  { apply (val_even_iff_val_xor_one_odd _).mp h,
    rw ← contra,
    exact h,
  },
  { apply (val_odd_iff_val_xor_one_even _).mp h,
    rw ← contra,
    exact h,
  }
end

  /-
    xoring by one is an involution. This is a bit non-trivial, because
    of our definition of xor.
  -/

lemma xor_one_involutive (b : ℕ) : involutive (xor_one b) := 
begin
  intros x,
  have prop := x.property,
  rw xor_one, split_ifs,
  { rcases even_or_odd (x.val) with h' | h',
    { rw val_even_iff_val_xor_one_odd at h',
      contradiction,
    },
    { rw [xor_one, if_neg (odd_iff_not_even.mp h'), sub_add_cancel] }
  },
  { rcases even_or_odd (x.val) with h' | h',
    { rw [xor_one, if_pos h', add_sub_cancel] },
    { rw val_odd_iff_val_xor_one_even at h',
      rw odd_iff_not_even at h',
      contradiction,
    }
  }
end

  /-
    A really subtle lemma which requires some careful rewriting to prove,
    which traps a number to the xor by one of another.
  -/

lemma xor_one_trap (x : fin (2*b + 2)) (x' : fin (2*b + 2))
  : (xor_one b x') < (xor_one b x) → x ≤ x' → x = (xor_one b x') :=
begin
  unfold xor_one, split_ifs with hy hx hx,
  all_goals {intros h_lt h_le},
  { rw [fin.lt_iff_coe_lt_coe, fin.coe_eq_val, fin.coe_eq_val, fin.add_def,
    fin.add_def, fin.val_one, fiddly_even_mod hx, fiddly_even_mod hy] at h_lt,
    rw [fin.le_iff_coe_le_coe, fin.coe_eq_val, fin.coe_eq_val] at h_le,
    exfalso,
    exact not_le_of_lt (lt_of_succ_lt_succ h_lt) h_le
  },
  { rw [fin.lt_iff_coe_lt_coe, fin.coe_eq_val, fin.coe_eq_val, fin.add_def,
    fin.sub_def, fin.val_one, fiddly_odd_mod hx, fiddly_even_mod hy] at h_lt,
    rw [fin.le_iff_coe_le_coe, fin.coe_eq_val, fin.coe_eq_val] at h_le,
    exfalso,
    exact nat.not_succ_lt_self (lt_of_lt_of_le h_lt
    (le_trans (nat.pred_le _) h_le))
  },
  { rw [fin.eq_iff_veq, fin.sub_def, fin.val_one, fiddly_odd_mod hy],
    rw [fin.lt_iff_coe_lt_coe, fin.coe_eq_val, fin.coe_eq_val, fin.add_def,
    fin.sub_def, fin.val_one, fiddly_even_mod hx, fiddly_odd_mod hy] at h_lt,
    rw [fin.le_iff_coe_le_coe, fin.coe_eq_val, fin.coe_eq_val] at h_le,
    rw ← nat.odd_iff_not_even at hy,
    rcases hx with ⟨k, hk⟩,
    rcases hy with ⟨k', hk'⟩,
    rw [hk, hk'] at *,
    rw nat.add_sub_cancel at h_lt ⊢,
    cases (le_iff_eq_or_lt.mp h_le),
    { exfalso,
      exact two_mul_neq_two_mul_add_one k k' h,
    },
    { exact le_antisymm (nat.le_of_succ_le_succ h)
    (nat.le_of_succ_le_succ h_lt) }
  },
  { rw [fin.lt_iff_coe_lt_coe, fin.coe_eq_val, fin.coe_eq_val, fin.sub_def,
    fin.sub_def, fin.val_one, fiddly_odd_mod hx, fiddly_odd_mod hy] at h_lt,
    rw [fin.le_iff_coe_le_coe, fin.coe_eq_val, fin.coe_eq_val] at h_le,
    exfalso,
    exact not_le_of_lt h_lt (pred_le_pred h_le)
  }
end

  -- This is the key relationship between the div_two and mul_two functions.

lemma fin_div_two_mul_two_related (x : fin (2*b + 2))
  : x = x.div_two.mul_two ∨ x = (xor_one b x.div_two.mul_two) :=
begin
  rcases even_or_odd (x.val) with h | h,
  { rcases h with ⟨k, hk⟩,
    left, unfold fin.div_two fin.mul_two,
    rw [fin.ext_iff, fin.coe_mk, fin.coe_mk, fin.coe_eq_val, hk],
    simp,
  },
  { rcases h with ⟨k, hk⟩,
    right, unfold xor_one fin.div_two fin.mul_two,
    rw if_pos,
    { dsimp, rw [fin.eq_iff_veq, fin.add_def, fin.val_one, hk, fin.mk_val,
      fin.coe_eq_val, hk, add_comm,nat.add_div_of_dvd_left (dvd_mul_right 2 k),
      nat.div_eq_of_lt (one_lt_two),zero_add, mul_div_right _ (zero_lt_two),
      ← hk, mod_eq_of_lt x.property,hk, add_comm],
    },
    { dsimp, use (↑x / 2) }
  }
end

  /-
    When you mod_two a xor by one, it's the same as adding one (in fin 2) to the
    first value mod two. It might be that a better definition of mod_two would
    make this easier, or even unnecessary.
  -/

lemma xor_one_mod_two (x : fin (2*b + 2))
  : (xor_one b x).mod_two = 1 + x.mod_two :=
begin
  rw xor_one, unfold fin.mod_two, split_ifs, 
  { rw [fin.eq_iff_veq, fin.mk_val, fin.add_def, fin.val_one, fin.mk_val, 
    fin.coe_eq_val, fin.coe_eq_val, fin.add_def, fin.val_one, fiddly_even_mod h,
    add_comm],
    simp,
  },
  { rcases (odd_iff_not_even.mpr h) with ⟨_, hk⟩,
    rw [fin.eq_iff_veq, fin.mk_val, fin.add_def, fin.val_one, fin.mk_val,
    fin.coe_eq_val, fin.coe_eq_val, fin.sub_def, fin.val_one, fiddly_odd_mod h,
    hk, add_comm _ 1],
    simp,
  }
end

  -- This is the "floor" part of Theorem 3.1

lemma xor_one_floor (x : fin (2*b + 2)) : (xor_one b x).div_two = x.div_two :=
begin
  unfold fin.div_two xor_one,
  rw subtype.mk_eq_mk, split_ifs,
  { rcases (id h) with ⟨k, hk⟩,
    rw [fin.coe_eq_val, fin.coe_eq_val, fin.add_def, fin.val_one,
    fiddly_even_mod h, hk, add_comm, nat.add_div_of_dvd_left
    (dvd_mul_right 2 k), nat.div_eq_of_lt (one_lt_two), zero_add],
  },
  { rcases (odd_iff_not_even.mpr h) with ⟨k, hk⟩,
    rw [fin.coe_eq_val, fin.coe_eq_val, fin.sub_def, fin.val_one,
    fiddly_odd_mod h, hk, add_succ_sub_one, add_zero, add_comm,
    nat.add_div_of_dvd_left (dvd_mul_right 2 k),
    nat.div_eq_of_lt (one_lt_two), zero_add],
  }
end

  /-
    This defines the permutation represented by xor. We can view this as giving
    for us that xor by one really is in {0, 1, .., 2b + 1}: the first part of
    Theorem 3.1.
  -/

def xor_one_perm (b : ℕ) : perm (fin (2*b + 2)) :=
  function.involutive.to_equiv (xor_one _) (xor_one_involutive _)

  -- Lemma which shows that the permutation coerces to the function.

lemma xor_one_perm_eq_xor_one : ⇑(xor_one_perm b) = xor_one b :=
begin
  ext, simp [xor_one_perm, xor_one],
end 

  /-
    Definition 3.2. 
  -/

def Xif_s (s : fin (b + 1) → fin 2) (x : fin (2*b + 2)) : fin (2*b + 2)
  := ite (s (x.div_two) = 1) (xor_one b x) x

  -- Theorem 3.3. Easy after all the above!

theorem Xif_s_involutive (s : fin (b + 1) → fin 2) : involutive (Xif_s s) := 
begin
  intros x, rw Xif_s, rw Xif_s, split_ifs with h h',
  { apply xor_one_involutive },
  { exfalso, rw (xor_one_floor x) at h', exact h' h },
  { refl }
end

  -- Xif_s as a permutation.

def Xif_s_perm (s : fin (b + 1) → fin 2) : perm (fin (2*b + 2)) :=
  function.involutive.to_equiv (Xif_s s) (Xif_s_involutive s)

 -- Lemma which shows that the permutation coerces to the function.
 
theorem coe_Xif_s_perm_eq_Xif_s (s : fin (b + 1) → fin 2)
  : ⇑(Xif_s_perm s) = Xif_s s :=
begin
  ext, simp [Xif_s_perm, Xif_s],
end 

end part_three

section part_four

variables {b : ℕ} (π : perm ( fin (2*b + 2) )) (x : fin (2*b + 2)) (j k : ℤ)

  -- Definition 4.1

def XbackXforth : fin (2*b + 2) → fin (2*b + 2) :=
  π ∘ (xor_one b) ∘ ⇑(π⁻¹) ∘ (xor_one b)

def XbackXforth_inv : fin (2*b + 2) → fin (2*b + 2) :=
  (xor_one b) ∘ π ∘ (xor_one b) ∘ ⇑(π⁻¹) 

lemma XbackXforth_inv_left_inv
  : function.left_inverse (XbackXforth_inv π) (XbackXforth π) :=
begin
  intro x, simp [XbackXforth, XbackXforth_inv],
  rw [xor_one_involutive, equiv.perm.apply_inv_self, xor_one_involutive],
end

lemma XbackXforth_inv_right_inv
  : function.right_inverse (XbackXforth_inv π) (XbackXforth π) :=
begin
  intro x, simp [XbackXforth, XbackXforth_inv],
  rw [xor_one_involutive, equiv.perm.inv_apply_self, xor_one_involutive,
  equiv.perm.apply_inv_self]
end

  -- Theorem 4.2, which constructs the corresponding permutation.

def XbackXforth_perm : perm ( fin (2*b + 2) ) :=
  ⟨_, _, XbackXforth_inv_left_inv π, XbackXforth_inv_right_inv π⟩

 -- Simp lemma which shows that the permutation coerces to the function.

theorem coe_XbackXforth_perm_eq_XbackXforth
  : ⇑(XbackXforth_perm π) = XbackXforth π :=
begin
  ext, simp [XbackXforth, XbackXforth_perm],
end

lemma ex_kay_plus_one: (((XbackXforth_perm π) ^ (k + 1)) x) =
  (XbackXforth_perm π) (((XbackXforth_perm π) ^ k) x) :=
  (by {repeat {rw ex_kay}, rw [← gpow_one (XbackXforth_perm π),
      gpow_add, mul_apply, equiv.perm.gpow_apply_comm, gpow_one]} )

lemma XbackXforth_pow_pow_step_up : (XbackXforth_perm π) ( (xor_one_perm b)
  (((XbackXforth_perm π) ^ (k + 1)) x) ) =
    (xor_one_perm b) (((XbackXforth_perm π) ^ k) x) :=
begin
  rw [ex_kay_plus_one, XbackXforth_perm, equiv.coe_fn_mk,
  xor_one_perm_eq_xor_one],
  simp [XbackXforth, XbackXforth_inv],
  rw [xor_one_involutive, equiv.perm.inv_apply_self, xor_one_involutive,
  equiv.perm.apply_inv_self],
end

lemma XbackXforth_pow_pow_step_down : (XbackXforth_perm π)⁻¹ ( (xor_one_perm b)
  (((XbackXforth_perm π) ^ k) x) ) =
    (xor_one_perm b) (((XbackXforth_perm π) ^ (k + 1)) x) :=
begin
  rw equiv.perm.inv_def, rw [ex_kay_plus_one, XbackXforth_perm, equiv.coe_fn_mk,
  xor_one_perm_eq_xor_one],
  simp [XbackXforth, XbackXforth_inv],
end

  -- Part one of Theorem 4.3

theorem XbackXforth_pow_pow :
  ( (XbackXforth_perm π) ^ k) ((xor_one_perm b)
     (((XbackXforth_perm π) ^ k) x)) = (xor_one_perm b) x := 
begin
  cases k,
  { rw int.of_nat_eq_coe, induction k with k hk,
    { simp, },
    {  rwa [int.coe_nat_succ, gpow_add, equiv.perm.coe_mul, function.comp_app,
      ← equiv.perm.coe_mul, ← gpow_add, gpow_one, XbackXforth_pow_pow_step_up],
    }
  },
  { rw int.neg_succ_of_nat_coe', induction k with k hk,
    { exact (XbackXforth_pow_pow_step_down π x (-1)) },
    { rwa [int.coe_nat_succ, neg_add_rev, int.add_sub_assoc, add_comm (-1 : ℤ),
      gpow_add, equiv.perm.coe_mul, function.comp_app, ← equiv.perm.coe_mul,
      ← gpow_add, gpow_neg, gpow_one, int.add_neg_one,
      XbackXforth_pow_pow_step_down, sub_add_cancel],
    }
  },
end

  -- Lemma on pairs in ℤ which lets us take a "minimum pair".

lemma min_prop_pairs { p : ℤ → ℤ → Prop }
  ( p_symm : ∀ {j k : ℤ}, p j k → p k j ) 
    (p_sat : ∃ j k : ℤ, p j k) :
      ∃ j k : ℤ, j ≤ k ∧ p j k ∧ 
        (∀ j' k' : ℤ, j' ≤ k' -> k' - j' < k - j ->  ¬p j' k') :=
begin
  let P : set ℕ := { n : ℕ | ∃ j k : ℤ, j ≤ k ∧ p j k ∧ k - j = n},
  have hP : P.nonempty,
  { rcases p_sat with ⟨j, k, hpjk⟩,
    cases (le_or_lt j k),
    { exact ⟨(k - j).nat_abs, j, k, h, hpjk, int.eq_nat_abs_of_zero_le 
      (sub_nonneg_of_le h)⟩ },
    { exact ⟨(j - k).nat_abs, k, j, int.le_of_lt h, p_symm hpjk,
      int.eq_nat_abs_of_zero_le (sub_nonneg_of_le (int.le_of_lt h))⟩,
    }
  },
  let n := (wo_set_is_wf P).min hP,
  have hn : n ∈ P := set.is_wf.min_mem _ _,
  have hn2 : ∀ m : ℕ, m < n → ¬ m ∈ P,
  { intros _ lt_n m_in_P,
    apply set.is_wf.not_lt_min (wo_set_is_wf P) hP m_in_P lt_n,
  },
  rcases (set.is_wf.min_mem _ hP) with ⟨j ,k, hjk, hpjk, hjkn⟩,
  use [j, k, hjk, hpjk],
  intros j' k' j'_le_k' hlt,
  let m := (k' - j').nat_abs,
  have hm : k' - j' = m :=
    int.eq_nat_abs_of_zero_le(sub_nonneg_of_le j'_le_k'),
  have hmn : m < n,
  { rw [hjkn, hm] at hlt,
    rwa ← int.coe_nat_lt,
  },
  exact λ h, (hn2 m hmn) ⟨j', k',  j'_le_k', h, hm⟩,
end

  -- Part 2 of Theorem 4.3

theorem ex_jay_neq_xor_one_ex_kay :
  ∀ j k : ℤ, (((XbackXforth_perm π) ^ j) x) ≠ (xor_one_perm b)
    (((XbackXforth_perm π) ^ k) x) :=
begin
  rintro j' k' hjk',
  have p_symm : ∀ j k : ℤ, (XbackXforth_perm π ^ j) x = (xor_one_perm b)
    ((XbackXforth_perm π ^ k) x)
      → (XbackXforth_perm π ^ k) x = (xor_one_perm b)
        ((XbackXforth_perm π ^ j) x),
  { intros _ _,
    { intro h,
      rw xor_one_perm_eq_xor_one at h ⊢,
      apply (xor_one_involutive b).injective,
      rw [(xor_one_involutive b), h],
    },
  },
  rcases (min_prop_pairs p_symm ⟨_, _, hjk'⟩) with ⟨j, k, j_le_k, hjk, min_jk⟩,
  clear' j' k' hjk',
  have ge_add_two_or_succ_or_eq_of_le :
    ∀ a b : ℤ, a ≤ b → (b = a) ∨ (b = a + 1) ∨ (a + 2 ≤ b),
  { intros a b hab,
    rcases int.eq_coe_of_zero_le (int.sub_nonneg_of_le hab) with ⟨_ | _ | n, hn⟩,
    { left, rwa [int.coe_nat_zero, sub_eq_zero] at hn },
    { right, left, rwa [int.coe_nat_one, sub_eq_iff_eq_add'] at hn },
    { right, right, apply int.add_le_of_le_sub_left,
      apply le_of_sub_nonneg,
      rw int.coe_nat_succ at hn, rw int.coe_nat_succ at hn,
      rw add_assoc at hn, rw one_add_one_eq_two at hn,
      rw ← sub_eq_iff_eq_add at hn, rw hn, exact int.coe_zero_le _,
    }
  },
  rcases (ge_add_two_or_succ_or_eq_of_le  _ _ j_le_k)
    with rfl | rfl | j_add_two_le_k,
  { rw (xor_one_perm_eq_xor_one) at hjk,
    exact (ne_xor_one _ hjk),
  },
  { refine ne_xor_one (π⁻¹ ((XbackXforth_perm π ^ (1 + j)) x)) _,
    conv begin
      congr,
      { rw [gpow_add, gpow_one, equiv.perm.coe_mul, ← equiv.coe_trans,
        trans_apply,
        hjk, ← add_comm (1 : ℤ), ← trans_apply, equiv.coe_trans,
        ← equiv.coe_trans (XbackXforth_perm π),
        ← trans_apply (xor_one_perm b), equiv.coe_trans, equiv.coe_trans],
      },
      { rw [← xor_one_perm_eq_xor_one, ← trans_apply _ (xor_one_perm b),
        equiv.coe_trans]
      },
    end,
    apply (congr _ (eq.refl _)),
    rw [coe_XbackXforth_perm_eq_XbackXforth, xor_one_perm_eq_xor_one,
    XbackXforth],
    conv begin
      to_lhs,
      rw [← comp.assoc _ _ (xor_one b ∘ ⇑π⁻¹ ∘ xor_one b), comp.assoc],
      congr,
      { rw [ ← equiv.perm.coe_mul, mul_left_inv, equiv.perm.coe_one] },
      { rw comp.assoc _ _ (xor_one b),
        congr, skip, rw comp.assoc,
        congr, skip, rw function.involutive.comp_self (xor_one_involutive b)
      }
    end,
    rw [comp.right_id, comp.left_id]
  },
  { refine min_jk (j + 1) (k - 1) (by linarith) (by linarith) _,
    rw [← XbackXforth_pow_pow_step_up, sub_add_cancel, ← hjk,
    ← trans_apply, equiv.coe_trans, ← equiv.perm.coe_mul,
    ← add_comm (1 : ℤ), gpow_add, gpow_one]
  }
end

  -- Part 3 of Theorem 4.3

theorem cycle_size_bound :
  (of_fintype (cycle (XbackXforth_perm π) x)).to_finset.card ≤ b + 1 :=
begin
  let s_0 := (of_fintype (cycle (XbackXforth_perm π) x)).to_finset,
  let s_1 := finset.image (xor_one_perm b) s_0,
  have union_bound := le_trans (finset.card_le_univ (s_0 ∪ s_1))
      (le_of_eq (fintype.card_fin _)),
  have disj : disjoint s_0 s_1, 
  { simp [finset.disjoint_iff_disjoint_coe, set.disjoint_left],
    rintros rfl ⟨j, hj⟩ _ ⟨k, rfl⟩ hk,
    exact ex_jay_neq_xor_one_ex_kay π x _ _ hj
  },
  have card_equal : s_1.card = s_0.card :=
    finset.card_image_of_inj_on (function.injective.inj_on
      (function.involutive.injective (xor_one_involutive _)) _),
  rw [finset.card_union_eq disj, card_equal, ← two_mul s_0.card] at union_bound,
  conv at union_bound begin to_rhs, congr, skip, rw ← mul_one 2, end,
  conv at union_bound begin to_rhs, rw ← mul_add, end,
  exact (mul_le_mul_left (zero_lt_two)).mp union_bound,
end

  -- Theorem 4.4

theorem cyclemin_xor_one_commutes :
  function.commute (cyclemin (XbackXforth_perm π)) (xor_one b) := 
begin
  intros x,
  rcases (set.is_wf.min_mem (wo_set_is_wf _)
    (cycle_nonempty (XbackXforth_perm π) x)) with ⟨j, hj⟩,
  rcases (set.is_wf.min_mem (wo_set_is_wf _)
    (cycle_nonempty (XbackXforth_perm π) (xor_one b x))) with ⟨k, hk⟩,
  apply le_antisymm,
  { apply cyclemin_le,
    rw cyclemin,
    use (-j), rw ← hj,
    apply equiv.injective ((XbackXforth_perm π) ^ j),
    rw [← xor_one_perm_eq_xor_one, XbackXforth_pow_pow],
    simp only [equiv.apply_eq_iff_eq, gpow_neg, equiv.perm.apply_inv_self],
  },
  { 
    rw [cyclemin, cyclemin, ← hk, ← hj],
    by_contradiction, push_neg at h,
    have k_xor_eq_xor_minus_k : (XbackXforth_perm π ^ k) (xor_one b x)
      = (xor_one b) ((XbackXforth_perm π ^ -k) x),
    { apply equiv.injective ((XbackXforth_perm π) ^ - k),
      rw [← xor_one_perm_eq_xor_one, XbackXforth_pow_pow],
      simp only [equiv.apply_eq_iff_eq, gpow_neg, equiv.perm.inv_apply_self],
    },
    rw k_xor_eq_xor_minus_k at h,
    have cyclemin_bound
      : (XbackXforth_perm π ^ j) x ≤ (XbackXforth_perm π ^ -k) x,
    { rw hj,
      apply cyclemin_le,
      use -k,
    },
    exact ex_jay_neq_xor_one_ex_kay π x j (-k)
    (xor_one_trap _ _ h cyclemin_bound),
  },
end

end part_four

section part_five
variables {b : ℕ} (π : perm ( fin (2*b + 2) ))
variables (x : fin (2*b + 2)) (s : fin (b + 1) → fin 2) 

  /-
    Note that all of these definitions (from Definition 5.1) will be
    noncomputable because they use cyclemin. But we can use Theorem 2.5 and
    Theorem 4.3 to get round this...
  -/

noncomputable def firstcontrol : fin (b + 1) → fin 2 :=
  fin.mod_two ∘ (cyclemin (XbackXforth_perm π)) ∘ fin.mul_two

noncomputable def F_perm : perm ( fin (2*b + 2) ) := Xif_s_perm (firstcontrol π)

noncomputable def lastcontrol : fin (b + 1) → fin 2 :=
  fin.mod_two ∘ (F_perm π) ∘ π ∘ fin.mul_two

noncomputable def L_perm : perm ( fin (2*b + 2) ) := Xif_s_perm (lastcontrol π)

noncomputable def middleperm : fin (2*b + 2) → fin (2*b + 2) :=
  (F_perm π) ∘ π ∘ (L_perm π)

  -- Theorem 5.2

theorem firstcontrol_zero_eq_zero : (firstcontrol π) 0 = 0 :=
begin
  rw firstcontrol, rw comp_apply, rw comp_apply,
  rw fin.mul_two, simp only [fin.mul_two, fin.mk_zero, fin.coe_zero, mul_zero],
  have q : cyclemin (XbackXforth_perm π) 0 = 0,
  { rw cyclemin, apply le_antisymm,
    { apply set.is_wf.min_le,
      use 0, simp only [id.def, gpow_zero, equiv.perm.coe_one],
    },
    { exact nat.zero_le _ }
  },
  rw q, rw fin.mod_two, simp only [fin.mk_zero, fin.coe_zero, nat.zero_mod],
end

  -- Theorem 5.3

theorem F_perm_eq_cyclemin_upto_parity :
  fin.mod_two ∘ (F_perm π) = fin.mod_two ∘ (cyclemin (XbackXforth_perm π)) :=
begin
  ext1 x,
  rcases (fin_div_two_mul_two_related x) with x_eq | x_eq,
  { rw [comp_apply, comp_apply,
    F_perm, coe_Xif_s_perm_eq_Xif_s, Xif_s],
    split_ifs with h, 
    { rw [firstcontrol, comp_apply, comp_apply] at h,
      rw [x_eq, h, xor_one_mod_two, mul_two_mod_two_eq_zero, add_zero]
    },
    { rw [fin_two_not_one_iff_zero, firstcontrol, comp_apply,
      comp_apply, ← x_eq] at h,
      rw [h, x_eq, mul_two_mod_two_eq_zero]
    }
  },
  { rw [comp_apply, comp_apply, x_eq, cyclemin_xor_one_commutes,
    F_perm, coe_Xif_s_perm_eq_Xif_s, Xif_s],
    split_ifs with h,
    { rw [firstcontrol, comp_apply, comp_apply, ← x_eq] at h,
      rw [xor_one_involutive, mul_two_mod_two_eq_zero, xor_one_mod_two, h,
      fin.eq_iff_veq, fin.add_def, fin.val_zero', fin.val_one, nat.mod_self],
    },
    { rw [fin_two_not_one_iff_zero, firstcontrol, comp_apply,
      comp_apply, ← x_eq] at h,
      rw [xor_one_mod_two, xor_one_mod_two, mul_two_mod_two_eq_zero, h],
    }
  }
end

  -- Theorem 5.4

theorem L_perm_eq_F_π_perm_upto_parity :
  fin.mod_two ∘ (L_perm π) = fin.mod_two ∘ (F_perm π) ∘ π :=
begin
  ext1 x,
  rcases (fin_div_two_mul_two_related x) with x_eq | x_eq,
  { rw [L_perm, lastcontrol, coe_Xif_s_perm_eq_Xif_s, 
    comp_apply, comp_apply, comp_apply, Xif_s], split_ifs,
    { rw [comp_apply, ← comp.assoc, comp_apply, ← x_eq, comp_apply] at h,
      rw [xor_one_mod_two, h, x_eq, mul_two_mod_two_eq_zero, add_zero],
    },
    { rw [fin_two_not_one_iff_zero, ← comp.assoc, ← comp.assoc, comp_apply,
      ← x_eq, comp_apply, comp_apply] at h,
      rw [h, x_eq, mul_two_mod_two_eq_zero],
    }
  },
  { have bydef : (XbackXforth_perm π) ((xor_one b) (π ((xor_one b) x))) = (π x),
    { rw [coe_XbackXforth_perm_eq_XbackXforth, XbackXforth, function.comp_app,
      function.comp_app, function.comp_app, xor_one_involutive,
      equiv.perm.inv_apply_self, xor_one_involutive],
    },
    rw [← comp.assoc _ _ π, F_perm_eq_cyclemin_upto_parity, comp.assoc _ _ π,
    comp_apply, comp_apply, comp_apply, ← bydef, cyclemin_invariant_pi,
    cyclemin_xor_one_commutes, L_perm, lastcontrol, coe_Xif_s_perm_eq_Xif_s, 
    Xif_s], split_ifs,
    { rw [← comp.assoc _ (F_perm π) _, F_perm_eq_cyclemin_upto_parity,
      comp_apply, comp_apply, comp_apply] at h,
      rw [x_eq, xor_one_involutive, xor_one_mod_two, h, mul_two_mod_two_eq_zero,
      fin.eq_iff_veq, fin.add_def, fin.val_zero', fin.val_one, nat.mod_self],
    },
    { rw [fin_two_not_one_iff_zero, ← comp.assoc _ (F_perm π) _,
      F_perm_eq_cyclemin_upto_parity,
      comp_apply, comp_apply, comp_apply] at h,
      rw [x_eq, xor_one_mod_two, xor_one_mod_two, mul_two_mod_two_eq_zero,
      xor_one_involutive, h] 
    }
  },
end

  /-
    We define middleperm_perm as a perm and show it's equal to middleperm,
    for part one of Theorem 5.5.
  -/

noncomputable def middleperm_perm : perm ( fin (2*b + 2) )
  := (F_perm π) * π * (L_perm π)

theorem coe_middleperm_perm_eq_middleperm
  : ⇑(middleperm_perm π) = (middleperm π) := 
  (by {rw [middleperm, middleperm_perm, equiv.perm.coe_mul,
      equiv.perm.coe_mul]} )

  -- We show middleperm preserves parity for the second part of Theorem 5.5.

theorem middleperm_preserves_parity
  : fin.mod_two ∘ (middleperm_perm π) = fin.mod_two :=
begin
  rw coe_middleperm_perm_eq_middleperm, rw middleperm,
  rw ← comp.assoc, rw ← comp.assoc, rw comp.assoc _ _ π,
  rw ← L_perm_eq_F_π_perm_upto_parity, rw comp.assoc,
  rw L_perm, rw function.involutive.comp_self,
  { rw right_id },
  { rw coe_Xif_s_perm_eq_Xif_s, apply Xif_s_involutive }
end

  -- Under suitable conditions, we have computable versions of all the above.

def fast_firstcontrol (i : ℕ) (π : perm (fin (2*b + 2)))
  : fin (b + 1) → fin 2 :=
    fin.mod_two ∘ (fast_cyclemin i (XbackXforth_perm π)) ∘ fin.mul_two

def fast_F_perm (i : ℕ) (π : perm (fin (2*b + 2))) : perm (fin (2*b + 2))
  := Xif_s_perm (fast_firstcontrol i π)

def fast_lastcontrol (i : ℕ) (π : perm (fin (2*b + 2)))
  : fin (b + 1) → fin 2 :=
    fin.mod_two ∘ (fast_F_perm i π) ∘ π ∘ fin.mul_two

def fast_L_perm (i : ℕ) (π : perm (fin (2*b + 2))) : perm (fin (2*b + 2))
  := Xif_s_perm (fast_lastcontrol i π)

def fast_middleperm (i : ℕ) (π : perm (fin (2*b + 2)))
  : fin (2*b + 2) → fin (2*b + 2)
    := (fast_F_perm i π) ∘ π ∘ (fast_L_perm i π)

def fast_middleperm_perm (i : ℕ) (π : perm (fin (2*b + 2)))
  : perm (fin (2*b + 2)) :=
  (fast_F_perm i π) * π * (fast_L_perm i π)

@[simp]
theorem fast_firstcontrol_eq_firstcontrol {i : ℕ} (h : b + 1 ≤ 2^i)
  : fast_firstcontrol i π = firstcontrol π := 
begin
  ext1 y, simp [fast_firstcontrol, firstcontrol], 
  rw fast_cyclemin_eq_cyclemin y.mul_two
  (le_trans (cycle_size_bound π (fin.mul_two y)) h) 
end

@[simp]
theorem fast_F_perm_eq_F_perm {i : ℕ} (h : b + 1 ≤ 2^i)
  : fast_F_perm i π = F_perm π
    := (by {ext, simp [h, fast_F_perm, F_perm, Xif_s]} )

@[simp]
theorem fast_lastcontrol_eq_lastcontrol {i : ℕ} (h : b + 1 ≤ 2^i)
  : fast_lastcontrol i π = lastcontrol π
    := (by {ext, simp [h, fast_lastcontrol, lastcontrol]} )

@[simp]
theorem fast_L_perm_eq_L_perm {i : ℕ} (h : b + 1 ≤ 2^i)
  : fast_L_perm i π = L_perm π
    := (by {ext, simp [h, fast_L_perm, L_perm, Xif_s]} )


@[simp]
theorem fast_middleperm_eq_middleperm {i : ℕ} (h : b + 1 ≤ 2^i)
  : fast_middleperm i π = middleperm π
    := (by {ext, simp [h, fast_middleperm, middleperm]} )

def π_even : fin (b + 1) -> fin (b + 1) :=
  fin.div_two ∘ π ∘ fin.mul_two

def π_odd : fin (b + 1) -> fin (b + 1) :=
  fin.div_two ∘ π ∘ (xor_one b) ∘ fin.mul_two

def π_even_inv : fin (b + 1) -> fin (b + 1) :=
  fin.div_two ∘ (xor_one b) ∘ ⇑(π⁻¹) ∘ fin.mul_two

def π_odd_inv : fin (b + 1) -> fin (b + 1) :=
  fin.div_two ∘ ⇑(π⁻¹) ∘ fin.mul_two

theorem π_even_left_inverse (h : fin.mod_two ∘ π = fin.mod_two)
  : function.left_inverse (π_even_inv π) (π_even π) :=
begin
  intro x, unfold π_even π_even_inv, sorry
end

end part_five


