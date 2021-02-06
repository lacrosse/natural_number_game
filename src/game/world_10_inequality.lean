-- Game axiomatics

import game.world_09_advanced_multiplication
import mynat.le
namespace mynat

lemma one_add_le_self (x : mynat) : x ≤ 1 + x := begin[nat_num_game]
  use 1,
  apply add_comm,
end

lemma le_refl (x : mynat) : x ≤ x := begin[nat_num_game]
  use 0,
  refl,
end

attribute [refl] mynat.le_refl

theorem le_succ (a b : mynat) : a ≤ b → a ≤ (succ b) := begin[nat_num_game]
  intro h,
  cases h,
  rw h_h,
  use succ h_w,
  refl,
end

lemma zero_le (a : mynat) : 0 ≤ a := begin[nat_num_game]
  induction a,
  refl, {
    cases a_ih,
    rw a_ih_h,
    use succ a_ih_w,
    refl
  }
end

theorem le_trans (a b c : mynat) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := begin[nat_num_game]
  cases hab,
  cases hbc,
  rw hab_h at hbc_h,
  use hab_w + hbc_w,
  rw add_assoc at hbc_h,
  apply hbc_h,
end

theorem le_antisymm (a b : mynat) (hab : a ≤ b) (hba : b ≤ a) : a = b := begin[nat_num_game]
  cases hab,
  cases hba,
  rw [hab_h, add_assoc] at hba_h,
  symmetry at hba_h,
  have w_sum_eq_zero_h := eq_zero_of_add_right_eq_self hba_h,
  have hab_w_eq_zero := add_right_eq_zero w_sum_eq_zero_h,
  rw [hab_w_eq_zero, add_zero] at hab_h,
  rwa [hab_h],
end

lemma le_zero (a : mynat) (h : a ≤ 0) : a = 0 := begin[nat_num_game]
  induction a,
  refl, {
    exfalso,
    cases h,
    symmetry at h_h,
    apply succ_ne_zero,
    exact add_right_eq_zero h_h,
  }
end

lemma succ_le_succ (a b : mynat) (h : a ≤ b) : succ a ≤ succ b := begin[nat_num_game]
  cases h,
  use h_w,
  rwa [succ_add, h_h],
end

theorem le_total (a b : mynat) : a ≤ b ∨ b ≤ a := begin[nat_num_game]
  induction b generalizing a, {
    right,
    apply zero_le,
  }, {
    cases a, {
      left,
      apply zero_le,
    }, {
      cases b_ih a, {
        left,
        apply succ_le_succ,
        exact h
      }, {
        right,
        apply succ_le_succ,
        exact h
      }
    }
  }
end

instance : linear_order mynat := by structure_helper

lemma le_succ_self (a : mynat) : a ≤ succ a := begin[nat_num_game]
  apply le_succ,
  apply le_refl,
end

theorem add_le_add_right {a b : mynat} : a ≤ b → ∀ t, (a + t) ≤ (b + t) := begin[nat_num_game]
  intros h t,
  induction t,
  rwa [add_zero], {
    rwa [add_succ, add_succ],
    apply succ_le_succ,
    exact t_ih,
  }
end

theorem le_of_succ_le_succ (a b : mynat) : succ a ≤ succ b → a ≤ b := begin[nat_num_game]
  intro h,
  cases h,
  use h_w,
  rw [succ_add, succ_eq_succ_iff] at h_h,
  apply h_h,
end

theorem not_succ_le_self (a : mynat) : ¬ (succ a ≤ a) := begin[nat_num_game]
  intro h,
  induction a, {
    cases h,
    rw succ_add at h_h,
    apply zero_ne_succ,
    apply h_h,
  }, {
    apply a_ih,
    apply le_of_succ_le_succ,
    apply h,
  }
end

theorem add_le_add_left {a b : mynat} (h : a ≤ b) (t : mynat) : t + a ≤ t + b := begin[nat_num_game]
  induction t, {
    rwa [zero_add, zero_add]
  }, {
    rw [succ_add, succ_add],
    apply succ_le_succ,
    apply t_ih
  }
end

lemma lt_aux_one (a b : mynat) : a ≤ b ∧ ¬ (b ≤ a) → succ a ≤ b := begin[nat_num_game]
  intro h,
  cases h,
  cases h_left,
  cases h_left_w, {
    exfalso,
    apply h_right,
    rwa h_left_h,
    refl,
  }, {
    rw h_left_h,
    use h_left_w,
    rwa [add_succ, succ_add],
  }
end

end mynat
