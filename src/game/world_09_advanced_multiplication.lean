import game.world_08_advanced_addition
namespace mynat

theorem mul_pos (a b : mynat) : a ≠ 0 → b ≠ 0 → a * b ≠ 0 := begin[nat_num_game]
  intros anz bnz f,
  cases b, {
    apply bnz,
    refl
  }, {
    rw mul_succ at f,
    apply anz,
    induction a,
    refl, {
      apply add_left_eq_zero,
      rwa f,
    }
  }
end

theorem eq_zero_or_eq_zero_of_mul_eq_zero (a b : mynat) (h : a * b = 0) : a = 0 ∨ b = 0 := begin[nat_num_game]
  induction b, {
    right,
    refl
  }, {
    left,
    rw mul_succ at h,
    apply add_left_eq_zero,
    apply h
  }
end

theorem mul_eq_zero_iff (a b : mynat): a * b = 0 ↔ a = 0 ∨ b = 0 := begin[nat_num_game]
  split,
  apply eq_zero_or_eq_zero_of_mul_eq_zero, {
    intro or_eq_zero,
    cases or_eq_zero,
    rwa [or_eq_zero, zero_mul],
    rwa [or_eq_zero, mul_zero],
  }
end

theorem mul_left_cancel (a b c : mynat) (ha : a ≠ 0) : a * b = a * c → b = c := begin[nat_num_game]
  induction c generalizing b, {
    rw mul_zero,
    intro h,
    cases eq_zero_or_eq_zero_of_mul_eq_zero _ _ h, {
      exfalso,
      exact ha h_1
    }, exact h_1
  }, {
    intro eq,
    cases b, {
      rw mul_zero at eq,
      exfalso,
      apply ha,
      symmetry at eq,
      cases eq_zero_or_eq_zero_of_mul_eq_zero _ _ eq,
      exact h, {
        exfalso,
        exact succ_ne_zero _ h,
      }
    },{
      have hyp : b = c_n, {
        apply c_ih,
        rw mul_succ at eq,
        rw mul_succ at eq,
        apply add_right_cancel _ _ _ eq,
      },
      rwa hyp,
    }
  }
end

end mynat
