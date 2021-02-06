import game.world_07_advanced_proposition
namespace mynat

theorem succ_inj' {a b : mynat} (hs : succ(a) = succ(b)) :  a = b := begin[nat_num_game]
  exact succ_inj hs,
end

theorem succ_succ_inj {a b : mynat} (h : succ(succ(a)) = succ(succ(b))) : a = b := begin[nat_num_game]
  apply succ_inj ∘ succ_inj,
  exact h,
end

theorem succ_eq_succ_of_eq {a b : mynat} : a = b → succ(a) = succ(b) := begin[nat_num_game]
  intro h,
  rwa h,
end

theorem succ_eq_succ_iff (a b : mynat) : succ a = succ b ↔ a = b := begin[nat_num_game]
  split,
  exact succ_inj,
  exact succ_eq_succ_of_eq,
end

theorem add_right_cancel (a t b : mynat) : a + t = b + t → a = b := begin[nat_num_game]
  intro h,
  induction t,
  rwa add_zero at h, {
    apply t_ih,
    rwa [add_succ, add_succ] at h,
    cc
  }
end

theorem add_left_cancel (t a b : mynat) : t + a = t + b → a = b := begin[nat_num_game]
  rw [add_comm t, add_comm t],
  apply add_right_cancel,
end

theorem add_right_cancel_iff (t a b : mynat) :  a + t = b + t ↔ a = b := begin[nat_num_game]
  split,
  apply add_right_cancel, {
    intro h,
    rwa h,
  }
end

lemma eq_zero_of_add_right_eq_self {a b : mynat} : a + b = a → b = 0 := begin[nat_num_game]
  intros h,
  induction a, {
    rw zero_add at h,
    apply h
  }, {
    apply a_ih,
    rw succ_add at h,
    apply succ_inj h
  }
end

theorem succ_ne_zero (a : mynat) : succ a ≠ 0 := begin[nat_num_game]
  symmetry,
  apply zero_ne_succ,
end

lemma add_left_eq_zero {{a b : mynat}} (H : a + b = 0) : b = 0 := begin[nat_num_game]
  cases b,
  refl, {
    exfalso,
    rw add_succ at H,
    apply succ_ne_zero,
    apply H
  }
end

lemma add_right_eq_zero {a b : mynat} : a + b = 0 → a = 0 := begin[nat_num_game]
  rw add_comm,
  apply add_left_eq_zero,
end

theorem add_one_eq_succ (d : mynat) : d + 1 = succ d := begin[nat_num_game]
  symmetry,
  apply succ_eq_add_one,
end

lemma ne_succ_self (n : mynat) : n ≠ succ n := begin[nat_num_game]
  induction n,
  apply zero_ne_succ, {
    intro h,
    apply n_ih,
    apply succ_inj,
    apply h
  }
end

end mynat
