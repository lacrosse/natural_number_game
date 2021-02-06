import game.world_01_tutorial
namespace mynat

lemma zero_add (n : mynat) : 0 + n = n := begin[nat_num_game]
  induction n,
  rwa add_zero,
  rwa [add_succ, n_ih],
end

lemma add_assoc (a b c : mynat) : (a + b) + c = a + (b + c) := begin[nat_num_game]
  induction c,
  rwa [add_zero, add_zero],
  rwa [add_succ, add_succ, add_succ, c_ih],
end

lemma succ_add (a b : mynat) : succ a + b = succ (a + b) := begin[nat_num_game]
  induction b,
  rwa [add_zero, add_zero],
  rwa [add_succ, add_succ, b_ih],
end

lemma add_comm (a b : mynat) : a + b = b + a := begin[nat_num_game]
  induction b,
  rwa [add_zero, zero_add],
  rwa [add_succ, succ_add, b_ih],
end

theorem succ_eq_add_one (n : mynat) : succ n = n + 1 := begin[nat_num_game]
  induction n,
  rwa [one_eq_succ_zero, add_succ, add_zero],
  rwa [succ_add, n_ih],
end

lemma add_right_comm (a b c : mynat) : a + b + c = a + c + b := begin[nat_num_game]
  rwa [add_assoc, add_assoc, add_comm(b)],
end

end mynat
