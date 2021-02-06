import game.world_02_addition
namespace mynat

lemma zero_mul (m : mynat) : 0 * m = 0 := begin[nat_num_game]
  induction m,
  rwa mul_zero,
end

lemma mul_one (m : mynat) : m * 1 = m := begin[nat_num_game]
  induction m,
  rwa zero_mul,
  rwa [one_eq_succ_zero, mul_succ, mul_zero, zero_add],
end

lemma one_mul (m : mynat) : 1 * m = m := begin[nat_num_game]
  induction m,
  rwa mul_zero,
  rwa [mul_succ, succ_eq_add_one, m_ih],
end

lemma mul_add (t a b : mynat) : t * (a + b) = t * a + t * b := begin[nat_num_game]
  induction a,
  rwa [mul_zero, zero_add, zero_add],
  rwa [mul_succ, succ_add, mul_succ, a_ih, add_right_comm],
end

lemma mul_assoc (a b c : mynat) : (a * b) * c = a * (b * c) := begin[nat_num_game]
  induction c,
  refl,
  rwa [mul_succ, mul_succ, mul_add, c_ih],
end

lemma succ_mul (a b : mynat) : succ a * b = a * b + b := begin[nat_num_game]
  induction b,
  rwa [add_zero, mul_zero, mul_zero],
  rwa [mul_succ, mul_succ, b_ih, add_succ, add_succ, add_right_comm],
end

lemma add_mul (a b t : mynat) : (a + b) * t = a * t + b * t := begin[nat_num_game]
  induction t,
  rwa [mul_zero, mul_zero, mul_zero, add_zero],
  rwa [
    mul_succ, mul_succ, mul_succ, t_ih,
    add_assoc(a * t_n), add_assoc(a * t_n),
    add_comm(a), add_comm(a), add_assoc
  ],
end

lemma mul_comm (a b : mynat) : a * b = b * a := begin[nat_num_game]
  induction b,
  rwa [mul_zero, zero_mul],
  rwa [mul_succ, succ_mul, b_ih],
end

lemma mul_left_comm (a b c : mynat) : a * (b * c) = b * (a * c) := begin[nat_num_game]
  induction c,
  rwa [mul_zero, mul_zero, mul_zero],
  rwa [
    mul_succ, mul_succ, mul_add, mul_add, c_ih,
    mul_comm(b), mul_comm(b)
  ],
end

end mynat
