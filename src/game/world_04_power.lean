import game.world_03_multiplication
import mynat.pow
namespace mynat
def two_eq_succ_one : (2 : mynat) = succ 1 := rfl

lemma zero_pow_zero : (0 : mynat) ^ (0 : mynat) = 1 := begin[nat_num_game]
  rwa pow_zero,
end

lemma zero_pow_succ (m : mynat) : (0 : mynat) ^ (succ m) = 0 := begin[nat_num_game]
  rwa [pow_succ, mul_zero],
end

lemma pow_one (a : mynat) : a ^ (1 : mynat) = a := begin[nat_num_game]
  rwa [one_eq_succ_zero, pow_succ, pow_zero, one_mul],
end

lemma one_pow (m : mynat) : (1 : mynat) ^ m = 1 := begin[nat_num_game]
  induction m,
  rwa pow_zero,
  rwa [pow_succ, mul_one],
end

lemma pow_add (a m n : mynat) : a ^ (m + n) = a ^ m * a ^ n := begin[nat_num_game]
  induction n,
  rwa [pow_zero, add_zero, mul_one],
  rwa [add_succ, pow_succ, pow_succ, n_ih, mul_assoc],
end

lemma mul_pow (a b n : mynat) : (a * b) ^ n = a ^ n * b ^ n := begin[nat_num_game]
  induction n,
  rwa [pow_zero, pow_zero, pow_zero, mul_one],
  rwa [
    pow_succ, pow_succ, pow_succ, n_ih,
    mul_assoc(a ^ n_n), mul_assoc(a ^ n_n), mul_comm(a), mul_comm(a), mul_assoc
  ],
end

lemma pow_pow (a m n : mynat) : (a ^ m) ^ n = a ^ (m * n) := begin[nat_num_game]
  induction n,
  rwa [mul_zero, pow_zero, pow_zero],
  rwa [mul_succ, pow_add, pow_succ, n_ih],
end

lemma add_squared (a b : mynat) :
    (a + b) ^ (2 : mynat) = a ^ (2 : mynat) + b ^ (2 : mynat) + 2 * a * b := begin[nat_num_game]
  rwa [
    two_eq_succ_one, one_eq_succ_zero,
    pow_succ, pow_succ, pow_succ, pow_succ, pow_succ, pow_succ,
    pow_zero, pow_zero, pow_zero,
    one_mul, one_mul, one_mul,
    succ_mul, succ_mul,
    zero_mul, zero_add,
    add_mul, add_mul,
    mul_add, mul_add,
    add_assoc, add_assoc,
    add_comm(b*b), add_assoc, mul_comm(b)
  ],
end

end mynat
