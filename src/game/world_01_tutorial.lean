import mynat.definition
import mynat.mul

namespace mynat

lemma example1 (x y z : mynat) : x * y + z = x * y + z := begin[nat_num_game]
  refl,
end

lemma example2 (x y : mynat) (h : y = x + 7) : 2 * y = 2 * (x + 7) := begin[nat_num_game]
  rwa h,
end

lemma example3 (a b : mynat) (h : succ a = b) : succ(succ(a)) = succ(b) := begin[nat_num_game]
  rwa h,
end

lemma add_succ_zero (a : mynat) : a + succ(0) = succ(a) := begin[nat_num_game]
  rwa [add_succ, add_zero],
end

end mynat
