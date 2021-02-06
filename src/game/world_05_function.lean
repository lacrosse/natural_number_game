import game.world_04_power
namespace mynat

example (P Q : Type) (p : P) (h : P → Q) : Q := begin[nat_num_game]
  exact h p,
end

example : mynat → mynat := begin[nat_num_game]
  intro p,
  exact 3 * p + 2,
end

example (P Q R S T U: Type) (p : P) (h : P → Q) (i : Q → R) (j : Q → T) (k : S → T) (l : T → U) : U := begin[nat_num_game]
  apply l ∘ j ∘ h,
  exact p,
end

example (P Q : Type) : P → (Q → P) := begin[nat_num_game]
  intros p _,
  exact p,
end

example (P Q R : Type) : (P → (Q → R)) → ((P → Q) → (P → R)) := begin[nat_num_game]
  intros f g p,
  apply f p,
  apply g p,
end

example (P Q F : Type) : (P → Q) → ((Q → F) → (P → F)) := begin[nat_num_game]
  intros g h,
  apply h ∘ g,
end

example (P Q : Type) : (P → Q) → ((Q → empty) → (P → empty)) := begin[nat_num_game]
  intros f g,
  exact g ∘ f,
end

example (A B C D E F G H I J K L : Type)
    (f1 : A → B) (f2 : B → E) (f3 : E → D) (f4 : D → A) (f5 : E → F) (f6 : F → C) (f7 : B → C) (f8 : F → G)
    (f9 : G → J) (f10 : I → J) (f11 : J → I) (f12 : I → H) (f13 : E → H) (f14 : H → K) (f15 : I → L)
    : A → L := begin[nat_num_game]
  apply f15 ∘ f11 ∘ f9 ∘ f8 ∘ f5 ∘ f2 ∘ f1,
end

end mynat
