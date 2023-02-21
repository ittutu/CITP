constants F G : ℕ → ℕ 

axiom f1 (x) : x ≤ 7 → F(x) = 5
axiom f2 (x) : 7 < x → F(x) = 1

axiom g1 (y) : y ≤ 4 → G(y) = 2
axiom g2 (y) : 4 < y → G(y) = 7

attribute [simp] f1 f2 g1 g2

axiom leqorgt (x y : ℕ) : x ≤ y ∨ y < x

theorem fg (x) : 9 ≤ G(F(x)) + G(x) :=
begin
 cases leqorgt x 7 with hx7,
 simp [hx7],
 cases leqorgt x 4 with hx4, 
 -- x ≤ 7 ∧ x ≤ 4
 simp [hx4],
 rw g2,
 comp_val,
 -- x ≤ 7 ∧ x > 4
 simp [h],
 rw g2,
 apply @nat.le.intro _ _ 5,
 simp,
 comp_val,
 simp [h],
 rw g1,
 cases leqorgt x 4 with hx4bis, 
 -- x > 7 ∧ x ≤ 4
 have transform := le_of_lt h,
 have transi := le_trans transform hx4bis,
 have turn_back := not_lt_of_ge transi,
 exfalso,
 apply turn_back,
 comp_val, 
 -- x > 7 ∧ x > 4
 simp [h_1],
 apply @nat.le.intro _ _ 3,
 simp,
end
