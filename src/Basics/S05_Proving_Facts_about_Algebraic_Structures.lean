import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)


#check (inf_comm x y : x ⊓ y = y ⊓ x)
#check (inf_assoc x y z : x ⊓ y ⊓ z = x ⊓ (y ⊓ z))
#check (sup_comm x y : x ⊔ y = y ⊔ x)
#check (sup_assoc x y z : x ⊔ y ⊔ z = x ⊔ (y ⊔ z))
#check (inf_sup_self : x ⊓ (x ⊔ y) = x)
#check (sup_inf_self : x ⊔ x ⊓ y = x)



example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  · apply le_inf
    · exact inf_le_right
    · exact inf_le_left
  · apply le_inf
    · exact inf_le_right
    · exact inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · apply le_inf
    · apply le_trans inf_le_left inf_le_left
    · apply le_inf
      · apply le_trans inf_le_left inf_le_right
      · apply inf_le_right
  · apply le_inf
    · apply le_inf
      · apply inf_le_left
      · apply le_trans inf_le_right inf_le_left
    · apply le_trans inf_le_right inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  · apply sup_le
    · apply le_sup_right
    · apply le_sup_left
  · apply sup_le
    · apply le_sup_right
    · apply le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  · apply sup_le
    · apply sup_le
      · apply le_sup_left
      · apply le_trans le_sup_left le_sup_right
    · apply le_trans le_sup_right le_sup_right
  · apply sup_le
    · apply le_trans le_sup_left le_sup_left
    · apply sup_le
      · apply le_trans le_sup_right le_sup_left
      · apply le_sup_right


theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · apply inf_le_left
  · apply le_inf
    · apply le_refl
    · apply le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  · apply sup_le
    · apply le_refl
    · apply inf_le_left
  · apply le_sup_left

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

--结论的互相证明
example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw[h, inf_comm (a ⊔ b) ,absorb1, inf_comm (a ⊔ b) , h, inf_comm c, ← sup_assoc, absorb2,inf_comm c]

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  rw[h, sup_comm (a ⊓ b),absorb2, sup_comm (a ⊓ b), h, sup_comm c, ← inf_assoc, absorb1, sup_comm c]
end

section
variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  have :  a - a  ≤ b - a:= by
    apply sub_le_sub_right h
  rw[sub_self] at this
  exact this


example (h: 0 ≤ b - a) : a ≤ b := by
  -- 对不等式 h: 0 ≤ b - a 两边同时加 a，利用加法保序性
  have h_add : 0 + a ≤ (b - a) + a := add_le_add_right h a
  -- 化简两边：0 + a = a，(b - a) + a = b（环中加法逆元性质）
  simp only [zero_add, sub_add_cancel] at h_add
  -- 此时 h_add 就是 a ≤ b，直接完成证明
  exact h_add


example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have : b - a ≥ 0 := by
    exact sub_nonneg.mpr h
  have : (b -a) * c ≥ 0 := by
    apply mul_nonneg this h'
  simp at this
  rw[sub_mul, sub_nonneg] at this
  exact this

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)


example (x y : X) : 0 ≤ dist x y := by
  have : 0 ≤ 2 * dist x y := by
    nth_rw 1[two_mul, dist_comm, ← dist_self y]
    apply dist_triangle
  linarith
end
