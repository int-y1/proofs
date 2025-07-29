
instance intSetoid : Setoid (Nat × Nat) where
  r x y := x.1 + y.2 = y.1 + x.2
  iseqv := by
    -- Exercise 4.1.1.
    refine ⟨fun x => rfl, fun h => h.symm, fun {x y z} h₁ h₂ => ?_⟩
    apply Nat.add_right_cancel (m := y.1)
    rw [Nat.add_assoc, Nat.add_comm z.2, h₂, Nat.add_comm, Nat.add_assoc, Nat.add_comm y.2, h₁,
      Nat.add_comm y.1, Nat.add_assoc]

/-- Definition 4.1.1. Integers. -/
def XInt := Quotient intSetoid

namespace XInt

variable (n m : Nat) (x y z : XInt)

def mk (a b : Nat) : XInt := Quotient.mk' (a, b)

/-- An em dash creates an integer from 2 natural numbers. -/
infix:75 " — " => mk

example : 3 — 5 = 2 — 4 := Quotient.sound rfl
example : 3 — 5 ≠ 2 — 3 := by
  intro h
  have := Quotient.exact h
  simp [HasEquiv.Equiv, Setoid.r] at this

/-- Definition 4.1.2. Sum of two integers. -/
instance : Add XInt := by
  refine ⟨fun x y ↦ Quotient.liftOn₂ x y (fun x y ↦ (x.1 + y.1) — (x.2 + y.2)) ?_⟩
  -- Lemma 4.1.3. Addition is well-defined.
  refine fun (a₁, a₂) (b₁, b₂) (c₁, c₂) (d₁, d₂) hab hcd ↦ Quotient.sound ?_
  dsimp only [HasEquiv.Equiv, Setoid.r] at hab hcd ⊢
  rw [Nat.add_assoc, Nat.add_left_comm b₁, ← Nat.add_assoc, hab, hcd,
    Nat.add_assoc, Nat.add_left_comm a₂, ← Nat.add_assoc]

/-- Definition 4.1.2. Product of two integers. -/
instance : Mul XInt := by
  refine ⟨fun x y ↦
    Quotient.liftOn₂ x y (fun x y ↦ (x.1 * y.1 + x.2 * y.2) — (x.1 * y.2 + x.2 * y.1)) ?_⟩
  -- Lemma 4.1.3. Multiplication is well-defined.
  refine fun (a₁, a₂) (b₁, b₂) (c₁, c₂) (d₁, d₂) hab hcd ↦ Quotient.sound ?_
  dsimp only [HasEquiv.Equiv] at hab hcd ⊢
  apply Setoid.iseqv.trans (y := (c₁ * b₁ + c₂ * b₂, c₁ * b₂ + c₂ * b₁)) <;>
    dsimp only [Setoid.r] at hab hcd ⊢
  · have (a b c d : Nat) : a + b + (c + d) = a + d + (c + b) := by
      rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm c b, Nat.add_left_comm d, Nat.add_comm d]
    rw [this, ← Nat.right_distrib, ← Nat.right_distrib,
      this, ← Nat.right_distrib, ← Nat.right_distrib, hab]
  · have (a b c d : Nat) : a + b + (c + d) = a + c + (b + d) := by
      rw [Nat.add_assoc, Nat.add_assoc, Nat.add_left_comm c]
    rw [this, ← Nat.left_distrib, ← Nat.left_distrib,
      this, ← Nat.left_distrib, ← Nat.left_distrib, Nat.add_comm b₂, Nat.add_comm d₂, hcd]

/-- This instance provides a way to cast a `Nat` literal to `XInt`. -/
instance : OfNat XInt n := ⟨n — 0⟩

/-- This instance provides a way to cast a `Nat` variable to `XInt`. -/
instance : Coe Nat XInt := ⟨fun n ↦ n — 0⟩

theorem coe_nat_add : (n : XInt) + (m : XInt) = ((n + m : Nat) : XInt) := Quot.sound rfl
theorem coe_nat_mul : (n : XInt) * (m : XInt) = ((n * m : Nat) : XInt) := by
  apply Quot.sound
  rw [Nat.zero_mul, Nat.zero_mul]
  rfl

/-- Definition 4.1.4. Negation of integers. -/
instance : Neg XInt := by
  refine ⟨fun x => Quotient.liftOn x (fun x ↦ x.2 — x.1) ?_⟩
  -- Exercise 4.1.2. Negation is well-defined.
  refine fun (a₁, a₂) (b₁, b₂) hab ↦ Quotient.sound ?_
  dsimp only [HasEquiv.Equiv, Setoid.r] at hab ⊢
  rw [Nat.add_comm, Nat.add_comm b₂, hab]

/-- Lemma 4.1.5, 1 or 2 or 3 -/
theorem trichotomy : x = 0 ∨ (∃ n : Nat, n > 0 ∧ x = n) ∨ (∃ n : Nat, n > 0 ∧ x = -n) := by
  revert x; apply Quotient.ind; intro ⟨a, b⟩
  cases Nat.lt_or_ge a b <;> rename_i hab
  · have : 0 < b - a := by
      apply Nat.lt_sub_of_add_lt
      rw [Nat.zero_add]
      exact hab
    refine Or.inr (Or.inr ⟨b - a, this, Quotient.sound ?_⟩)
    dsimp only [HasEquiv.Equiv, Setoid.r]
    rw [Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt hab), Nat.zero_add]
  · cases Nat.eq_or_lt_of_le hab <;> rename_i hab
    · refine Or.inl (Quotient.sound ?_)
      rw [hab]
      dsimp only [HasEquiv.Equiv, Setoid.r]
      rw [Nat.zero_add, Nat.add_zero]
    · have : 0 < a - b := by
        apply Nat.lt_sub_of_add_lt
        rw [Nat.zero_add]
        exact hab
      refine Or.inr (Or.inl ⟨a - b, this, Quotient.sound ?_⟩)
      dsimp only [HasEquiv.Equiv, Setoid.r]
      rw [Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt hab), Nat.zero_add]

/-- Lemma 4.1.5, 1 excludes 2 -/
theorem trichotomy_1n2 : x = 0 → ¬∃ n : Nat, n > 0 ∧ x = n := by
  intro h
  rw [h]
  intro ⟨n, h₁, h₂⟩
  have h₂ := Quotient.exact h₂
  dsimp only [HasEquiv.Equiv, Setoid.r] at h₂
  rw [Nat.add_zero, Nat.add_zero] at h₂
  rw [← h₂] at h₁
  exact Nat.lt_irrefl 0 h₁

-- TODO: The rest of Lemma 4.1.5. This looks really annoying.

/-- Proposition 4.1.6. Equation 1. -/
theorem add_comm : x + y = y + x := by
  revert x y; apply Quotient.ind₂; intro x y
  apply Quotient.sound
  rw [Nat.add_comm x.1, Nat.add_comm x.2]; rfl

/-- Proposition 4.1.6. Equation 2. -/
theorem add_assoc : (x + y) + z = x + (y + z) := by
  revert x y z; apply Quotient.ind₂; intro x y; apply Quotient.ind; intro z
  apply Quotient.sound
  rw [Nat.add_assoc, Nat.add_assoc]; rfl

/-- Proposition 4.1.6. Equation 3, part 1. -/
theorem add_zero : x + 0 = x := by
  revert x; apply Quotient.ind; intro x
  exact Quotient.sound rfl

/-- Proposition 4.1.6. Equation 3, part 2. -/
theorem zero_add : 0 + x = x := by
  rw [add_comm]
  exact add_zero x

/-- Proposition 4.1.6. Equation 4, part 1. -/
theorem add_neg_self : x + -x = 0 := by
  revert x; apply Quotient.ind; intro x
  apply Quotient.sound
  dsimp only [HasEquiv.Equiv, Setoid.r]
  rw [Nat.add_zero, Nat.zero_add, Nat.add_comm]

/-- Proposition 4.1.6. Equation 4, part 2. -/
theorem neg_self_add : -x + x = 0 := by
  rw [add_comm]
  exact add_neg_self x

/-- Proposition 4.1.6. Equation 5. -/
theorem mul_comm : x * y = y * x := by
  revert x y; apply Quotient.ind₂; intro x y
  apply Quotient.sound
  congr 1 <;> dsimp only
  · rw [Nat.mul_comm x.1, Nat.mul_comm x.2]
  · rw [Nat.add_comm (x.1 * y.2), Nat.mul_comm x.1, Nat.mul_comm x.2]

/-- Proposition 4.1.6. Equation 6. -/
theorem mul_assoc : (x * y) * z = x * (y * z) := by
  revert x y z; apply Quotient.ind₂; intro ⟨a, b⟩ ⟨c, d⟩; apply Quotient.ind; intro ⟨e, f⟩
  apply Quotient.sound
  congr 1 <;> simp only [Nat.left_distrib, Nat.right_distrib, ← Nat.mul_assoc, Nat.add_assoc]
  · congr 1; rw [Nat.add_left_comm]; congr 1; apply Nat.add_comm
  · congr 1; rw [Nat.add_comm (b * c * e), Nat.add_left_comm]

/-- Proposition 4.1.6. Equation 7, part 1. -/
theorem mul_one : x * 1 = x := by
  revert x; apply Quotient.ind; intro x
  apply Quotient.sound
  simp only [Nat.mul_one, Nat.mul_zero, Nat.zero_add]
  rfl

/-- Proposition 4.1.6. Equation 7, part 2. -/
theorem one_mul : 1 * x = x := by
  rw [mul_comm]
  exact mul_one x

/-- Proposition 4.1.6. Equation 8. -/
theorem left_distrib : x * (y + z) = x * y + x * z := by
  revert x y z; apply Quotient.ind₂; intro ⟨a, b⟩ ⟨c, d⟩; apply Quotient.ind; intro ⟨e, f⟩
  apply Quotient.sound
  congr 1 <;> simp only [Nat.left_distrib, Nat.add_assoc] <;> congr 1 <;> rw [Nat.add_left_comm]

/-- Proposition 4.1.6. Equation 9. -/
theorem right_distrib : (y + z) * x = y * x + z * x := by
  rw [mul_comm, mul_comm y, mul_comm z]
  exact left_distrib x y z

instance : Sub XInt := ⟨fun x y ↦ x + -y⟩

theorem mk_eq_sub : (n — m) = (n : XInt) - (m : XInt) := by
  apply Quotient.sound
  rw [Nat.zero_add]
  rfl

theorem mul_zero : x * 0 = 0 := by
  revert x; apply Quotient.ind; intro x
  exact Quotient.sound rfl

theorem zero_mul : 0 * x = 0 := by
  rw [mul_comm]
  exact mul_zero x

/-- Proposition 4.1.8. Exercise 4.1.5. -/
theorem mul_eq_zero_iff_eq_zero : x * y = 0 ↔ x = 0 ∨ y = 0 := by
  constructor
  · intro h
    match trichotomy x, trichotomy y with
    | Or.inl hx, _ => exact Or.inl hx
    | _, Or.inl hy => exact Or.inr hy
    | Or.inr (Or.inl ⟨n, hn, hx⟩), Or.inr (Or.inl ⟨m, hm, hy⟩) => ?_
    | Or.inr (Or.inl ⟨n, hn, hx⟩), Or.inr (Or.inr ⟨m, hm, hy⟩) => ?_
    | Or.inr (Or.inr ⟨n, hn, hx⟩), Or.inr (Or.inl ⟨m, hm, hy⟩) => ?_
    | Or.inr (Or.inr ⟨n, hn, hx⟩), Or.inr (Or.inr ⟨m, hm, hy⟩) => ?_
    all_goals
      rw [hx, hy] at h
      have h := Quotient.exact h
      simp [HasEquiv.Equiv, Setoid.r] at h
      exact (Nat.lt_irrefl _ (h ▸ (Nat.mul_pos hn hm))).elim
  · intro h
    cases h <;> rename_i h <;> rw [h]
    · rw [zero_mul]
    · rw [mul_zero]

/-- Corollary 4.1.9. Exercise 4.1.6. -/
theorem mul_right_cancel (h₁ : x * z = y * z) (h₂ : z ≠ 0) : x = y := by
  have : x * z + (-y) * z = y * z + (-y) * z := by rw [h₁]
  rw [← right_distrib, ← right_distrib, add_neg_self, zero_mul] at this
  cases (mul_eq_zero_iff_eq_zero _ _).1 this <;> rename_i h
  · have : x + -y + y = 0 + y := by rw [h]
    rw [add_assoc, neg_self_add, add_zero, zero_add] at this
    exact this
  · exact (h₂ h).elim

/-- Definition 4.1.10 for `≤`. -/
instance : LE XInt where
  le m n := ∃ a : Nat, n = m + a

/-- Definition 4.1.10 for `<`. -/
instance : LT XInt where
  lt m n := n ≥ m ∧ n ≠ m

example : (5 : XInt) > (-3 : XInt) := by
  refine ⟨⟨8, Quotient.sound ?_⟩, ?_⟩
  · simp only [HasEquiv.Equiv, Setoid.r]
  · intro h
    have := Quotient.exact h
    simp [HasEquiv.Equiv, Setoid.r] at this

variable (a b c : XInt)

/-- Lemma 4.1.11. Equation 1. -/
theorem gt_iff_sub_eq_pos_nat : a > b ↔ ∃ n : Nat, n > 0 ∧ n = a - b := by
  constructor
  · intro ⟨⟨n, h₁⟩, h₂⟩
    refine ⟨n, ?_, ?_⟩
    · match n with
      | 0 =>
        have : a = b + 0 := h₁
        rw [add_zero] at this
        exact (h₂ this).elim
      | n + 1 => exact Nat.zero_lt_succ n
    · dsimp only [HSub.hSub, Sub.sub]
      rw [h₁, add_comm, ← add_assoc, neg_self_add, zero_add]
  · intro ⟨n, h₁, h₂⟩
    dsimp only [HSub.hSub, Sub.sub] at h₂
    constructor
    · exists n
      rw [h₂, add_comm, add_assoc, neg_self_add, add_zero]
    · intro h
      rw [h, add_neg_self] at h₂
      have := Quotient.exact h₂
      simp only [HasEquiv.Equiv, Setoid.r, Nat.add_zero] at this
      rw [this] at h₁
      exact Nat.lt_irrefl _ h₁

/-- Lemma 4.1.11. Equation 2. -/
theorem gt_imp_gt_add_right (h : a > b) : a + c > b + c := by
  have ⟨n, h₁, h₂⟩ := (gt_iff_sub_eq_pos_nat _ _).1 h
  rw [gt_iff_sub_eq_pos_nat]
  refine ⟨n, h₁, ?_⟩
  rw [h₂]
  dsimp only [HSub.hSub, Sub.sub]
  rw [add_assoc, ← zero_add (c + _), ← neg_self_add b, add_assoc, ← add_assoc b,
    add_neg_self, add_zero]

/-- Lemma 4.1.11. Equation 3. -/
theorem gt_and_pos_imp_gt_mul (h₁ : a > b) (h₂ : c > 0) : a * c > b * c := by
  have ⟨c', hc₁, hc₂⟩ := (gt_iff_sub_eq_pos_nat _ _).1 h₂
  dsimp only [HSub.hSub, Sub.sub] at hc₂
  rw [← add_zero (-0), neg_self_add, add_zero] at hc₂
  rw [← hc₂]
  have ⟨n, hn₁, hn₂⟩ := (gt_iff_sub_eq_pos_nat _ _).1 h₁
  rw [gt_iff_sub_eq_pos_nat]
  refine ⟨n * c', Nat.mul_pos hn₁ hc₁, ?_⟩
  rw [← coe_nat_mul, hn₂, hc₂]
  dsimp only [HSub.hSub, Sub.sub]
  rw [right_distrib]
  congr
  -- goal is something simple, move the statement into the naturals
  revert b c; apply Quotient.ind₂; intro b c; intros
  apply Quotient.sound
  dsimp only
  rw [Nat.add_comm, Nat.add_comm (b.2 * _)]
  rfl

/-- Lemma 4.1.11. Equation 4. -/
theorem gt_imp_neg_lt (h : a > b) : -a < -b := by
  have := (gt_imp_gt_add_right _ _ (-a + -b)) h
  rw [← add_assoc, add_neg_self, zero_add, add_comm, add_assoc, neg_self_add, add_zero] at this
  exact this

/-- Lemma 4.1.11. Equation 5. -/
theorem gt_trans (h₁ : a > b) (h₂ : b > c) : a > c := by
  have ⟨n, hn₁, hn₂⟩ := (gt_iff_sub_eq_pos_nat _ _).1 h₁
  have ⟨m, hm₁, hm₂⟩ := (gt_iff_sub_eq_pos_nat _ _).1 h₂
  rw [gt_iff_sub_eq_pos_nat]
  refine ⟨n + m, Nat.add_lt_add hn₁ hm₁, ?_⟩
  rw [← coe_nat_add, hn₂, hm₂]
  dsimp only [HSub.hSub, Sub.sub]
  rw [add_assoc, ← add_assoc (-b), neg_self_add, zero_add]

theorem neg_neg : - -a = a := by
  rw [← add_zero (- -a), ← neg_self_add a, ← add_assoc, neg_self_add, zero_add]

/-- Lemma 4.1.11. Equation 6. 1 or 2 or 3. -/
theorem order_trichotomy_123 : a > b ∨ a < b ∨ a = b := by
  match trichotomy (a + -b) with
  | Or.inl h =>
    apply Or.inr; apply Or.inr
    rw [← zero_add b, ← h, add_assoc, neg_self_add, add_zero]
  | Or.inr (Or.inl ⟨n, h₁, h₂⟩) =>
    apply Or.inl
    rw [gt_iff_sub_eq_pos_nat]
    exact ⟨n, h₁, h₂.symm⟩
  | Or.inr (Or.inr ⟨n, h₁, h₂⟩) =>
    apply Or.inr; apply Or.inl
    suffices b > a by exact this
    rw [gt_iff_sub_eq_pos_nat]
    refine ⟨n, h₁, ?_⟩
    dsimp only [HSub.hSub, Sub.sub]
    rw [← neg_neg (n — 0), ← h₂]
    -- goal is something simple, move the statement into the naturals
    revert a b; apply Quotient.ind₂; intro a b; intros
    apply Quotient.sound
    dsimp only
    rw [Nat.add_comm, Nat.add_comm a.1]
    rfl

-- I don't feel like proving that exactly one of 1, 2, 3 holds.

/-- Exercise 4.1.3. -/
theorem neg_one_mul_eq_neg : (-1) * a = -a := by
  revert a; apply Quotient.ind; intro a
  apply Quotient.sound
  simp
  rfl

/-- Exercise 4.1.8. -/
theorem naive_ind_counterexample :
    ∃ P : XInt → Prop, P 0 ∧ (∀ n, P n → P (n + 1)) ∧ (∃ n, ¬ P n) := by
  exists (fun n ↦ n ≥ 0)
  dsimp only
  constructor
  · exists 0
  constructor
  · intro n ⟨n', h⟩
    exists n' + 1
    rw [h, zero_add, zero_add, ← coe_nat_add]
    rfl
  · exists -1
    intro ⟨n, h⟩
    have := Quotient.exact h
    simp [HasEquiv.Equiv, Setoid.r] at this

/-- Exercise 4.1.9. -/
theorem square_ge_zero : x * x ≥ 0 := by
  match order_trichotomy_123 x 0 with
  | Or.inl h =>
    have := gt_and_pos_imp_gt_mul _ _ _ h h
    rw [zero_mul] at this
    exact this.1
  | Or.inr (Or.inl h) =>
    have h' : -x > -0 := gt_imp_neg_lt _ _ h
    rw [← add_zero (-0), neg_self_add] at h'
    have := gt_and_pos_imp_gt_mul _ _ _ h' h'
    rw [zero_mul, ← neg_one_mul_eq_neg x,
      mul_assoc, mul_comm x, mul_assoc, neg_one_mul_eq_neg, neg_one_mul_eq_neg, neg_neg] at this
    exact this.1
  | Or.inr (Or.inr h) => rw [h, mul_zero]; exists 0

end XInt
