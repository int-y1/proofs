import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1439: [7/15, 242/3, 3/77, 5/11, 1617/2]

Vector representation:
```
 0 -1 -1  1  0
 1 -1  0  0  2
 0  1  0 -1 -1
 0  0  1  0 -1
-1  1  0  2  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1439

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e+1⟩
  | _ => none

-- R3+R2 chain: alternating R3 and R2 when b=c=0, d≥1, e≥1.
theorem r3r2_chain : ∀ k a e, (⟨a, 0, 0, k, e + 1⟩ : Q) [fm]⊢* ⟨a + k, 0, 0, 0, e + k + 1⟩ := by
  intro k; induction k with
  | zero => intro a e; ring_nf; finish
  | succ k ih =>
    intro a e
    step fm; step fm
    apply stepStar_trans (ih (a + 1) (e + 1))
    ring_nf; finish

-- R4 chain: e → c.
theorem e_to_c : ∀ k a c, (⟨a, 0, c, 0, k⟩ : Q) [fm]⊢* ⟨a, 0, c + k, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a c; ring_nf; finish
  | succ k ih =>
    intro a c
    step fm
    apply stepStar_trans (ih a (c + 1))
    ring_nf; finish

-- R5+R1+R3+R1 chain (even c).
theorem r5r1r3r1_even : ∀ k a d, (⟨a + k, 0, 2 * k, d, 0⟩ : Q) [fm]⊢* ⟨a, 0, 0, d + 3 * k, 0⟩ := by
  intro k; induction k with
  | zero => intro a d; ring_nf; finish
  | succ k ih =>
    intro a d
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
        show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih a (d + 3))
    ring_nf; finish

-- R5+R1+R3+R1 chain (odd c).
theorem r5r1r3r1_odd : ∀ k a d, (⟨a + k, 0, 2 * k + 1, d, 0⟩ : Q) [fm]⊢* ⟨a, 0, 1, d + 3 * k, 0⟩ := by
  intro k; induction k with
  | zero => intro a d; ring_nf; finish
  | succ k ih =>
    intro a d
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring,
        show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih a (d + 3))
    ring_nf; finish

-- Type 0: (a+1, 0, 0, d, 0) ⊢⁺ next
-- Opening: R5 then R2 giving (a+1, 0, 0, d+2, 3)
-- This step is the same for all d.
theorem opening_type0 (a d : ℕ) :
    (⟨a + 1, 0, 0, d, 0⟩ : Q) [fm]⊢⁺ ⟨a + 1, 0, 0, d + 2, 3⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨a + 1, 0, 0, d, 0⟩ = some ⟨a, 1, 0, d + 2, 1⟩
    simp [fm]
  step fm
  ring_nf; finish

-- Type 1 opening: (a+1, 0, 1, d+1, 0) ⊢⁺ (a+1, 0, 0, d+3, 2)
-- R5: (a, 1, 1, d+3, 1) -> R1: (a, 0, 0, d+4, 1) -> R3: (a, 1, 0, d+3, 0) -> R2: (a+1, 0, 0, d+3, 2)
theorem opening_type1 (a d : ℕ) :
    (⟨a + 1, 0, 1, d + 1, 0⟩ : Q) [fm]⊢⁺ ⟨a + 1, 0, 0, d + 3, 2⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨a + 1, 0, 1, d + 1, 0⟩ = some ⟨a, 1, 1, d + 3, 1⟩
    simp [fm]
  step fm; step fm; step fm
  ring_nf; finish

-- Now combine: type 0, d even
theorem trans_0e (a k : ℕ) :
    (⟨a + 1, 0, 0, 2 * k, 0⟩ : Q) [fm]⊢⁺ ⟨a + k + 1, 0, 1, 3 * k + 6, 0⟩ := by
  apply stepPlus_stepStar_stepPlus (opening_type0 a (2 * k))
  rw [show (3 : ℕ) = 2 + 1 from rfl]
  apply stepStar_trans (r3r2_chain (2 * k + 2) (a + 1) 2)
  rw [show a + 1 + (2 * k + 2) = a + 2 * k + 3 from by ring,
      show 2 + (2 * k + 2) + 1 = 2 * k + 5 from by ring]
  apply stepStar_trans (e_to_c (2 * k + 5) (a + 2 * k + 3) 0)
  rw [show 0 + (2 * k + 5) = 2 * (k + 2) + 1 from by ring,
      show a + 2 * k + 3 = (a + k + 1) + (k + 2) from by ring]
  apply stepStar_trans (r5r1r3r1_odd (k + 2) (a + k + 1) 0)
  ring_nf; finish

-- Type 0, d odd
theorem trans_0o (a k : ℕ) :
    (⟨a + 1, 0, 0, 2 * k + 1, 0⟩ : Q) [fm]⊢⁺ ⟨a + k + 1, 0, 0, 3 * k + 9, 0⟩ := by
  apply stepPlus_stepStar_stepPlus (opening_type0 a (2 * k + 1))
  rw [show (3 : ℕ) = 2 + 1 from rfl]
  apply stepStar_trans (r3r2_chain (2 * k + 3) (a + 1) 2)
  rw [show a + 1 + (2 * k + 3) = a + 2 * k + 4 from by ring,
      show 2 + (2 * k + 3) + 1 = 2 * k + 6 from by ring]
  apply stepStar_trans (e_to_c (2 * k + 6) (a + 2 * k + 4) 0)
  rw [show 0 + (2 * k + 6) = 2 * (k + 3) from by ring,
      show a + 2 * k + 4 = (a + k + 1) + (k + 3) from by ring]
  apply stepStar_trans (r5r1r3r1_even (k + 3) (a + k + 1) 0)
  ring_nf; finish

-- Type 1, d+1 odd (d even, d=2k): (a+1, 0, 1, 2k+1, 0) ⊢⁺ (a+k+2, 0, 1, 3k+6, 0)
theorem trans_1e (a k : ℕ) :
    (⟨a + 1, 0, 1, 2 * k + 1, 0⟩ : Q) [fm]⊢⁺ ⟨a + k + 2, 0, 1, 3 * k + 6, 0⟩ := by
  rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (opening_type1 a (2 * k))
  rw [show (2 : ℕ) = 1 + 1 from rfl,
      show 2 * k + 3 = 2 * k + 3 from rfl]
  apply stepStar_trans (r3r2_chain (2 * k + 3) (a + 1) 1)
  rw [show a + 1 + (2 * k + 3) = a + 2 * k + 4 from by ring,
      show 1 + (2 * k + 3) + 1 = 2 * k + 5 from by ring]
  apply stepStar_trans (e_to_c (2 * k + 5) (a + 2 * k + 4) 0)
  rw [show 0 + (2 * k + 5) = 2 * (k + 2) + 1 from by ring,
      show a + 2 * k + 4 = (a + k + 2) + (k + 2) from by ring]
  apply stepStar_trans (r5r1r3r1_odd (k + 2) (a + k + 2) 0)
  ring_nf; finish

-- Type 1, d+1 even (d odd, d=2k+1): (a+1, 0, 1, 2k+2, 0) ⊢⁺ (a+k+2, 0, 0, 3k+9, 0)
theorem trans_1o (a k : ℕ) :
    (⟨a + 1, 0, 1, 2 * k + 2, 0⟩ : Q) [fm]⊢⁺ ⟨a + k + 2, 0, 0, 3 * k + 9, 0⟩ := by
  rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (opening_type1 a (2 * k + 1))
  rw [show (2 : ℕ) = 1 + 1 from rfl,
      show 2 * k + 1 + 3 = 2 * k + 4 from by ring]
  apply stepStar_trans (r3r2_chain (2 * k + 4) (a + 1) 1)
  rw [show a + 1 + (2 * k + 4) = a + 2 * k + 5 from by ring,
      show 1 + (2 * k + 4) + 1 = 2 * k + 6 from by ring]
  apply stepStar_trans (e_to_c (2 * k + 6) (a + 2 * k + 5) 0)
  rw [show 0 + (2 * k + 6) = 2 * (k + 3) from by ring,
      show a + 2 * k + 5 = (a + k + 2) + (k + 3) from by ring]
  apply stepStar_trans (r5r1r3r1_even (k + 3) (a + k + 2) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ (∃ a d, q = ⟨a + 1, 0, 0, d, 0⟩) ∨ (∃ a d, q = ⟨a + 1, 0, 1, d + 1, 0⟩))
  · intro q hq
    rcases hq with ⟨a, d, rfl⟩ | ⟨a, d, rfl⟩
    · rcases Nat.even_or_odd d with ⟨k, hk⟩ | ⟨k, hk⟩
      · subst hk; rw [show k + k = 2 * k from by ring]
        exact ⟨_, Or.inr ⟨a + k, 3 * k + 5, by ring_nf⟩, trans_0e a k⟩
      · subst hk
        exact ⟨_, Or.inl ⟨a + k, 3 * k + 9, by ring_nf⟩, trans_0o a k⟩
    · rcases Nat.even_or_odd d with ⟨k, hk⟩ | ⟨k, hk⟩
      · subst hk; rw [show k + k + 1 = 2 * k + 1 from by ring]
        exact ⟨_, Or.inr ⟨a + k + 1, 3 * k + 5, by ring_nf⟩, trans_1e a k⟩
      · subst hk; rw [show 2 * k + 1 + 1 = 2 * k + 2 from by ring]
        exact ⟨_, Or.inl ⟨a + k + 1, 3 * k + 9, by ring_nf⟩, trans_1o a k⟩
  · exact Or.inl ⟨0, 0, rfl⟩

end Sz22_2003_unofficial_1439
