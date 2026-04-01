import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1571: [7/45, 25/77, 242/5, 3/11, 55/2]

Vector representation:
```
 0 -2 -1  1  0
 0  0  2 -1 -1
 1  0 -1  0  2
 0  1  0  0 -1
-1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1571

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

-- R4 chain: transfer e to b (c=0, d=0)
theorem e_to_b : ∀ k, ∀ a b, ⟨a, b, 0, 0, e + k⟩ [fm]⊢* ⟨a, b + k, 0, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro a b; exists 0
  · intro a b; rw [Nat.add_succ]; step fm
    apply stepStar_trans (ih a (b + 1)); ring_nf; finish

-- R3 chain with b=0
theorem r3_chain_b0 : ∀ k, ∀ a c e, ⟨a, 0, c + k, 0, e⟩ [fm]⊢* ⟨a + k, 0, c, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih
  · intro a c e; exists 0
  · intro a c e
    rw [show c + (k + 1) = (c + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (a + 1) c (e + 2)); ring_nf; finish

-- R3 chain with b=1
theorem r3_chain_b1 : ∀ k, ∀ a c e, ⟨a, 1, c + k, 0, e⟩ [fm]⊢* ⟨a + k, 1, c, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih
  · intro a c e; exists 0
  · intro a c e
    rw [show c + (k + 1) = (c + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (a + 1) c (e + 2)); ring_nf; finish

-- Drain loop: 5 steps per round (R5,R1,R2,R1,R1)
theorem drain_loop : ∀ k, ∀ a d, ⟨a + k, b + 6 * k, 0, d, 0⟩ [fm]⊢* ⟨a, b, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih
  · intro a d; simp; exists 0
  · intro a d
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + 6 * (k + 1) = (b + 6 * k) + 6 from by ring]
    apply stepStar_trans
      (step_stepStar (show ⟨(a + k) + 1, (b + 6 * k) + 6, 0, d, 0⟩ [fm]⊢
        ⟨a + k, (b + 6 * k) + 6, 1, d, 1⟩ from by simp [fm]))
    rw [show (b + 6 * k) + 6 = ((b + 6 * k) + 4) + 2 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    apply stepStar_trans
      (step_stepStar (show ⟨a + k, (b + 6 * k) + 4, 0, d + 1, 1⟩ [fm]⊢
        ⟨a + k, (b + 6 * k) + 4, 2, d, 0⟩ from by simp [fm]))
    rw [show (b + 6 * k) + 4 = ((b + 6 * k) + 2) + 2 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    step fm
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 2)); ring_nf; finish

-- R2,R2,R3 loop (b=1): (a, 1, c, 2k, 2) ⊢* (a+k, 1, c+3k, 0, 2)
theorem r2r2r3_loop : ∀ k, ∀ a c, ⟨a, 1, c, 2 * k, 2⟩ [fm]⊢* ⟨a + k, 1, c + 3 * k, 0, 2⟩ := by
  intro k; induction' k with k ih
  · intro a c; simp; exists 0
  · intro a c
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    apply stepStar_trans
      (step_stepStar (show ⟨a, 1, c, 2 * k + 2, 2⟩ [fm]⊢ ⟨a, 1, c + 2, 2 * k + 1, 1⟩ from by simp [fm]))
    apply stepStar_trans
      (step_stepStar (show ⟨a, 1, c + 2, 2 * k + 1, 1⟩ [fm]⊢ ⟨a, 1, c + 4, 2 * k, 0⟩ from by simp [fm]))
    apply stepStar_trans
      (step_stepStar (show ⟨a, 1, c + 4, 2 * k, 0⟩ [fm]⊢ ⟨a + 1, 1, c + 3, 2 * k, 2⟩ from by simp [fm]))
    apply stepStar_trans (ih (a + 1) (c + 3)); ring_nf; finish

-- R2,R3,R2 loop (b=1): (a, 1, c, 2k, 1) ⊢* (a+k, 1, c+3k, 0, 1)
theorem r2r3r2_loop_b1 : ∀ k, ∀ a c, ⟨a, 1, c, 2 * k, 1⟩ [fm]⊢* ⟨a + k, 1, c + 3 * k, 0, 1⟩ := by
  intro k; induction' k with k ih
  · intro a c; simp; exists 0
  · intro a c
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    apply stepStar_trans
      (step_stepStar (show ⟨a, 1, c, 2 * k + 2, 1⟩ [fm]⊢ ⟨a, 1, c + 2, 2 * k + 1, 0⟩ from by simp [fm]))
    apply stepStar_trans
      (step_stepStar (show ⟨a, 1, c + 2, 2 * k + 1, 0⟩ [fm]⊢ ⟨a + 1, 1, c + 1, 2 * k + 1, 2⟩ from by simp [fm]))
    apply stepStar_trans
      (step_stepStar (show ⟨a + 1, 1, c + 1, 2 * k + 1, 2⟩ [fm]⊢ ⟨a + 1, 1, c + 3, 2 * k, 1⟩ from by simp [fm]))
    apply stepStar_trans (ih (a + 1) (c + 3)); ring_nf; finish

-- R2,R3,R2 loop (b=0): (a, 0, c, 2k, 1) ⊢* (a+k, 0, c+3k, 0, 1)
theorem r2r3r2_loop_b0 : ∀ k, ∀ a c, ⟨a, 0, c, 2 * k, 1⟩ [fm]⊢* ⟨a + k, 0, c + 3 * k, 0, 1⟩ := by
  intro k; induction' k with k ih
  · intro a c; simp; exists 0
  · intro a c
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    apply stepStar_trans
      (step_stepStar (show ⟨a, 0, c, 2 * k + 2, 1⟩ [fm]⊢ ⟨a, 0, c + 2, 2 * k + 1, 0⟩ from by simp [fm]))
    apply stepStar_trans
      (step_stepStar (show ⟨a, 0, c + 2, 2 * k + 1, 0⟩ [fm]⊢ ⟨a + 1, 0, c + 1, 2 * k + 1, 2⟩ from by simp [fm]))
    apply stepStar_trans
      (step_stepStar (show ⟨a + 1, 0, c + 1, 2 * k + 1, 2⟩ [fm]⊢ ⟨a + 1, 0, c + 3, 2 * k, 1⟩ from by simp [fm]))
    apply stepStar_trans (ih (a + 1) (c + 3)); ring_nf; finish

-- T1: (a+k+1, 6k+3, 0, 0, 0) ⊢⁺ (a+4k+2, 6k+5, 0, 0, 0)
theorem trans1 (a k : ℕ) :
    ⟨a + k + 1, 6 * k + 3, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + 4 * k + 2, 6 * k + 5, 0, 0, 0⟩ := by
  rw [show 6 * k + 3 = 3 + 6 * k from by ring, show a + k + 1 = (a + 1) + k from by ring]
  apply stepStar_stepPlus_stepPlus (drain_loop k (a + 1) 0 (b := 3))
  rw [show 0 + 2 * k = 2 * k from by ring]
  apply step_stepStar_stepPlus
    (show ⟨a + 1, 3, 0, 2 * k, 0⟩ [fm]⊢ ⟨a, 3, 1, 2 * k, 1⟩ from by simp [fm])
  rw [show (3 : ℕ) = 1 + 2 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  apply stepStar_trans
    (step_stepStar (show ⟨a, 1, 0, 2 * k + 1, 1⟩ [fm]⊢ ⟨a, 1, 2, 2 * k, 0⟩ from by simp [fm]))
  apply stepStar_trans
    (step_stepStar (show ⟨a, 1, 2, 2 * k, 0⟩ [fm]⊢ ⟨a + 1, 1, 1, 2 * k, 2⟩ from by simp [fm]))
  apply stepStar_trans (r2r2r3_loop k (a + 1) 1)
  rw [show a + 1 + k = a + k + 1 from by ring, show 1 + 3 * k = 3 * k + 1 from by ring]
  rw [show 3 * k + 1 = 0 + (3 * k + 1) from by ring]
  apply stepStar_trans (r3_chain_b1 (3 * k + 1) (a + k + 1) 0 2)
  rw [show a + k + 1 + (3 * k + 1) = a + 4 * k + 2 from by ring,
      show 2 + 2 * (3 * k + 1) = 0 + (6 * k + 4) from by ring]
  apply stepStar_trans (e_to_b (6 * k + 4) (a + 4 * k + 2) 1 (e := 0))
  rw [show 1 + (6 * k + 4) = 6 * k + 5 from by ring]; finish

-- T2: (a+k+1, 6k+5, 0, 0, 0) ⊢⁺ (a+4k+3, 6k+6, 0, 0, 0)
theorem trans2 (a k : ℕ) :
    ⟨a + k + 1, 6 * k + 5, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + 4 * k + 3, 6 * k + 6, 0, 0, 0⟩ := by
  rw [show 6 * k + 5 = 5 + 6 * k from by ring, show a + k + 1 = (a + 1) + k from by ring]
  apply stepStar_stepPlus_stepPlus (drain_loop k (a + 1) 0 (b := 5))
  rw [show 0 + 2 * k = 2 * k from by ring]
  apply step_stepStar_stepPlus
    (show ⟨a + 1, 5, 0, 2 * k, 0⟩ [fm]⊢ ⟨a, 5, 1, 2 * k, 1⟩ from by simp [fm])
  rw [show (5 : ℕ) = 3 + 2 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  apply stepStar_trans
    (step_stepStar (show ⟨a, 3, 0, 2 * k + 1, 1⟩ [fm]⊢ ⟨a, 3, 2, 2 * k, 0⟩ from by simp [fm]))
  rw [show (3 : ℕ) = 1 + 2 from by ring, show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  apply stepStar_trans
    (step_stepStar (show ⟨a, 1, 1, 2 * k + 1, 0⟩ [fm]⊢ ⟨a + 1, 1, 0, 2 * k + 1, 2⟩ from by simp [fm]))
  apply stepStar_trans
    (step_stepStar (show ⟨a + 1, 1, 0, 2 * k + 1, 2⟩ [fm]⊢ ⟨a + 1, 1, 2, 2 * k, 1⟩ from by simp [fm]))
  apply stepStar_trans (r2r3r2_loop_b1 k (a + 1) 2)
  rw [show a + 1 + k = a + k + 1 from by ring, show 2 + 3 * k = 3 * k + 2 from by ring]
  rw [show 3 * k + 2 = 0 + (3 * k + 2) from by ring]
  apply stepStar_trans (r3_chain_b1 (3 * k + 2) (a + k + 1) 0 1)
  rw [show a + k + 1 + (3 * k + 2) = a + 4 * k + 3 from by ring,
      show 1 + 2 * (3 * k + 2) = 0 + (6 * k + 5) from by ring]
  apply stepStar_trans (e_to_b (6 * k + 5) (a + 4 * k + 3) 1 (e := 0))
  rw [show 1 + (6 * k + 5) = 6 * k + 6 from by ring]; finish

-- T3: (a+k+2, 6k+6, 0, 0, 0) ⊢⁺ (a+4k+5, 6k+9, 0, 0, 0)
theorem trans3 (a k : ℕ) :
    ⟨a + k + 2, 6 * k + 6, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + 4 * k + 5, 6 * k + 9, 0, 0, 0⟩ := by
  rw [show 6 * k + 6 = 6 + 6 * k from by ring, show a + k + 2 = (a + 2) + k from by ring]
  apply stepStar_stepPlus_stepPlus (drain_loop k (a + 2) 0 (b := 6))
  rw [show 0 + 2 * k = 2 * k from by ring]
  apply step_stepStar_stepPlus
    (show ⟨a + 2, 6, 0, 2 * k, 0⟩ [fm]⊢ ⟨a + 1, 6, 1, 2 * k, 1⟩ from by simp [fm])
  rw [show (6 : ℕ) = 4 + 2 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  apply stepStar_trans
    (step_stepStar (show ⟨a + 1, 4, 0, 2 * k + 1, 1⟩ [fm]⊢ ⟨a + 1, 4, 2, 2 * k, 0⟩ from by simp [fm]))
  rw [show (4 : ℕ) = 2 + 2 from by ring, show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  rw [show (2 : ℕ) = 0 + 2 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  apply stepStar_trans
    (step_stepStar (show ⟨a + 1, 0, 0, 2 * k + 2, 0⟩ [fm]⊢ ⟨a, 0, 1, 2 * k + 2, 1⟩ from by simp [fm]))
  apply stepStar_trans
    (step_stepStar (show ⟨a, 0, 1, 2 * k + 2, 1⟩ [fm]⊢ ⟨a, 0, 3, 2 * k + 1, 0⟩ from by simp [fm]))
  apply stepStar_trans
    (step_stepStar (show ⟨a, 0, 3, 2 * k + 1, 0⟩ [fm]⊢ ⟨a + 1, 0, 2, 2 * k + 1, 2⟩ from by simp [fm]))
  apply stepStar_trans
    (step_stepStar (show ⟨a + 1, 0, 2, 2 * k + 1, 2⟩ [fm]⊢ ⟨a + 1, 0, 4, 2 * k, 1⟩ from by simp [fm]))
  apply stepStar_trans (r2r3r2_loop_b0 k (a + 1) 4)
  rw [show a + 1 + k = a + k + 1 from by ring, show 4 + 3 * k = 3 * k + 4 from by ring]
  rw [show 3 * k + 4 = 0 + (3 * k + 4) from by ring]
  apply stepStar_trans (r3_chain_b0 (3 * k + 4) (a + k + 1) 0 1)
  rw [show a + k + 1 + (3 * k + 4) = a + 4 * k + 5 from by ring,
      show 1 + 2 * (3 * k + 4) = 0 + (6 * k + 9) from by ring]
  apply stepStar_trans (e_to_b (6 * k + 9) (a + 4 * k + 5) 0 (e := 0))
  rw [show 0 + (6 * k + 9) = 6 * k + 9 from by ring]; finish

-- 3-step macro
theorem macro_trans (F k : ℕ) :
    ⟨F + k + 1, 6 * k + 3, 0, 0, 0⟩ [fm]⊢⁺ ⟨F + 10 * k + 7, 6 * k + 9, 0, 0, 0⟩ := by
  apply stepPlus_trans (trans1 F k)
  rw [show F + 4 * k + 2 = (F + 3 * k + 1) + k + 1 from by ring]
  apply stepPlus_trans (trans2 (F + 3 * k + 1) k)
  rw [show F + 3 * k + 1 + 4 * k + 3 = (F + 6 * k + 2) + k + 2 from by ring]
  apply stepPlus_stepStar_stepPlus (trans3 (F + 6 * k + 2) k)
  rw [show F + 6 * k + 2 + 4 * k + 5 = F + 10 * k + 7 from by ring]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 3, 0, 0, 0⟩) (by execute fm 5)
  rw [show (1 : ℕ) = 0 + 0 + 1 from by ring, show (3 : ℕ) = 6 * 0 + 3 from by ring]
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨F, k⟩ ↦ ⟨F + k + 1, 6 * k + 3, 0, 0, 0⟩) ⟨0, 0⟩
  intro ⟨F, k⟩; simp only
  exact ⟨⟨F + 9 * k + 5, k + 1⟩, by
    show ⟨F + k + 1, 6 * k + 3, 0, 0, 0⟩ [fm]⊢⁺ ⟨F + 9 * k + 5 + (k + 1) + 1, 6 * (k + 1) + 3, 0, 0, 0⟩
    rw [show F + 9 * k + 5 + (k + 1) + 1 = F + 10 * k + 7 from by ring,
        show 6 * (k + 1) + 3 = 6 * k + 9 from by ring]
    exact macro_trans F k⟩

end Sz22_2003_unofficial_1571
