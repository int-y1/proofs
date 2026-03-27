import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #479: [28/15, 3/22, 1225/2, 11/7, 2/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -1
-1  0  2  2  0
 0  0  0 -1  1
 1  0 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6 (1M context)
-/

namespace Sz22_2003_unofficial_479

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

-- R4 repeated: transfer k from d to e
theorem d_to_e : ∀ k e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c, d, e + k⟩ := by
  intro k; induction k with
  | zero => intro e; exists 0
  | succ k ih =>
    intro e; rw [← Nat.add_assoc]; step fm
    apply stepStar_trans (ih _); ring_nf; finish

-- (R2, R1) pair repeated n times
theorem r2r1_chain : ∀ n a d e, ⟨a + 1, 0, c + n, d, e + n⟩ [fm]⊢* ⟨a + n + 1, 0, c, d + n, e⟩ := by
  intro n; induction n with
  | zero => intro a d e; exists 0
  | succ n ih =>
    intro a d e
    rw [show c + (n + 1) = (c + n) + 1 from by ring,
        show e + (n + 1) = (e + n) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih _ _ _); ring_nf; finish

-- R2 repeated: transfer k from (a,e) to b
theorem e_to_b : ∀ k b, ⟨a + k, b, 0, d, k⟩ [fm]⊢* ⟨a, b + k, 0, d, 0⟩ := by
  intro k; induction k with
  | zero => intro b; exists 0
  | succ k ih =>
    intro b; rw [← Nat.add_assoc]; step fm
    apply stepStar_trans (ih _); ring_nf; finish

-- R3 drain: a steps of R3
theorem r3_drain : ∀ a c d, ⟨a, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, c + 2 * a, d + 2 * a, 0⟩ := by
  intro a; induction a with
  | zero => intro c d; exists 0
  | succ a ih =>
    intro c d; step fm
    apply stepStar_trans (ih _ _); ring_nf; finish

-- Cascade: from (a+1, b, 0, d, 0) to (0, 0, 2a+3b+2, d+2a+5b+2, 0)
theorem cascade : ∀ b a d, ⟨a + 1, b, 0, d, 0⟩ [fm]⊢* ⟨0, 0, 2 * a + 3 * b + 2, d + 2 * a + 5 * b + 2, 0⟩ := by
  intro b; induction b using Nat.strongRecOn with
  | ind b ih =>
    intro a d
    match b with
    | 0 =>
      apply stepStar_trans (r3_drain (a + 1) 0 d); ring_nf; finish
    | 1 =>
      step fm; step fm
      apply stepStar_trans (r3_drain (a + 2) 1 (d + 3)); ring_nf; finish
    | b + 2 =>
      step fm; step fm; step fm
      apply stepStar_trans (ih b (by omega) (a + 3) (d + 4)); ring_nf; finish

-- Phases 1-5 composed as ⊢*: from one step after start to the target
theorem phases_star (c : ℕ) :
    ⟨0, 0, c + 2, 2 * c + 1, 1⟩ [fm]⊢* ⟨0, 0, 3 * c + 5, 6 * c + 8, 0⟩ := by
  -- Continue d_to_e: (0,0,c+2,2c+1,1) ⊢* (0,0,c+2,0,2c+2)
  rw [show (2 * c + 1 : ℕ) = 0 + (2 * c + 1) from by ring]
  apply stepStar_trans (d_to_e (2 * c + 1) 1)
  rw [show (1 + (2 * c + 1) : ℕ) = 2 * c + 2 from by ring]
  -- R5: (0,0,c+2,0,2c+2) -> (1,0,c+1,0,2c+2)
  step fm
  -- r2r1_chain with n = c+1
  rw [show c + 1 = 0 + (c + 1) from by ring,
      show 2 * c + 2 = (c + 1) + (c + 1) from by ring]
  apply stepStar_trans (r2r1_chain (c + 1) 0 0 (c + 1))
  rw [show 0 + (c + 1) + 1 = 1 + (c + 1) from by ring,
      show 0 + (c + 1) = c + 1 from by ring]
  -- e_to_b: (c+2,0,0,c+1,c+1) ⊢* (1,c+1,0,c+1,0)
  apply stepStar_trans (e_to_b (c + 1) 0)
  rw [show 0 + (c + 1) = c + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  -- cascade
  apply stepStar_trans (cascade (c + 1) 0 (c + 1))
  ring_nf; finish

-- Main transition
theorem full_transition (c : ℕ) :
    ⟨0, 0, c + 2, 2 * c + 2, 0⟩ [fm]⊢⁺ ⟨0, 0, 3 * c + 5, 6 * c + 8, 0⟩ := by
  rw [show (2 * c + 2 : ℕ) = (2 * c + 1) + 1 from by ring]
  step fm
  exact phases_star c

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 2, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun c ↦ ⟨0, 0, c + 2, 2 * c + 2, 0⟩) 0
  intro c; exact ⟨3 * c + 3, by
    rw [show 3 * c + 3 + 2 = 3 * c + 5 from by ring,
        show 2 * (3 * c + 3) + 2 = 6 * c + 8 from by ring]
    exact full_transition c⟩

end Sz22_2003_unofficial_479
