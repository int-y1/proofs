import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #441: [27/35, 5/66, 14/3, 11/7, 9/2]

Vector representation:
```
 0  3 -1 -1  0
-1 -1  1  0 -1
 1 -1  0  1  0
 0  0  0 -1  1
-1  2  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_441

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a+1, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

-- Rule 3 chain: (a, b+k, 0, d, 0) ->* (a+k, b, 0, d+k, 0)
theorem rule3_chain : ∀ k a b d, ⟨a, b+k, 0, d, 0⟩ [fm]⊢* ⟨a+k, b, 0, d+k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih (a + 1) b (d + 1))
  rw [show a + 1 + k = a + (k + 1) from by ring,
      show d + 1 + k = d + (k + 1) from by ring]; finish

-- Rule 4 chain: (a, 0, 0, d+k, e) ->* (a, 0, 0, d, e+k)
theorem d_to_e : ∀ k a d e, ⟨a, 0, 0, d+k, e⟩ [fm]⊢* ⟨a, 0, 0, d, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih a d (e + 1))
  rw [show e + 1 + k = e + (k + 1) from by ring]; finish

-- Phase 3: repeated (rule5, rule2, rule2) triplets
-- (a+3*k, 0, c, 0, e+2*k) ->* (a, 0, c+2*k, 0, e)
theorem phase3 : ∀ k a c e, ⟨a+3*k, 0, c, 0, e+2*k⟩ [fm]⊢* ⟨a, 0, c+2*k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  rw [show a + 3 * (k + 1) = (a + 3 * k) + 3 from by ring,
      show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih a (c + 2) e)
  rw [show c + 2 + 2 * k = c + 2 * (k + 1) from by ring]; finish

-- Tail: (2, 0, c, 0, 2) ->* (1, 4, c, 0, 0)
theorem tail8 : ∀ c, ⟨2, 0, c, 0, 2⟩ [fm]⊢* ⟨1, 4, c, 0, 0⟩ := by
  intro c
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; finish

-- Phase 4: repeated (rule3, rule1) pairs
-- (k, b+1, c+1+j, 0, 0) ->* (k+j+1, b+2*j+3, c, 0, 0)
theorem phase4 : ∀ j k b c, ⟨k, b+1, c+1+j, 0, 0⟩ [fm]⊢* ⟨k+j+1, b+2*j+3, c, 0, 0⟩ := by
  intro j; induction' j with j ih <;> intro k b c
  · step fm; step fm; finish
  rw [show c + 1 + (j + 1) = (c + 1 + j) + 1 from by ring]
  step fm
  rw [show c + 1 + j + 1 = (c + 1 + j) + 1 from by ring]
  step fm
  rw [show b + 3 = (b + 2) + 1 from by ring]
  apply stepStar_trans (ih (k + 1) (b + 2) c)
  rw [show k + 1 + j + 1 = k + (j + 1) + 1 from by ring,
      show b + 2 + 2 * j + 3 = b + 2 * (j + 1) + 3 from by ring]; finish

-- Main transition: (a+1, 2*a+4, 0, 0, 0) ->+ (2*a+3, 4*a+8, 0, 0, 0)
theorem main_trans (a : ℕ) :
    ⟨a+1, 2*a+4, 0, 0, 0⟩ [fm]⊢⁺ ⟨2*a+3, 4*a+8, 0, 0, 0⟩ := by
  -- Phase 1: rule3_chain (2*a+4) times
  have p1 : ⟨a+1, 2*a+4, 0, 0, 0⟩ [fm]⊢* ⟨3*a+5, 0, 0, 2*a+4, 0⟩ := by
    have h := rule3_chain (2*a+4) (a+1) 0 0
    simp only [Nat.zero_add] at h
    rw [show a + 1 + (2 * a + 4) = 3 * a + 5 from by ring] at h; exact h
  -- Phase 2: d_to_e (2*a+4) times
  have p2 : ⟨3*a+5, 0, 0, 2*a+4, 0⟩ [fm]⊢* ⟨3*a+5, 0, 0, 0, 2*a+4⟩ := by
    have h := d_to_e (2*a+4) (3*a+5) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: phase3 (a+1) times
  have p3 : ⟨3*a+5, 0, 0, 0, 2*a+4⟩ [fm]⊢* ⟨2, 0, 2*a+2, 0, 2⟩ := by
    have h := phase3 (a+1) 2 0 2
    rw [show 2 + 3 * (a + 1) = 3 * a + 5 from by ring,
        show 2 + 2 * (a + 1) = 2 * a + 4 from by ring,
        show 0 + 2 * (a + 1) = 2 * a + 2 from by ring] at h; exact h
  -- Tail
  have p4 : ⟨2, 0, 2*a+2, 0, 2⟩ [fm]⊢* ⟨1, 4, 2*a+2, 0, 0⟩ := tail8 (2*a+2)
  -- Phase 4: (1, 4, 2*a+2, 0, 0) = (1, 3+1, 0+1+(2*a+1), 0, 0)
  have p5 : ⟨1, 4, 2*a+2, 0, 0⟩ [fm]⊢* ⟨2*a+3, 4*a+8, 0, 0, 0⟩ := by
    rw [show (4 : ℕ) = 3 + 1 from by ring,
        show 2 * a + 2 = 0 + 1 + (2 * a + 1) from by ring]
    have h := phase4 (2*a+1) 1 3 0
    rw [show 1 + (2 * a + 1) + 1 = 2 * a + 3 from by ring,
        show 3 + 2 * (2 * a + 1) + 3 = 4 * a + 8 from by ring] at h; exact h
  -- Chain everything together
  exact stepStar_stepPlus_stepPlus p1
    (stepStar_stepPlus_stepPlus p2
      (stepStar_stepPlus_stepPlus p3
        (stepStar_stepPlus_stepPlus p4
          (stepStar_stepPlus p5 (by
            intro heq
            have := congr_arg (fun q : Q => q.1) heq
            simp at this)))))

def seq : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 * seq n + 1

theorem seq_pos : ∀ n, seq n ≥ 1 := by
  intro n; induction n with
  | zero => decide
  | succ n ih => unfold seq; omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 4, 0, 0, 0⟩) (by execute fm 12)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨seq n, 2 * seq n + 2, 0, 0, 0⟩) 0
  intro n
  exists n + 1
  show ⟨seq n, 2 * seq n + 2, 0, 0, 0⟩ [fm]⊢⁺
    ⟨seq (n + 1), 2 * seq (n + 1) + 2, 0, 0, 0⟩
  simp only [seq]
  -- Goal: (seq n, 2*seq n+2, 0,0,0) ⊢⁺ (2*seq n+1, 2*(2*seq n+1)+2, 0,0,0)
  -- = (seq n, 2*seq n+2, 0,0,0) ⊢⁺ (2*seq n+1, 4*seq n+4, 0,0,0)
  rw [show 2 * (2 * seq n + 1) + 2 = 4 * seq n + 4 from by ring]
  have hs := seq_pos n
  have h := main_trans (seq n - 1)
  rw [show seq n - 1 + 1 = seq n from by omega,
      show 2 * (seq n - 1) + 4 = 2 * seq n + 2 from by omega,
      show 2 * (seq n - 1) + 3 = 2 * seq n + 1 from by omega,
      show 4 * (seq n - 1) + 8 = 4 * seq n + 4 from by omega] at h
  exact h

end Sz22_2003_unofficial_441
