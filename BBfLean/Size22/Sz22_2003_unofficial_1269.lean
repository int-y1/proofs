import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1269: [5/6, 99/35, 4/5, 7/11, 55/2]

Vector representation:
```
-1 -1  1  0  0
 0  2 -1 -1  1
 2  0 -1  0  0
 0  0  0  1 -1
-1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1269

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

-- R2,R1,R1 chain: k rounds
theorem r2r1r1_chain : ∀ k : ℕ, ∀ a c d e,
    ⟨a + 2 * k, (0 : ℕ), c + 1, d + k, e⟩ [fm]⊢*
    ⟨a, (0 : ℕ), c + k + 1, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show a + 2 * (k + 1) = (a + 2) + 2 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (a + 2) c (d + 1) e)
    rw [show c + k + 1 = (c + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show c + k + 2 = c + (k + 1) + 1 from by ring,
        show e + k + 1 = e + (k + 1) from by ring]
    finish

-- R2 chain with a=0: k rounds
theorem r2_chain : ∀ k : ℕ, ∀ b c d e,
    ⟨(0 : ℕ), b, c + k, d + k, e⟩ [fm]⊢*
    ⟨(0 : ℕ), b + 2 * k, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 2) c d (e + 1))
    rw [show b + 2 + 2 * k = b + 2 * (k + 1) from by ring,
        show e + 1 + k = e + (k + 1) from by ring]
    finish

-- R1,R1,R3 chain: k rounds
theorem r1r1r3_chain : ∀ k : ℕ, ∀ b c e,
    ⟨(2 : ℕ), b + 2 * k, c, (0 : ℕ), e⟩ [fm]⊢*
    ⟨(2 : ℕ), b, c + k, (0 : ℕ), e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring]
    step fm; step fm
    rw [show c + 1 + 1 = (c + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (c + 1) e)
    rw [show c + 1 + k = c + (k + 1) from by ring]
    finish

-- R3 chain: k rounds
theorem r3_chain : ∀ k : ℕ, ∀ a c e,
    ⟨a, (0 : ℕ), c + k, (0 : ℕ), e⟩ [fm]⊢*
    ⟨a + 2 * k, (0 : ℕ), c, (0 : ℕ), e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c e)
    rw [show a + 2 + 2 * k = a + 2 * (k + 1) from by ring]
    finish

-- R4 chain: k rounds
theorem r4_chain : ∀ k : ℕ, ∀ a d e,
    ⟨a, (0 : ℕ), (0 : ℕ), d, e + k⟩ [fm]⊢*
    ⟨a, (0 : ℕ), (0 : ℕ), d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 1) e)
    ring_nf; finish

-- Main transition for even n=2m (m >= 0): (2m+1, 0, 0, 2m, 0) ->+ (2m+2, 0, 0, 2m+1, 0)
theorem main_transition_even (m : ℕ) :
    ⟨2 * m + 1, (0 : ℕ), (0 : ℕ), 2 * m, (0 : ℕ)⟩ [fm]⊢⁺
    ⟨2 * m + 2, (0 : ℕ), (0 : ℕ), 2 * m + 1, (0 : ℕ)⟩ := by
  -- R5
  rw [show 2 * m + 1 = (2 * m) + 1 from by ring]
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨(2 * m) + 1, 0, 0, 2 * m, 0⟩ : Q) [fm]⊢ ⟨2 * m, 0, 1, 2 * m, 1⟩)
  have h1 := r2r1r1_chain m 0 0 m 1
  have h1' : ⟨2 * m, (0 : ℕ), 1, 2 * m, 1⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), m + 1, m, m + 1⟩ := by
    convert h1 using 2; ring_nf
  apply stepStar_trans h1'
  -- State: (0, 0, m+1, m, m+1). R2 chain k=m.
  have h2 := r2_chain m 0 1 0 (m + 1)
  have h2' : ⟨(0 : ℕ), (0 : ℕ), m + 1, m, m + 1⟩ [fm]⊢* ⟨(0 : ℕ), 2 * m, 1, (0 : ℕ), 2 * m + 1⟩ := by
    convert h2 using 2; ring_nf
  apply stepStar_trans h2'
  -- R3
  step fm
  -- State: (2, 2m, 0, 0, 2m+1). R1R1R3 chain k=m.
  have h3 := r1r1r3_chain m 0 0 (2 * m + 1)
  have h3' : ⟨(2 : ℕ), 2 * m, 0, (0 : ℕ), 2 * m + 1⟩ [fm]⊢* ⟨(2 : ℕ), (0 : ℕ), m, (0 : ℕ), 2 * m + 1⟩ := by
    convert h3 using 2; ring_nf
  apply stepStar_trans h3'
  -- R3 chain k=m
  have h4 := r3_chain m 2 0 (2 * m + 1)
  have h4' : ⟨(2 : ℕ), (0 : ℕ), m, (0 : ℕ), 2 * m + 1⟩ [fm]⊢* ⟨2 * m + 2, (0 : ℕ), (0 : ℕ), (0 : ℕ), 2 * m + 1⟩ := by
    convert h4 using 2; ring_nf
  apply stepStar_trans h4'
  -- R4 chain
  have h5 := r4_chain (2 * m + 1) (2 * m + 2) 0 0
  have h5' : ⟨2 * m + 2, (0 : ℕ), (0 : ℕ), (0 : ℕ), 2 * m + 1⟩ [fm]⊢* ⟨2 * m + 2, (0 : ℕ), (0 : ℕ), 2 * m + 1, (0 : ℕ)⟩ := by
    convert h5 using 2; ring_nf
  apply stepStar_trans h5'
  finish

-- Main transition for odd n=2m+1: (2m+2, 0, 0, 2m+1, 0) ->+ (2m+3, 0, 0, 2m+2, 0)
theorem main_transition_odd (m : ℕ) :
    ⟨2 * m + 2, (0 : ℕ), (0 : ℕ), 2 * m + 1, (0 : ℕ)⟩ [fm]⊢⁺
    ⟨2 * m + 3, (0 : ℕ), (0 : ℕ), 2 * m + 2, (0 : ℕ)⟩ := by
  -- R5
  rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨(2 * m + 1) + 1, 0, 0, 2 * m + 1, 0⟩ : Q) [fm]⊢ ⟨2 * m + 1, 0, 1, 2 * m + 1, 1⟩)
  -- R2R1R1 chain k=m
  have h1 := r2r1r1_chain m 1 0 (m + 1) 1
  have h1' : ⟨2 * m + 1, (0 : ℕ), 1, 2 * m + 1, 1⟩ [fm]⊢* ⟨1, (0 : ℕ), m + 1, m + 1, m + 1⟩ := by
    convert h1 using 2; ring_nf
  apply stepStar_trans h1'
  -- R2: (1, 0, m+1, m+1, m+1) -> (1, 2, m, m, m+2)
  rw [show m + 1 = (m : ℕ) + 1 from by ring]
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨1, 0, (m : ℕ) + 1, m + 1, m + 1⟩ : Q) [fm]⊢ ⟨1, 2, m, m, m + 2⟩))
  -- R1: (1, 2, m, m, m+2) -> (0, 1, m+1, m, m+2)
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨1, 2, m, m, m + 2⟩ : Q) [fm]⊢ ⟨0, 1, m + 1, m, m + 2⟩))
  -- R2 chain k=m
  have h2 := r2_chain m 1 1 0 (m + 2)
  have h2' : ⟨(0 : ℕ), 1, m + 1, m, m + 2⟩ [fm]⊢* ⟨(0 : ℕ), 2 * m + 1, 1, (0 : ℕ), 2 * m + 2⟩ := by
    convert h2 using 2; ring_nf
  apply stepStar_trans h2'
  -- R3
  step fm
  -- R1R1R3 chain k=m
  have h3 := r1r1r3_chain m 1 0 (2 * m + 2)
  have h3' : ⟨(2 : ℕ), 2 * m + 1, 0, (0 : ℕ), 2 * m + 2⟩ [fm]⊢* ⟨(2 : ℕ), 1, m, (0 : ℕ), 2 * m + 2⟩ := by
    convert h3 using 2; ring_nf
  apply stepStar_trans h3'
  -- R1: (2, 1, m, 0, 2m+2) -> (1, 0, m+1, 0, 2m+2)
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨2, 1, m, 0, 2 * m + 2⟩ : Q) [fm]⊢ ⟨1, 0, m + 1, 0, 2 * m + 2⟩))
  -- R3 chain k=m+1: (1, 0, m+1, 0, 2m+2) ->* (2m+3, 0, 0, 0, 2m+2)
  have h4 := r3_chain (m + 1) 1 0 (2 * m + 2)
  have h4' : ⟨1, (0 : ℕ), m + 1, (0 : ℕ), 2 * m + 2⟩ [fm]⊢* ⟨2 * m + 3, (0 : ℕ), (0 : ℕ), (0 : ℕ), 2 * m + 2⟩ := by
    convert h4 using 2; ring_nf
  apply stepStar_trans h4'
  -- R4 chain
  have h5 := r4_chain (2 * m + 2) (2 * m + 3) 0 0
  have h5' : ⟨2 * m + 3, (0 : ℕ), (0 : ℕ), (0 : ℕ), 2 * m + 2⟩ [fm]⊢* ⟨2 * m + 3, (0 : ℕ), (0 : ℕ), 2 * m + 2, (0 : ℕ)⟩ := by
    convert h5 using 2; ring_nf
  apply stepStar_trans h5'
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, n + 1, 0⟩) 0
  intro n
  exists n + 1
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    have h := main_transition_odd m
    convert h using 2; ring_nf
  · subst hm
    have h := main_transition_even (m + 1)
    convert h using 2

end Sz22_2003_unofficial_1269
