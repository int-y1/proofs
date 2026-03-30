import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1113: [5/6, 4/35, 539/2, 9/11, 22/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  0
-1  0  0  2  1
 0  2  0  0 -1
 1  0  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1113

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

theorem r3_chain : ∀ k d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d + 2) (e + 1))
    ring_nf; finish

theorem r4_chain : ∀ k b, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + 2 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 2))
    ring_nf; finish

theorem setup : ⟨0, b + 1, 0, d + 2, 0⟩ [fm]⊢* ⟨2, b, 0, d, 1⟩ := by
  step fm; step fm; step fm; finish

theorem interleave :
    ∀ k b c d, ⟨2, b + 2 * k, c, d + k, 1⟩ [fm]⊢* ⟨2, b, c + k, d, 1⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 1) d)
    ring_nf; finish

theorem r2_chain : ∀ k a c d, ⟨a, 0, c + k, d + k, e⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d)
    ring_nf; finish

theorem r2_chain_z : ∀ k, ⟨a, 0, c + k, k, e⟩ [fm]⊢* ⟨a + 2 * k, 0, c, 0, e⟩ := by
  intro k
  have h := r2_chain (e := e) k a c 0
  simp at h; exact h

theorem tail_round : ⟨a + 1, 0, c + 2, 0, e⟩ [fm]⊢* ⟨a + 4, 0, c, 0, e + 1⟩ := by
  step fm; step fm; step fm; ring_nf; finish

theorem tail_even : ∀ k a e, ⟨a + 1, 0, c + 2 * k, 0, e⟩ [fm]⊢*
    ⟨a + 3 * k + 1, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
    apply stepStar_trans (tail_round (a := a) (c := c + 2 * k) (e := e))
    rw [show a + 4 = (a + 3) + 1 from by ring]
    apply stepStar_trans (ih (a + 3) (e + 1))
    ring_nf; finish

theorem tail_c1 : ⟨a + 1, 0, 1, 0, e⟩ [fm]⊢* ⟨a + 1, 0, 0, 3, e + 2⟩ := by
  step fm; step fm; step fm; finish

theorem half1 (A e : ℕ) :
    ⟨A + e + 1, 0, 0, 0, e⟩ [fm]⊢* ⟨2 * A + 3 * e + 1, 0, 0, 3, e + 3⟩ := by
  -- R3 x (A+e+1)
  rw [show A + e + 1 = 0 + (A + e + 1) from by ring]
  apply stepStar_trans (r3_chain (a := 0) (A + e + 1) 0 e)
  rw [show 0 + 2 * (A + e + 1) = 2 * A + 2 * e + 2 from by ring,
      show e + (A + e + 1) = 0 + (A + 2 * e + 1) from by ring]
  -- R4 x (A+2e+1)
  apply stepStar_trans (r4_chain (d := 2 * A + 2 * e + 2) (e := 0) (A + 2 * e + 1) 0)
  rw [show 0 + 2 * (A + 2 * e + 1) = (2 * A + 4 * e + 1) + 1 from by ring,
      show 2 * A + 2 * e + 2 = (2 * A + 2 * e) + 2 from by ring]
  -- Setup
  apply stepStar_trans (setup (b := 2 * A + 4 * e + 1) (d := 2 * A + 2 * e))
  -- Interleave x (A+2e)
  rw [show 2 * A + 4 * e + 1 = 1 + 2 * (A + 2 * e) from by ring,
      show 2 * A + 2 * e = A + (A + 2 * e) from by ring]
  apply stepStar_trans (interleave (A + 2 * e) 1 0 A)
  -- (2, 1, A+2e, A, 1). Last R1.
  rw [show 0 + (A + 2 * e) = A + 2 * e from by ring]
  step fm
  -- (1, 0, A+2e+1, A, 1). R2 x A.
  rw [show A + 2 * e + 1 = (2 * e + 1) + A from by ring]
  apply stepStar_trans (r2_chain_z (a := 1) (c := 2 * e + 1) (e := 1) A)
  rw [show 1 + 2 * A = (2 * A) + 1 from by ring,
      show 2 * e + 1 = 1 + 2 * e from by ring]
  -- tail_even x e
  apply stepStar_trans (tail_even (c := 1) e (2 * A) 1)
  -- (2A+3e+1, 0, 1, 0, e+1)
  rw [show 2 * A + 3 * e + 1 = (2 * A + 3 * e) + 1 from by ring,
      show 1 + e = e + 1 from by ring]
  -- tail_c1
  apply stepStar_trans (tail_c1 (a := 2 * A + 3 * e) (e := e + 1))
  ring_nf; finish

theorem half2 (N F : ℕ) :
    ⟨N + F + 1, 0, 0, 3, F + 1⟩ [fm]⊢* ⟨2 * N + 3 * F + 5, 0, 0, 0, F + 1⟩ := by
  -- R3 x (N+F+1)
  rw [show N + F + 1 = 0 + (N + F + 1) from by ring]
  apply stepStar_trans (r3_chain (a := 0) (N + F + 1) 3 (F + 1))
  rw [show 3 + 2 * (N + F + 1) = 2 * N + 2 * F + 5 from by ring,
      show F + 1 + (N + F + 1) = 0 + (N + 2 * F + 2) from by ring]
  -- R4 x (N+2F+2)
  apply stepStar_trans (r4_chain (d := 2 * N + 2 * F + 5) (e := 0) (N + 2 * F + 2) 0)
  rw [show 0 + 2 * (N + 2 * F + 2) = (2 * N + 4 * F + 3) + 1 from by ring,
      show 2 * N + 2 * F + 5 = (2 * N + 2 * F + 3) + 2 from by ring]
  -- Setup
  apply stepStar_trans (setup (b := 2 * N + 4 * F + 3) (d := 2 * N + 2 * F + 3))
  -- Interleave x (N+2F+1)
  rw [show 2 * N + 4 * F + 3 = 1 + 2 * (N + 2 * F + 1) from by ring,
      show 2 * N + 2 * F + 3 = (N + 2) + (N + 2 * F + 1) from by ring]
  apply stepStar_trans (interleave (N + 2 * F + 1) 1 0 (N + 2))
  rw [show 0 + (N + 2 * F + 1) = N + 2 * F + 1 from by ring]
  -- Last R1
  step fm
  -- R2 x (N+2)
  rw [show N + 2 * F + 1 + 1 = (2 * F) + (N + 2) from by ring]
  apply stepStar_trans (r2_chain_z (a := 1) (c := 2 * F) (e := 1) (N + 2))
  -- (2N+5, 0, 2F, 0, 1)
  rw [show 1 + 2 * (N + 2) = (2 * N + 4) + 1 from by ring,
      show 2 * F = 0 + 2 * F from by ring]
  -- tail_even x F
  apply stepStar_trans (tail_even (c := 0) F (2 * N + 4) 1)
  ring_nf; finish

theorem main_trans (A e : ℕ) :
    ⟨A + e + 2, 0, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨4 * A + 7 * e + 14, 0, 0, 0, e + 4⟩ := by
  -- half1 with A_h1 = A, e_h1 = e+1:
  -- (A + (e+1) + 1, 0, 0, 0, e+1) = (A+e+2, 0, 0, 0, e+1) ✓
  -- result: (2A + 3(e+1) + 1, 0, 0, 3, (e+1)+3) = (2A+3e+4, 0, 0, 3, e+4)
  rw [show A + e + 2 = A + (e + 1) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (half1 A (e + 1))
  -- Need: (2A+3(e+1)+1, 0, 0, 3, (e+1)+3) ⊢⁺ (4A+7e+14, 0, 0, 0, e+4)
  -- = (2A+3e+4, 0, 0, 3, e+4) ⊢⁺ (4A+7e+14, 0, 0, 0, e+4)
  show ⟨2 * A + 3 * (e + 1) + 1, 0, 0, 3, (e + 1) + 3⟩ [fm]⊢⁺ _
  rw [show 2 * A + 3 * (e + 1) + 1 = (2 * A + 2 * e) + (e + 3) + 1 from by ring,
      show (e + 1) + 3 = (e + 3) + 1 from by ring]
  -- half2 with N = 2A+2e, F = e+3
  -- N+F+1 = 2A+2e+e+3+1 = 2A+3e+4 ✓
  -- Need ⊢⁺ not ⊢*. First step of half2 is R3 (since N+F+1 = 2A+3e+4 >= 1).
  -- Use step + stepStar to get stepPlus.
  -- (2A+3e+4, 0, 0, 3, e+4) → R3 → (2A+3e+3, 0, 0, 5, e+5)
  rw [show (2 * A + 2 * e) + (e + 3) + 1 = (2 * A + 3 * e + 3) + 1 from by ring,
      show (e + 3) + 1 = e + 4 from by ring]
  apply step_stepStar_stepPlus (c₂ := ⟨2 * A + 3 * e + 3, 0, 0, 5, e + 5⟩)
  · simp [fm]
  -- Now: (2A+3e+3, 0, 0, 5, e+5) →* (4A+7e+14, 0, 0, 0, e+4)
  -- This is the rest of half2 after the first R3 step.
  -- r3_chain with a=0, k=2A+3e+3, d=5, e=e+5:
  -- (2A+3e+3, 0, 0, 5, e+5) →* (0, 0, 0, 5+2(2A+3e+3), e+5+2A+3e+3)
  -- = (0, 0, 0, 4A+6e+11, 2A+4e+8)
  rw [show 2 * A + 3 * e + 3 = 0 + (2 * A + 3 * e + 3) from by ring]
  apply stepStar_trans (r3_chain (a := 0) (2 * A + 3 * e + 3) 5 (e + 5))
  rw [show 5 + 2 * (2 * A + 3 * e + 3) = 4 * A + 6 * e + 11 from by ring,
      show e + 5 + (2 * A + 3 * e + 3) = 0 + (2 * A + 4 * e + 8) from by ring]
  apply stepStar_trans (r4_chain (d := 4 * A + 6 * e + 11) (e := 0) (2 * A + 4 * e + 8) 0)
  rw [show 0 + 2 * (2 * A + 4 * e + 8) = (4 * A + 8 * e + 15) + 1 from by ring,
      show 4 * A + 6 * e + 11 = (4 * A + 6 * e + 9) + 2 from by ring]
  apply stepStar_trans (setup (b := 4 * A + 8 * e + 15) (d := 4 * A + 6 * e + 9))
  rw [show 4 * A + 8 * e + 15 = 1 + 2 * (2 * A + 4 * e + 7) from by ring,
      show 4 * A + 6 * e + 9 = (2 * A + 2 * e + 2) + (2 * A + 4 * e + 7) from by ring]
  apply stepStar_trans (interleave (2 * A + 4 * e + 7) 1 0 (2 * A + 2 * e + 2))
  rw [show 0 + (2 * A + 4 * e + 7) = 2 * A + 4 * e + 7 from by ring]
  step fm
  rw [show 2 * A + 4 * e + 7 + 1 = (2 * e + 6) + (2 * A + 2 * e + 2) from by ring]
  apply stepStar_trans (r2_chain_z (a := 1) (c := 2 * e + 6) (e := 1) (2 * A + 2 * e + 2))
  rw [show 1 + 2 * (2 * A + 2 * e + 2) = (4 * A + 4 * e + 4) + 1 from by ring,
      show 2 * e + 6 = 0 + 2 * (e + 3) from by ring]
  apply stepStar_trans (tail_even (c := 0) (e + 3) (4 * A + 4 * e + 4) 1)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨7, 0, 0, 0, 3⟩)
  · execute fm 33
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨A, e⟩ ↦ ⟨A + e + 2, 0, 0, 0, e + 1⟩) ⟨3, 2⟩
  intro ⟨A, e⟩
  refine ⟨⟨4 * A + 6 * e + 9, e + 3⟩, ?_⟩
  show ⟨A + e + 2, 0, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨4 * A + 6 * e + 9 + (e + 3) + 2, 0, 0, 0, (e + 3) + 1⟩
  rw [show 4 * A + 6 * e + 9 + (e + 3) + 2 = 4 * A + 7 * e + 14 from by ring,
      show (e + 3) + 1 = e + 4 from by ring]
  exact main_trans A e

end Sz22_2003_unofficial_1113
