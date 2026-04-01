import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1339: [63/10, 2/33, 1573/2, 5/7, 21/13]

Vector representation:
```
-1  2 -1  1  0  0
 1 -1  0  0 -1  0
-1  0  0  0  2  1
 0  0  1 -1  0  0
 0  1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1339

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e, f⟩ => some ⟨a, b+2, c, d+1, e, f⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a+1, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+2, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | _ => none

-- R4 chain: transfer d to c.
theorem r4_chain : ∀ k, ∀ c d,
    ⟨(0 : ℕ), 0, c, d + k, e, f⟩ [fm]⊢* ⟨0, 0, c + k, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    rw [show c + (k + 1) = (c + 1) + k from by ring]
    exact ih (c + 1) d

-- R1+R2 chain: each pair does R1 then R2.
-- From (1, b, c+1, d, e+1, F):
--   R1: (0, b+2, c, d+1, e+1, F)
--   R2: (1, b+1, c, d+1, e, F)
-- Net: b+=1, c-=1, d+=1, e-=1.
-- So: (1, b, k, d, k+1, F) →* (1, b+k, 0, d+k, 1, F)
theorem r1r2_chain : ∀ k, ∀ b d,
    ⟨(1 : ℕ), b, k, d, k + 1, F⟩ [fm]⊢* ⟨1, b + k, 0, d + k, 1, F⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · ring_nf; finish
  · step fm; step fm
    rw [show b + (k + 1) = (b + 1) + k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    exact ih (b + 1) (d + 1)

-- R3+R2+R2 loop.
-- From (a+1, b+2, 0, D, 0, F):
--   R3: (a, b+2, 0, D, 2, F+1)
--   R2: (a+1, b+1, 0, D, 1, F+1)
--   R2: (a+2, b, 0, D, 0, F+1)
-- Net: a+=1, b-=2, F+=1.
-- After k rounds: (a+1, b+2*k, 0, D, 0, F) →* (a+1+k, b, 0, D, 0, F+k)
theorem r3r2r2_loop : ∀ k, ∀ a b D F,
    ⟨a + 1, b + 2 * k, (0 : ℕ), D, 0, F⟩ [fm]⊢* ⟨a + 1 + k, b, 0, D, 0, F + k⟩ := by
  intro k; induction' k with k ih <;> intro a b D F
  · ring_nf; finish
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring]
    step fm; step fm; step fm
    rw [show a + 1 + (k + 1) = (a + 1) + 1 + k from by ring,
        show F + (k + 1) = (F + 1) + k from by ring]
    exact ih (a + 1) b D (F + 1)

-- R3 drain: each step: (A+1,0,0,D,E,F)→(A,0,0,D,E+2,F+1).
theorem r3_drain : ∀ A, ∀ D E F,
    ⟨A, (0 : ℕ), 0, D, E, F⟩ [fm]⊢* ⟨0, 0, 0, D, E + 2 * A, F + A⟩ := by
  intro A; induction' A with A ih <;> intro D E F
  · exists 0
  · step fm
    rw [show E + 2 * (A + 1) = (E + 2) + 2 * A from by ring,
        show F + (A + 1) = (F + 1) + A from by ring]
    exact ih D (E + 2) (F + 1)

-- Main transition for n even: n = 2*m.
-- (0, 0, 0, 2m+2, 2m+4, f+1) →⁺ (0, 0, 0, 2m+3, 2m+5, f+2m+3)
theorem main_even (m f : ℕ) :
    ⟨(0 : ℕ), 0, 0, 2 * m + 2, 2 * m + 4, f + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * m + 3, 2 * m + 5, f + 2 * m + 3⟩ := by
  -- Phase 1: R4 chain (2m+2 steps).
  have h1 : ⟨(0 : ℕ), 0, 0, 2 * m + 2, 2 * m + 4, f + 1⟩ [fm]⊢*
      ⟨0, 0, 2 * m + 2, 0, 2 * m + 4, f + 1⟩ := by
    have := r4_chain (2 * m + 2) 0 0 (e := 2 * m + 4) (f := f + 1)
    simpa using this
  -- Phase 2: R5 + R2 (2 steps).
  have h2 : ⟨(0 : ℕ), 0, 2 * m + 2, 0, 2 * m + 4, f + 1⟩ [fm]⊢⁺
      ⟨1, 0, 2 * m + 2, 1, 2 * m + 3, f⟩ := by
    rw [show (2 * m + 4 : ℕ) = (2 * m + 3) + 1 from by ring]
    step fm; step fm; finish
  -- Phase 3: R1+R2 chain (2m+2 rounds).
  have h3 : ⟨(1 : ℕ), 0, 2 * m + 2, 1, 2 * m + 3, f⟩ [fm]⊢*
      ⟨1, 2 * m + 2, 0, 2 * m + 3, 1, f⟩ := by
    have := r1r2_chain (2 * m + 2) 0 1 (F := f)
    rw [show (2 * m + 2) + 1 = 2 * m + 3 from by ring,
        show 0 + (2 * m + 2) = 2 * m + 2 from by ring,
        show 1 + (2 * m + 2) = 2 * m + 3 from by ring] at this
    exact this
  -- Phase 4: R2 step.
  have h4 : ⟨(1 : ℕ), 2 * m + 2, 0, 2 * m + 3, 1, f⟩ [fm]⊢⁺
      ⟨2, 2 * m + 1, 0, 2 * m + 3, 0, f⟩ := by
    rw [show (2 * m + 2 : ℕ) = (2 * m + 1) + 1 from by ring]
    step fm; finish
  -- Phase 5: R3+R2+R2 loop (m rounds).
  -- (2, 2m+1, 0, 2m+3, 0, f) with b = 2m+1 = 1 + 2*m.
  -- Loop m rounds: (2+m, 1, 0, 2m+3, 0, f+m).
  have h5 : ⟨(2 : ℕ), 2 * m + 1, 0, 2 * m + 3, 0, f⟩ [fm]⊢*
      ⟨m + 2, 1, 0, 2 * m + 3, 0, f + m⟩ := by
    rw [show (2 * m + 1 : ℕ) = 1 + 2 * m from by ring,
        show (2 : ℕ) = 1 + 1 from by ring,
        show m + 2 = 1 + 1 + m from by ring]
    exact r3r2r2_loop m 1 1 (2 * m + 3) f
  -- Phase 6: R3 + R2 (b=1 tail).
  have h6 : ⟨(m + 2 : ℕ), 1, 0, 2 * m + 3, 0, f + m⟩ [fm]⊢*
      ⟨m + 2, 0, 0, 2 * m + 3, 1, f + m + 1⟩ := by
    rw [show (m + 2 : ℕ) = (m + 1) + 1 from by ring]
    step fm; step fm; ring_nf; finish
  -- Phase 7: R3 drain (m+2 steps).
  have h7 : ⟨(m + 2 : ℕ), 0, 0, 2 * m + 3, 1, f + m + 1⟩ [fm]⊢*
      ⟨0, 0, 0, 2 * m + 3, 2 * m + 5, f + 2 * m + 3⟩ := by
    have := r3_drain (m + 2) (2 * m + 3) 1 (f + m + 1)
    convert this using 2; ring_nf
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2
      (stepStar_trans h3
        (stepStar_trans (stepPlus_stepStar h4)
          (stepStar_trans h5
            (stepStar_trans h6 h7)))))

-- Main transition for n odd: n = 2*m+1.
-- (0, 0, 0, 2m+3, 2m+5, f+1) →⁺ (0, 0, 0, 2m+4, 2m+6, f+2m+4)
theorem main_odd (m f : ℕ) :
    ⟨(0 : ℕ), 0, 0, 2 * m + 3, 2 * m + 5, f + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * m + 4, 2 * m + 6, f + 2 * m + 4⟩ := by
  -- Phase 1: R4 chain.
  have h1 : ⟨(0 : ℕ), 0, 0, 2 * m + 3, 2 * m + 5, f + 1⟩ [fm]⊢*
      ⟨0, 0, 2 * m + 3, 0, 2 * m + 5, f + 1⟩ := by
    have := r4_chain (2 * m + 3) 0 0 (e := 2 * m + 5) (f := f + 1)
    simpa using this
  -- Phase 2: R5 + R2.
  have h2 : ⟨(0 : ℕ), 0, 2 * m + 3, 0, 2 * m + 5, f + 1⟩ [fm]⊢⁺
      ⟨1, 0, 2 * m + 3, 1, 2 * m + 4, f⟩ := by
    rw [show (2 * m + 5 : ℕ) = (2 * m + 4) + 1 from by ring]
    step fm; step fm; finish
  -- Phase 3: R1+R2 chain (2m+3 rounds).
  have h3 : ⟨(1 : ℕ), 0, 2 * m + 3, 1, 2 * m + 4, f⟩ [fm]⊢*
      ⟨1, 2 * m + 3, 0, 2 * m + 4, 1, f⟩ := by
    have := r1r2_chain (2 * m + 3) 0 1 (F := f)
    rw [show (2 * m + 3) + 1 = 2 * m + 4 from by ring,
        show 0 + (2 * m + 3) = 2 * m + 3 from by ring,
        show 1 + (2 * m + 3) = 2 * m + 4 from by ring] at this
    exact this
  -- Phase 4: R2 step.
  have h4 : ⟨(1 : ℕ), 2 * m + 3, 0, 2 * m + 4, 1, f⟩ [fm]⊢⁺
      ⟨2, 2 * m + 2, 0, 2 * m + 4, 0, f⟩ := by
    rw [show (2 * m + 3 : ℕ) = (2 * m + 2) + 1 from by ring]
    step fm; finish
  -- Phase 5: R3+R2+R2 loop (m+1 rounds). b=2m+2=0+2*(m+1).
  have h5 : ⟨(2 : ℕ), 2 * m + 2, 0, 2 * m + 4, 0, f⟩ [fm]⊢*
      ⟨m + 3, 0, 0, 2 * m + 4, 0, f + m + 1⟩ := by
    rw [show (2 * m + 2 : ℕ) = 0 + 2 * (m + 1) from by ring,
        show (2 : ℕ) = 1 + 1 from by ring,
        show m + 3 = 1 + 1 + (m + 1) from by ring,
        show f + m + 1 = f + (m + 1) from by ring]
    exact r3r2r2_loop (m + 1) 1 0 (2 * m + 4) f
  -- Phase 6: R3 drain (m+3 steps).
  have h6 : ⟨(m + 3 : ℕ), 0, 0, 2 * m + 4, 0, f + m + 1⟩ [fm]⊢*
      ⟨0, 0, 0, 2 * m + 4, 2 * m + 6, f + 2 * m + 4⟩ := by
    have := r3_drain (m + 3) (2 * m + 4) 0 (f + m + 1)
    convert this using 2; ring_nf
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2
      (stepStar_trans h3
        (stepStar_trans (stepPlus_stepStar h4)
          (stepStar_trans h5 h6))))

-- Combined main transition.
theorem main_trans (n f : ℕ) :
    ⟨(0 : ℕ), 0, 0, n + 2, n + 4, f + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, n + 3, n + 5, f + n + 3⟩ := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    exact main_even m f
  · subst hm
    exact main_odd m f

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 4, 2⟩) (by execute fm 12)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, f⟩ ↦ ⟨0, 0, 0, n + 2, n + 4, f + 1⟩) ⟨0, 1⟩
  intro ⟨n, f⟩
  exact ⟨⟨n + 1, f + n + 2⟩, main_trans n f⟩

end Sz22_2003_unofficial_1339
