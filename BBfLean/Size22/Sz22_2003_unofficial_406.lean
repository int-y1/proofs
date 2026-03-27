import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #406: [225/77, 7/6, 121/3, 2/5, 21/2]

Vector representation:
```
 0  2  2 -1 -1
-1 -1  0  1  0
 0 -1  0  0  2
 1  0 -1  0  0
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_406

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c+2, d, e⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R2+R1 chain: each pair consumes 1 from a and e, adds 1 to b and 2 to c
-- Requires b ≥ 1 (expressed as b+1)
theorem r2r1_chain : ∀ k a b c e,
    ⟨a+k, b+1, c, 0, e+k⟩ [fm]⊢* ⟨a, b+k+1, c+2*k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a b c e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm -- R2: (a+k, b, c, 1, (e+k)+1)
  step fm -- R1: (a+k, b+2, c+2, 0, e+k)
  apply stepStar_trans (ih a (b + 1) (c + 2) e)
  ring_nf; finish

-- R3 drain: convert b to e (a=0, d=0, so only R3 applies)
theorem b_drain : ∀ k c e,
    ⟨0, k, c, 0, e⟩ [fm]⊢* ⟨0, 0, c, 0, e+2*k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  step fm -- R3: (0, k, c, 0, e+2)
  apply stepStar_trans (ih c (e + 2))
  ring_nf; finish

-- R4 drain: convert c to a (b=0, d=0, so only R4 applies)
theorem c_drain : ∀ k a e,
    ⟨a, 0, k, 0, e⟩ [fm]⊢* ⟨a+k, 0, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  step fm -- R4: (a+1, 0, k, 0, e)
  apply stepStar_trans (ih (a + 1) e)
  ring_nf; finish

-- Main transition: (a+1, 0, 0, 0, e+a+1) →⁺ (2*a+2, 0, 0, 0, e+2*a+6)
theorem main_trans (a e : ℕ) :
    ⟨a+1, 0, 0, 0, e+a+1⟩ [fm]⊢⁺ ⟨2*a+2, 0, 0, 0, e+2*a+6⟩ := by
  -- R5: → (a, 1, 0, 1, e+a+1)
  step fm
  -- R1: rewrite e+a+1 = (e+a)+1
  rw [show e + a + 1 = (e + a) + 1 from by ring]
  step fm -- R1: → (a, 3, 2, 0, e+a)
  -- R2+R1 chain: a steps: (a, 3, 2, 0, e+a) →* (0, a+3, 2+2*a, 0, e)
  apply stepStar_trans
  · have h := r2r1_chain a 0 2 2 e
    simp only [Nat.zero_add] at h; exact h
  -- b_drain: (a+3) steps: (0, a+3, 2+2*a, 0, e) →* (0, 0, 2+2*a, 0, e+2*(a+3))
  apply stepStar_trans
  · have h := b_drain (a + 3) (2 + 2 * a) e
    simp only [show 2 + a + 1 = a + 3 from by ring] at h ⊢; exact h
  -- c_drain: (2+2*a) steps: (0, 0, 2+2*a, 0, e+2*(a+3)) →* (2+2*a, 0, 0, 0, e+2*(a+3))
  apply stepStar_trans
  · have h := c_drain (2 + 2 * a) 0 (e + 2 * (a + 3))
    simp only [Nat.zero_add] at h; exact h
  -- (2+2*a, 0, 0, 0, e+2*(a+3)) = (2*a+2, 0, 0, 0, e+2*a+6)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 5⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, e⟩ ↦ ⟨a+1, 0, 0, 0, e+a+1⟩) ⟨1, 3⟩
  intro ⟨a, e⟩
  refine ⟨⟨2*a+1, e+4⟩, ?_⟩
  show ⟨a+1, 0, 0, 0, e+a+1⟩ [fm]⊢⁺ ⟨(2*a+1)+1, 0, 0, 0, (e+4)+(2*a+1)+1⟩
  simp only [show (2 * a + 1) + 1 = 2 * a + 2 from by ring,
             show (e + 4) + (2 * a + 1) + 1 = e + 2 * a + 6 from by ring]
  exact main_trans a e

end Sz22_2003_unofficial_406
