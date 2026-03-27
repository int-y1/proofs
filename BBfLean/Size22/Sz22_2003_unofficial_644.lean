import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #644: [35/6, 143/2, 4/55, 39/7, 15/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  1  1
 2  0 -1  0 -1  0
 0  1  0 -1  0  1
 0  1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_644

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c+1, d, e, f⟩
  | _ => none

-- R4 repeated: convert d to b,f
theorem r4_chain : ∀ k b f, ⟨0, b, 0, d+k, e, f⟩ [fm]⊢* ⟨0, b+k, 0, d, e, f+k⟩ := by
  intro k; induction' k with k h <;> intro b f
  · exists 0
  rw [show d + (k + 1) = d + k + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R1,R1,R3 round chain
theorem r1r1r3_chain : ∀ k c d e, ⟨2, b+2*k, c, d, e+k, f⟩ [fm]⊢* ⟨2, b, c+k, d+2*k, e, f⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R3,R2,R2 drain chain
theorem r3r2r2_drain : ∀ k e f, ⟨0, 0, k+1, d, e+1, f⟩ [fm]⊢* ⟨0, 0, 0, d, e+k+2, f+2*k+2⟩ := by
  intro k; induction' k with k h <;> intro e f
  · step fm; step fm; step fm; finish
  rw [show (k+1)+1 = (k+1+1) from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R2,R2 then R3,R2,R2 drain (even case)
theorem r2r2_drain : ⟨2, 0, k+1, D, e, F⟩ [fm]⊢* ⟨0, 0, 0, D, e+k+3, F+2*k+4⟩ := by
  step fm; step fm
  rw [show e+1+1 = (e+1)+1 from by ring, show F+1+1 = F+2 from by ring]
  apply stepStar_trans (r3r2r2_drain (d := D) k (e+1) (F+2))
  ring_nf; finish

-- R1,R2 then R3,R2,R2 drain (odd case)
theorem r1r2_drain : ⟨2, 1, k+1, D, e+1, F⟩ [fm]⊢* ⟨0, 0, 0, D+1, e+k+4, F+2*k+5⟩ := by
  step fm; step fm
  apply stepStar_trans (r3r2r2_drain (d := D+1) (k+1) (e+1) (F+1))
  ring_nf; finish

-- Full even transition: C(2*m) ->+ C(2*m+1)
theorem even_trans : ∀ m,
    ⟨0, 0, 0, 2*m+1, 2*m+2, 4*m*m+6*m+3⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2*m+2, 2*m+3, 4*m*m+10*m+7⟩ := by
  intro m
  -- R4 x (2*m+1)
  rw [show 2*m+1 = 0 + (2*m+1) from by ring,
      show 4*m*m+6*m+3 = (0 : ℕ) + (4*m*m+6*m+3) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (d := 0) (e := 2*m+2) _ _ _)
  simp only [Nat.zero_add]
  -- R5
  rw [show 4*m*m+6*m+3+(2*m+1) = (4*m*m+8*m+3)+1 from by ring]
  step fm
  -- R3
  rw [show 2*m+1+1 = (2*m+1)+1 from by ring]
  step fm
  -- R1,R1,R3 chain x (m+1)
  rw [show 2*m+1+1 = 0+2*(m+1) from by ring,
      show 2*m+1 = m+(m+1) from by ring]
  apply stepStar_trans (r1r1r3_chain (b := 0) (f := 4*m*m+8*m+3) _ _ _ _)
  simp only [Nat.zero_add]
  apply stepStar_trans (r2r2_drain (k := m) (D := 2*(m+1)) (e := m) (F := 4*m*m+8*m+3))
  ring_nf; finish

-- Full odd transition: C(2*m+1) ->+ C(2*m+2)
theorem odd_trans : ∀ m,
    ⟨0, 0, 0, 2*m+2, 2*m+3, 4*m*m+10*m+7⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2*m+3, 2*m+4, 4*m*m+14*m+13⟩ := by
  intro m
  -- R4 x (2*m+2)
  rw [show 2*m+2 = 0+(2*m+2) from by ring,
      show 4*m*m+10*m+7 = (0 : ℕ)+(4*m*m+10*m+7) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (d := 0) (e := 2*m+3) _ _ _)
  simp only [Nat.zero_add]
  -- R5
  rw [show 4*m*m+10*m+7+(2*m+2) = (4*m*m+12*m+8)+1 from by ring]
  step fm
  -- R3
  rw [show 2*m+2+1 = (2*m+2)+1 from by ring]
  step fm
  -- R1,R1,R3 chain x (m+1)
  rw [show 2*m+2+1 = 1+2*(m+1) from by ring,
      show 2*m+2 = (m+1)+(m+1) from by ring]
  apply stepStar_trans (r1r1r3_chain (b := 1) (f := 4*m*m+12*m+8) _ _ _ _)
  simp only [Nat.zero_add]
  apply stepStar_trans (r1r2_drain (k := m) (D := 2*(m+1)) (e := m) (F := 4*m*m+12*m+8))
  ring_nf; finish

-- Main transition: C(n) ->+ C(n+1)
theorem main_trans (n : ℕ) :
    ⟨0, 0, 0, n+1, n+2, n*n+3*n+3⟩ [fm]⊢⁺
    ⟨0, 0, 0, n+2, n+3, n*n+5*n+7⟩ := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    have h := even_trans m
    have h1 : m+m+1 = 2*m+1 := by ring
    have h2 : m+m+2 = 2*m+2 := by ring
    have h3 : (m+m)*(m+m)+3*(m+m)+3 = 4*m*m+6*m+3 := by ring
    have h4 : m+m+3 = 2*m+3 := by ring
    have h5 : (m+m)*(m+m)+5*(m+m)+7 = 4*m*m+10*m+7 := by ring
    rw [h1, h2, h3, h4, h5]; exact h
  · subst hm
    have h := odd_trans m
    have h1 : 2*m+1+1 = 2*m+2 := by ring
    have h2 : 2*m+1+2 = 2*m+3 := by ring
    have h3 : (2*m+1)*(2*m+1)+3*(2*m+1)+3 = 4*m*m+10*m+7 := by ring
    have h4 : 2*m+1+3 = 2*m+4 := by ring
    have h5 : (2*m+1)*(2*m+1)+5*(2*m+1)+7 = 4*m*m+14*m+13 := by ring
    rw [h1, h2, h3, h4, h5]; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2, 3⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n+1, n+2, n*n+3*n+3⟩) 0
  intro n; refine ⟨n+1, ?_⟩
  have h := main_trans n
  have : n*n+5*n+7 = (n+1)*(n+1)+3*(n+1)+3 := by ring
  rw [this] at h; exact h

end Sz22_2003_unofficial_644
