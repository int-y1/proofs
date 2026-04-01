import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1462: [7/15, 3/77, 2662/3, 5/121, 21/2]

Vector representation:
```
 0 -1 -1  1  0
 0  1  0 -1 -1
 1 -1  0  0  3
 0  0  1  0 -2
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1462

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+3⟩
  | ⟨a, b, c, d, e+2⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R2 chain: transfer from d,e to b (c=0 so R1 doesn't fire)
theorem r2_chain : ∀ k, ∀ a b d e, ⟨a, b, 0, d + k, e + k⟩ [fm]⊢* ⟨a, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 1) d e); ring_nf; finish

-- R3 drain: when d=0 and c=0, drain b via R3
theorem r3_drain : ∀ k, ∀ a b e, ⟨a, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + k, b, 0, 0, e + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) b (e + 3)); ring_nf; finish

-- R4 drain: convert e to c in pairs
theorem r4_drain : ∀ k, ∀ a c e, ⟨a, 0, c, 0, e + 2 * k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) e); ring_nf; finish

-- R5+R1 chain: drain a and c simultaneously into d
theorem r5r1_chain : ∀ k, ∀ a c d, ⟨a + k, 0, c + k, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a c (d + 2)); ring_nf; finish

-- R3 step with arbitrary d: (a, b+1, 0, D, 0) → (a+1, b, 0, D, 3)
-- R1 needs c>=1 (c=0), R2 needs e>=1 (e=0), so R3 fires.
theorem r3_step_d : ∀ a b D, ⟨a, b + 1, 0, D, 0⟩ [fm]⊢* ⟨a + 1, b, 0, D, 3⟩ := by
  intro a b D; step fm; finish

-- One R2R3 round: R2 x3 then R3
theorem r2r3_round : ∀ a b D, ⟨a, b, 0, D + 3, 3⟩ [fm]⊢* ⟨a + 1, b + 2, 0, D, 3⟩ := by
  intro a b D
  rw [show (3 : ℕ) = 0 + 3 from by ring,
      show D + 3 = D + (0 + 3) from by ring]
  apply stepStar_trans (r2_chain 3 a b D 0)
  rw [show b + 3 = (b + 2) + 1 from by ring]
  apply r3_step_d a (b + 2) D

-- Multiple R2R3 rounds with remainder
theorem r2r3_rounds : ∀ k, ∀ a b r, ⟨a, b, 0, r + 3 * k, 3⟩ [fm]⊢* ⟨a + k, b + 2 * k, 0, r, 3⟩ := by
  intro k; induction' k with k ih <;> intro a b r
  · exists 0
  · rw [show r + 3 * (k + 1) = (r + 3 * k) + 3 from by ring]
    apply stepStar_trans (r2r3_round a b (r + 3 * k))
    apply stepStar_trans (ih (a + 1) (b + 2) r); ring_nf; finish

-- Phase B, D = 3k: (a, 0, 0, 3k, 3) → (a + 3k, 0, 0, 0, 6k + 3)
theorem phase_b_mod0 (k a : ℕ) :
    ⟨a, 0, 0, 3 * k, 3⟩ [fm]⊢* ⟨a + 3 * k, 0, 0, 0, 6 * k + 3⟩ := by
  rw [show 3 * k = 0 + 3 * k from by ring]
  apply stepStar_trans (r2r3_rounds k a 0 0)
  -- state: (a+k, 2k, 0, 0, 3). R3 drain on b=2k.
  rw [show 0 + 2 * k = 0 + 2 * k from rfl]
  apply stepStar_trans (r3_drain (2 * k) (a + k) 0 3)
  ring_nf; finish

-- Phase B, D = 3k+1: (a, 0, 0, 3k+1, 3) → (a + 3k + 1, 0, 0, 0, 6k + 5)
theorem phase_b_mod1 (k a : ℕ) :
    ⟨a, 0, 0, 3 * k + 1, 3⟩ [fm]⊢* ⟨a + 3 * k + 1, 0, 0, 0, 6 * k + 5⟩ := by
  rw [show 3 * k + 1 = 1 + 3 * k from by ring]
  apply stepStar_trans (r2r3_rounds k a 0 1)
  -- state: (a+k, 2k, 0, 1, 3). R2 fires once (d=1>=1, e=3>=1).
  rw [show 0 + 2 * k = 0 + 2 * k from rfl,
      show (1 : ℕ) = 0 + 1 from by ring,
      show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (r2_chain 1 (a + k) (0 + 2 * k) 0 2)
  -- state: (a+k, 2k+1, 0, 0, 2). R3 drain on b=2k+1.
  rw [show 0 + 2 * k + 1 = 0 + (2 * k + 1) from by ring]
  apply stepStar_trans (r3_drain (2 * k + 1) (a + k) 0 2)
  ring_nf; finish

-- Phase B, D = 3k+2: (a, 0, 0, 3k+2, 3) → (a + 3k + 2, 0, 0, 0, 6k + 7)
theorem phase_b_mod2 (k a : ℕ) :
    ⟨a, 0, 0, 3 * k + 2, 3⟩ [fm]⊢* ⟨a + 3 * k + 2, 0, 0, 0, 6 * k + 7⟩ := by
  rw [show 3 * k + 2 = 2 + 3 * k from by ring]
  apply stepStar_trans (r2r3_rounds k a 0 2)
  -- state: (a+k, 2k, 0, 2, 3). R2 fires twice (d=2>=1, e=3>=1).
  rw [show 0 + 2 * k = 0 + 2 * k from rfl,
      show (2 : ℕ) = 0 + 2 from by ring,
      show (3 : ℕ) = 1 + 2 from by ring]
  apply stepStar_trans (r2_chain 2 (a + k) (0 + 2 * k) 0 1)
  -- state: (a+k, 2k+2, 0, 0, 1). R3 drain on b=2k+2.
  rw [show 0 + 2 * k + 2 = 0 + (2 * k + 2) from by ring]
  apply stepStar_trans (r3_drain (2 * k + 2) (a + k) 0 1)
  ring_nf; finish

-- Phase B combined: (1, 0, 0, D, 3) → (D + 1, 0, 0, 0, 2*D + 3)
theorem phase_b (D : ℕ) :
    ⟨1, 0, 0, D, 3⟩ [fm]⊢* ⟨D + 1, 0, 0, 0, 2 * D + 3⟩ := by
  obtain ⟨j, rfl | rfl | rfl⟩ : ∃ j, D = 3 * j ∨ D = 3 * j + 1 ∨ D = 3 * j + 2 := ⟨D / 3, by omega⟩
  · have := phase_b_mod0 j 1
    rw [show 1 + 3 * j = 3 * j + 1 from by ring,
        show 6 * j + 3 = 2 * (3 * j) + 3 from by ring] at this
    exact this
  · have := phase_b_mod1 j 1
    rw [show 1 + 3 * j + 1 = 3 * j + 1 + 1 from by ring,
        show 6 * j + 5 = 2 * (3 * j + 1) + 3 from by ring] at this
    exact this
  · have := phase_b_mod2 j 1
    rw [show 1 + 3 * j + 2 = 3 * j + 2 + 1 from by ring,
        show 6 * j + 7 = 2 * (3 * j + 2) + 3 from by ring] at this
    exact this

-- Main transition: (1, 0, 0, d, 0) ⊢⁺ (1, 0, 0, 2d+2, 0)
theorem main_trans (d : ℕ) :
    ⟨1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨1, 0, 0, 2 * d + 2, 0⟩ := by
  -- Phase A: R5, R3
  step fm; step fm
  -- Phase B: (1, 0, 0, d+1, 3) → (d+2, 0, 0, 0, 2d+5)
  apply stepStar_trans (phase_b (d + 1))
  rw [show d + 1 + 1 = d + 2 from by ring,
      show 2 * (d + 1) + 3 = 1 + 2 * (d + 2) from by ring]
  -- Phase C: R4 drain (d+2, 0, 0, 0, 1+2*(d+2)) → (d+2, 0, d+2, 0, 1)
  apply stepStar_trans (r4_drain (d + 2) (d + 2) 0 1)
  rw [show 0 + (d + 2) = d + 2 from by ring,
      show d + 2 = (d + 1) + 1 from by ring]
  -- Phase D: opening 4 steps: R5, R1, R2, R1
  step fm; step fm; step fm; step fm
  -- State: (d+1, 0, d, 2, 0). Apply R5+R1 chain.
  have h := r5r1_chain d 1 0 2
  rw [show 1 + d = d + 1 from by ring, show 0 + d = d from by ring,
      show 2 + 2 * d = 2 * d + 2 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 2, 0⟩) (by execute fm 10)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨1, 0, 0, d, 0⟩) 2
  intro d; exact ⟨2 * d + 2, main_trans d⟩

end Sz22_2003_unofficial_1462
