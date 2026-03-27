import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #504: [28/15, 3/22, 35/2, 11/49, 33/7]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -1
-1  0  1  1  0
 0  0  0 -2  1
 0  1  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_504

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c, d+2, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R3 chain: convert a to c and d
theorem a_to_cd : ∀ k, ∀ a c d, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+k, d+k, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R4 chain: convert d to e (by 2s)
theorem d_to_e : ∀ k, ∀ c d e, ⟨0, 0, c, d+2*k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [Nat.mul_succ, ← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R2R1 chain: interleaved consumption of c and e
theorem r2r1_chain : ∀ k, ∀ a d e, ⟨a+1, 0, k, d, e+k⟩ [fm]⊢* ⟨a+k+1, 0, 0, d+k, e⟩ := by
  intro k; induction' k with k h <;> intro a d e
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R2 drain: convert a and e to b
theorem r2_drain : ∀ k, ∀ a b d, ⟨a+k, b, 0, d, k⟩ [fm]⊢* ⟨a, b+k, 0, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a b d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R3R1 chain: interleaved conversion of b to a and d
theorem r3r1_chain : ∀ k, ∀ a b d, ⟨a+1, b+k, 0, d, 0⟩ [fm]⊢* ⟨a+k+1, b, 0, d+2*k, 0⟩ := by
  intro k; induction' k with k h <;> intro a b d
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Main transition: C(N) ⊢⁺ C(N+1) where C(N) = (N+2, 0, 0, 3*N+3, 0)
theorem main_trans (N : ℕ) :
    ⟨N+2, 0, 0, 3*N+3, (0 : ℕ)⟩ [fm]⊢⁺ ⟨N+3, 0, 0, 3*N+6, (0 : ℕ)⟩ := by
  -- Phase 1: R3 x (N+2): →* (0, 0, N+2, 4N+5, 0)
  rw [show (N : ℕ)+2 = 0+(N+2) from by ring]
  apply stepStar_stepPlus_stepPlus (a_to_cd (N+2) 0 0 (3*N+3))
  -- Phase 2: R4 x (2N+2): →* (0, 0, N+2, 1, 2N+2)
  rw [show (0 : ℕ)+(N+2) = N+2 from by ring,
      show (3*N+3)+(N+2) = 1+2*(2*N+2) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_e (2*N+2) (N+2) 1 0)
  -- Phase 3: R5: → (0, 1, N+2, 0, 2N+3)
  rw [show (0 : ℕ)+(2*N+2) = 2*N+2 from by ring]
  apply step_stepStar_stepPlus
    (show ⟨0, 0, N+2, 0+1, 2*N+2⟩ [fm]⊢ ⟨0, 0+1, N+2, 0, (2*N+2)+1⟩ from by unfold fm; rfl)
  -- Phase 4: R1 + R2R1 chain: →* (N+3, 0, 0, N+2, N+2)
  rw [show (0 : ℕ)+1 = 1 from by ring, show (2*N+2)+1 = (N+2)+(N+1) from by ring,
      show (N : ℕ)+2 = (N+1)+1 from by ring]
  apply stepStar_trans
    (step_stepStar (show ⟨0, 0+1, (N+1)+1, 0, (N+2)+(N+1)⟩ [fm]⊢
      ⟨0+2, 0, N+1, 0+1, (N+2)+(N+1)⟩ from by unfold fm; rfl))
  rw [show (0 : ℕ)+2 = 1+1 from by ring, show (0 : ℕ)+1 = 1 from by ring]
  apply stepStar_trans (r2r1_chain (N+1) 1 1 (N+2))
  -- Phase 5: R2 drain: →* (1, N+2, 0, N+2, 0)
  rw [show (1 : ℕ)+(N+1)+1 = 1+(N+2) from by ring,
      show (1 : ℕ)+(N+1) = N+2 from by ring]
  apply stepStar_trans (r2_drain (N+2) 1 0 (N+2))
  -- Phase 6: R3: → (0, N+2, 1, N+3, 0)
  rw [show (0 : ℕ)+(N+2) = N+2 from by ring]
  apply stepStar_trans
    (step_stepStar (show ⟨0+1, N+2, 0, N+2, 0⟩ [fm]⊢ ⟨0, N+2, 0+1, (N+2)+1, 0⟩ from by
      unfold fm; rfl))
  -- Phase 7: R1 + R3R1 chain: →* (N+3, 0, 0, 3N+6, 0)
  rw [show (0 : ℕ)+1 = 1 from by ring, show (N+2)+1 = N+3 from by ring,
      show (N : ℕ)+2 = (N+1)+1 from by ring]
  apply stepStar_trans
    (step_stepStar (show ⟨0, (N+1)+1, 1, N+3, 0⟩ [fm]⊢ ⟨0+2, N+1, 0, (N+3)+1, 0⟩ from by
      rw [show (1 : ℕ) = 0+1 from by ring]; unfold fm; rfl))
  rw [show (0 : ℕ)+2 = 1+1 from by ring, show (N+3)+1 = N+4 from by ring,
      show (N : ℕ)+1 = 0+(N+1) from by ring]
  apply stepStar_trans (r3r1_chain (N+1) 1 0 (N+4))
  rw [show (1 : ℕ)+(N+1)+1 = N+3 from by ring,
      show (N+4)+2*(N+1) = 3*N+6 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 3, 0⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun N ↦ ⟨N+2, 0, 0, 3*N+3, 0⟩) 0
  intro N; exists N+1; exact main_trans N

end Sz22_2003_unofficial_504
