import BBfLean.FM

/-!
# sz22_2003_unofficial #592: [35/6, 121/2, 28/55, 3/7, 35/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 2  0 -1  1 -1
 0  1  0 -1  0
 0  0  1  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_592

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

-- R4 chain: transfer d to b
theorem d_to_b : ∀ k b, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro b
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by omega]
  step fm
  apply stepStar_trans (h _)
  rw [show b + 1 + k = b + (k + 1) from by omega]
  finish

-- R3,R2,R2 chain: drain c with a=0, b=0
theorem r3r2r2_chain : ∀ k, ∀ c d f, ⟨0, 0, c+k, d, f+k⟩ [fm]⊢* ⟨0, 0, c, d+k, f+4*k⟩ := by
  intro k; induction' k with k h <;> intro c d f
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by omega,
      show f + (k + 1) = (f + k) + 1 from by omega]
  step fm; step fm; step fm
  rw [show f + k + 2 + 2 = (f + 4) + k from by omega]
  apply stepStar_trans (h c (d + 1) (f + 4))
  rw [show d + 1 + k = d + (k + 1) from by omega,
      show f + 4 + 4 * k = f + 4 * (k + 1) from by omega]
  finish

-- R1,R1,R3 chain: interleaved phase
theorem r1r1r3_chain :
    ∀ k, ∀ c d g, ⟨2, 2+2*k, c, d, g+k⟩ [fm]⊢* ⟨2, 2, c+k, d+3*k, g⟩ := by
  intro k; induction' k with k h <;> intro c d g
  · exists 0
  rw [show 2 + 2 * (k + 1) = (2 + 2 * k) + 2 from by omega,
      show g + (k + 1) = (g + k) + 1 from by omega]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _)
  rw [show c + 1 + k = c + (k + 1) from by omega,
      show d + 1 + 1 + 1 + 3 * k = d + 3 * (k + 1) from by omega]
  finish

-- R5+R3 opening
theorem r5_r3 : ⟨0, b, 0, 0, e+1+1⟩ [fm]⊢⁺ ⟨2, b, 0, 2, e⟩ := by
  step fm; step fm; finish

-- R1+R1 close
theorem r1_r1_close : ⟨2, 2, c, d, e⟩ [fm]⊢⁺ ⟨0, 0, c+1+1, d+1+1, e⟩ := by
  step fm; step fm; finish

-- Full transition: (0,0,0,2n+2,2n+4) →⁺ (0,0,0,4n+6,4n+8)
theorem full_trans : ⟨0, 0, 0, 2*n+2, 2*n+4⟩ [fm]⊢⁺ ⟨0, 0, 0, 4*n+6, 4*n+8⟩ := by
  -- Phase 1: R4 chain
  rw [show 2*n+2 = 0 + (2*n+2) from by omega]
  apply stepStar_stepPlus_stepPlus (d_to_b (d := 0) (e := 2*n+4) (2*n+2) 0)
  rw [show (0 : ℕ) + (2*n+2) = 2*n+2 from by omega]
  -- Phase 2: R5+R3
  rw [show (2*n+4 : ℕ) = 2*n+2+1+1 from by omega]
  apply stepPlus_stepStar_stepPlus (r5_r3 (b := 2*n+2) (e := 2*n+2))
  -- State: (2, 2*n+2, 0, 2, 2*n+2)
  -- Phase 3: R1,R1,R3 chain: n rounds
  have phase3 : (⟨2, 2*n+2, 0, 2, 2*n+2⟩ : Q) [fm]⊢* ⟨2, 2, n, 3*n+2, n+2⟩ := by
    have heq : (⟨2, 2*n+2, 0, 2, 2*n+2⟩ : Q) = ⟨2, 2+2*n, 0, 2, (n+2)+n⟩ := by
      ext <;> simp +arith
    rw [heq]
    have h := r1r1r3_chain n 0 2 (n+2)
    rw [show 0+n = n from by omega, show 2+3*n = 3*n+2 from by omega] at h
    exact h
  apply stepStar_trans phase3
  -- State: (2, 2, n, 3*n+2, n+2)
  -- Phase 4: R1+R1 close
  apply stepStar_trans (stepPlus_stepStar (r1_r1_close (c := n) (d := 3*n+2) (e := n+2)))
  -- State: (0, 0, n+1+1, 3*n+2+1+1, n+2)
  -- Phase 5: R3,R2,R2 chain
  have phase5 : (⟨0, 0, n+1+1, 3*n+2+1+1, n+2⟩ : Q) [fm]⊢* ⟨0, 0, 0, 4*n+6, 4*n+8⟩ := by
    have heq : (⟨0, 0, n+1+1, 3*n+2+1+1, n+2⟩ : Q) = ⟨0, 0, 0+(n+2), 3*n+4, 0+(n+2)⟩ := by
      ext <;> simp +arith
    rw [heq]
    have h := r3r2r2_chain (n+2) 0 (3*n+4) 0
    rw [show 3*n+4+(n+2) = 4*n+6 from by omega,
        show 0+4*(n+2) = 4*n+8 from by omega] at h
    exact h
  exact phase5

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 4⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 2*n+2, 2*n+4⟩) 0
  intro n; exact ⟨2*n+2, by
    have h := @full_trans n
    rw [show 2*(2*n+2)+2 = 4*n+6 from by omega,
        show 2*(2*n+2)+4 = 4*n+8 from by omega]
    exact h⟩

end Sz22_2003_unofficial_592
