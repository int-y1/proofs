import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #818: [35/6, 8/55, 11/2, 3/7, 70/11]

Vector representation:
```
-1 -1  1  1  0
 3  0 -1  0 -1
-1  0  0  0  1
 0  1  0 -1  0
 1  0  1  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_818

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d+1, e⟩
  | _ => none

-- R4 chain: move d to b (a=0, c=0)
theorem d_to_b : ∀ k b d, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (b + 1) d); ring_nf; finish

-- R3 chain: move a to e (b=0, c=0)
theorem a_to_e : ∀ k a e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih a (e + 1)); ring_nf; finish

-- R2 chain: drain c using e (b=0)
theorem r2_drain : ∀ k a e, ⟨a, 0, k, d, e + k⟩ [fm]⊢* ⟨a + 3 * k, 0, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (a + 3) e); ring_nf; finish

-- Core spiral by strong induction on b.
theorem core : ∀ b c d e, ⟨0, b, c + 1, d, c + 1 + b + e⟩ [fm]⊢*
    ⟨3 * c + 2 * b + 3, 0, 0, d + b, e⟩ := by
  intro b; induction' b using Nat.strongRecOn with b IH; intro c d e
  rcases b with _ | _ | _ | b
  · -- b = 0: R2 drain
    rw [show c + 1 + 0 + e = e + (c + 1) from by ring]
    apply stepStar_trans (r2_drain (c + 1) 0 e (d := d)); ring_nf; finish
  · -- b = 1: R2, R1, R2 drain
    rw [show c + 1 + 1 + e = (c + e) + 1 + 1 from by ring]
    step fm; step fm
    rw [show c + e + 1 = e + (c + 1) from by ring]
    apply stepStar_trans (r2_drain (c + 1) 2 e (d := d + 1)); ring_nf; finish
  · -- b = 2: R2, R1, R1, R2 drain
    rw [show c + 1 + 2 + e = (c + e + 2) + 1 from by ring]
    step fm  -- R2: (3, 2, c, d, c+e+2)
    step fm  -- R1: (2, 1, c+1, d+1, c+e+2)
    step fm  -- R1: (1, 0, c+2, d+2, c+e+2)
    rw [show c + e + 2 = e + (c + 2) from by ring]
    apply stepStar_trans (r2_drain (c + 2) 1 e (d := d + 2)); ring_nf; finish
  · -- b = b+3: R2, R1, R1, R1 then IH with b
    rw [show c + 1 + (b + 3) + e = (c + b + e + 3) + 1 from by ring]
    step fm  -- R2: (3, b+3, c, d, c+b+e+3)
    step fm  -- R1: (2, b+2, c+1, d+1, c+b+e+3)
    step fm  -- R1: (1, b+1, c+2, d+2, c+b+e+3)
    step fm  -- R1: (0, b, c+3, d+3, c+b+e+3)
    rw [show c + b + e + 3 = (c + 2) + 1 + b + e from by ring]
    apply stepStar_trans (IH b (by omega) (c + 2) (d + 3) e); ring_nf; finish

-- Middle phase: R5, R1, then core
theorem middle : ⟨0, d + 1, 0, 0, d + 3 + r⟩ [fm]⊢* ⟨2 * d + 6, 0, 0, d + 2, r⟩ := by
  rw [show d + 3 + r = (d + r + 2) + 1 from by ring]
  step fm  -- R5: (1, d+1, 1, 1, d+r+2)
  step fm  -- R1: (0, d, 2, 2, d+r+2)
  rw [show d + r + 2 = 1 + 1 + d + r from by ring]
  apply stepStar_trans (core d 1 2 r); ring_nf; finish

-- Main transition: compose d_to_b + middle + a_to_e
theorem main_trans : ⟨0, 0, 0, d + 1, d + 3 + r⟩ [fm]⊢⁺
    ⟨0, 0, 0, d + 2, 2 * d + 6 + r⟩ := by
  have h1 : ⟨0, 0, 0, d + 1, d + 3 + r⟩ [fm]⊢* ⟨0, d + 1, 0, 0, d + 3 + r⟩ := by
    rw [show (d + 1 : ℕ) = 0 + (d + 1) from by ring]
    exact d_to_b (d + 1) 0 0 (e := d + 3 + r)
  have h2 : ⟨0, d + 1, 0, 0, d + 3 + r⟩ [fm]⊢* ⟨2 * d + 6, 0, 0, d + 2, r⟩ :=
    middle
  have h3 : ⟨2 * d + 6, 0, 0, d + 2, r⟩ [fm]⊢* ⟨0, 0, 0, d + 2, 2 * d + 6 + r⟩ := by
    have := a_to_e (2 * d + 6) 0 r (d := d + 2)
    simp only [Nat.zero_add] at this
    rwa [show r + (2 * d + 6) = 2 * d + 6 + r from by ring] at this
  exact stepStar_stepPlus (stepStar_trans h1 (stepStar_trans h2 h3)) (by simp [Q])

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0 + 1, 0 + 3 + 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, r⟩ ↦ ⟨0, 0, 0, d + 1, d + 3 + r⟩) ⟨0, 0⟩
  intro ⟨d, r⟩
  refine ⟨⟨d + 1, r + d + 2⟩, ?_⟩
  show ⟨0, 0, 0, d + 1, d + 3 + r⟩ [fm]⊢⁺ ⟨0, 0, 0, (d + 1) + 1, (d + 1) + 3 + (r + d + 2)⟩
  rw [show (d + 1) + 1 = d + 2 from by ring,
      show (d + 1) + 3 + (r + d + 2) = 2 * d + 6 + r from by ring]
  exact main_trans

end Sz22_2003_unofficial_818
