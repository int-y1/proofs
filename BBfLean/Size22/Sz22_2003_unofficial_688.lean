import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #688: [35/6, 4/55, 11/2, 3/7, 28/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  0  1
 0  1  0 -1  0
 2  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_688

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | _ => none

-- R3 chain: move a to e (b=0, c=0).
theorem a_to_e : ∀ k, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a) (d := d) (e := e + 1))
    ring_nf; finish

-- R4 chain: move d to b (a=0, c=0).
theorem d_to_b : ∀ k, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1) (d := d) (e := e))
    ring_nf; finish

-- R2 chain: consume c and e equally (b=0).
theorem r2_chain : ∀ k, ⟨a, 0, k, d, k⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, 0⟩ := by
  intro k; induction' k with k ih generalizing a d
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a := a + 2) (d := d))
    ring_nf; finish

-- Interleave: (2, b, c, d, b+c) →* (b+2c+2, 0, 0, d+b, 0).
theorem interleave : ∀ b, ∀ c d, ⟨2, b, c, d, b + c⟩ [fm]⊢* ⟨b + 2 * c + 2, 0, 0, d + b, 0⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih; intro c d
  rcases b with _ | _ | b
  · -- b = 0
    simp only [Nat.zero_add, Nat.add_zero]
    have := r2_chain c (a := 2) (d := d)
    rw [show 2 + 2 * c = 2 * c + 2 from by ring] at this
    exact this
  · -- b = 1
    rw [show 1 + c = c + 1 from by ring]
    step fm
    have h := r2_chain (c + 1) (a := 1) (d := d + 1)
    rw [show 1 + 2 * (c + 1) = 1 + 2 * c + 2 from by ring] at h
    convert h using 2
  · -- b = b' + 2
    rw [show b + 2 + c = (b + c) + 1 + 1 from by ring]
    step fm  -- R1
    step fm  -- R1
    step fm  -- R2
    rw [show b + c + 1 = b + (c + 1) from by ring]
    apply stepStar_trans (ih b (by omega) (c + 1) (d + 2))
    ring_nf; finish

-- Main transition: (n+2, 0, 0, n+1, 0) →⁺ (n+3, 0, 0, n+2, 0).
theorem main_trans : ⟨n + 2, 0, 0, n + 1, 0⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, n + 2, 0⟩ := by
  -- Phase 1: R3 chain
  have h1 : ⟨n + 2, 0, 0, n + 1, 0⟩ [fm]⊢* ⟨0, 0, 0, n + 1, n + 2⟩ := by
    have := a_to_e (n + 2) (a := 0) (d := n + 1) (e := 0)
    simp at this; exact this
  -- Phase 2: R4 chain
  have h2 : ⟨0, 0, 0, n + 1, n + 2⟩ [fm]⊢* ⟨0, n + 1, 0, 0, n + 2⟩ := by
    have := d_to_b (n + 1) (b := 0) (d := 0) (e := n + 2)
    simp at this; exact this
  -- Phase 3: R5 step
  have h3 : ⟨0, n + 1, 0, 0, n + 2⟩ [fm]⊢ ⟨2, n + 1, 0, 1, n + 1⟩ := by
    rw [show n + 2 = (n + 1) + 1 from by ring]
    simp [fm]
  -- Phase 4: Interleave
  have h4 : ⟨2, n + 1, 0, 1, n + 1⟩ [fm]⊢* ⟨n + 3, 0, 0, n + 2, 0⟩ := by
    rw [show n + 1 = (n + 1) + 0 from by ring]
    have := interleave (n + 1) 0 1
    simp only [Nat.add_zero] at this
    rw [show (n + 1) + 2 * 0 + 2 = n + 3 from by ring,
        show 1 + (n + 1) = n + 2 from by ring] at this
    exact this
  -- Compose
  exact stepStar_stepPlus_stepPlus h1
    (stepStar_stepPlus_stepPlus h2
      (step_stepStar_stepPlus h3 h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, n + 1, 0⟩) 0
  intro n; exact ⟨n + 1, main_trans⟩

end Sz22_2003_unofficial_688
