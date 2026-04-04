import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1932: [9/70, 25/33, 22/5, 7/11, 33/2]

Vector representation:
```
-1  2 -1 -1  0
 0 -1  2  0 -1
 1  0 -1  0  1
 0  0  0  1 -1
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1932

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R4 repeated: move e to d.
theorem e_to_d : ∀ k, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

-- R3 repeated: move c to a and e.
theorem c_to_ae : ∀ k, ⟨a, 0, c + k, 0, e⟩ [fm]⊢* ⟨a + k, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 1) (e := e + 1))
    ring_nf; finish

-- R3R2 chain: each round R3 then R2.
theorem r3r2_chain : ∀ k, ⟨a, b + k, c + 1, 0, 0⟩ [fm]⊢* ⟨a + k, b, c + 1 + k, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing a b c
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show c + 1 + (k + 1) = (c + 1 + k) + 1 from by ring]
    step fm
    step fm
    rw [show c + 1 + 1 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih (a := a + 1) (c := c + 1))
    ring_nf; finish

-- Drain cycle: 4 steps R1,R1,R5,R2.
theorem drain_cycle : ⟨A + 3, B, 2, D + 3, 0⟩ [fm]⊢* ⟨A, B + 4, 2, D + 1, 0⟩ := by
  step fm; step fm; step fm; step fm; finish

-- Drain last: 2 steps R1,R1.
theorem drain_last : ⟨A + 2, B, 2, 2, 0⟩ [fm]⊢* ⟨A, B + 4, 0, 0, 0⟩ := by
  step fm; step fm; finish

-- Full drain by induction.
theorem drain_all : ∀ k, ⟨A + 3 * k + 2, B, 2, 2 * k + 2, 0⟩ [fm]⊢* ⟨A, B + 4 * k + 4, 0, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing A B
  · rw [show A + 3 * 0 + 2 = A + 2 from by ring,
        show 2 * 0 + 2 = 2 from by ring,
        show B + 4 * 0 + 4 = B + 4 from by ring]
    exact drain_last
  · rw [show A + 3 * (k + 1) + 2 = (A + 3) + 3 * k + 2 from by ring,
        show 2 * (k + 1) + 2 = (2 * k + 2) + 1 + 1 from by ring]
    rw [show (2 * k + 2) + 1 + 1 = (2 * k + 2) + 1 + 1 from rfl]
    rw [show (A + 3) + 3 * k + 2 = (A + 3 * k + 2) + 3 from by ring,
        show (2 * k + 2) + 1 + 1 = (2 * k + 1) + 3 from by ring]
    apply stepStar_trans drain_cycle
    apply stepStar_trans (ih (B := B + 4))
    ring_nf; finish

-- Growth opening: R5 then R2.
theorem growth_open : ⟨F + 1, B, 0, 0, 0⟩ [fm]⊢* ⟨F, B, 2, 0, 0⟩ := by
  step fm; step fm; finish

-- Combined growth phase.
theorem growth_phase : ∀ B, ⟨F + 1, B, 0, 0, 0⟩ [fm]⊢* ⟨F + 2 * B + 2, 0, 0, B + 2, 0⟩ := by
  intro B
  apply stepStar_trans growth_open
  have h1 : ⟨F, 0 + B, 1 + 1, 0, 0⟩ [fm]⊢* ⟨F + B, 0, 1 + 1 + B, 0, 0⟩ :=
    r3r2_chain B (a := F) (b := 0) (c := 1)
  simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  rw [show 1 + 1 + B = B + 2 from by ring]
  have h2 : ⟨F + B, 0, 0 + (B + 2), 0, 0⟩ [fm]⊢* ⟨F + B + (B + 2), 0, 0, 0, 0 + (B + 2)⟩ :=
    c_to_ae (B + 2) (a := F + B) (c := 0) (e := 0)
  simp only [Nat.zero_add] at h2
  apply stepStar_trans h2
  have h3 : ⟨F + B + (B + 2), 0, 0, 0, 0 + (B + 2)⟩ [fm]⊢* ⟨F + B + (B + 2), 0, 0, 0 + (B + 2), 0⟩ :=
    e_to_d (B + 2) (a := F + B + (B + 2)) (d := 0) (e := 0)
  simp only [Nat.zero_add] at h3
  apply stepStar_trans h3
  ring_nf; finish

-- Main transition.
theorem main_trans : ⟨F + 3 * G + 7, 0, 0, 2 * G + 4, 0⟩ [fm]⊢⁺ ⟨F + 8 * G + 18, 0, 0, 4 * G + 10, 0⟩ := by
  rw [show F + 3 * G + 7 = (F + 3 * G + 6) + 1 from by ring,
      show 2 * G + 4 = (2 * G + 3) + 1 from by ring]
  step fm
  step fm
  show ⟨F + 3 * G + 6, 0, 2, 2 * G + 4, 0⟩ [fm]⊢* ⟨F + 8 * G + 18, 0, 0, 4 * G + 10, 0⟩
  rw [show F + 3 * G + 6 = (F + 1) + 3 * (G + 1) + 2 from by ring,
      show 2 * G + 4 = 2 * (G + 1) + 2 from by ring]
  apply stepStar_trans (drain_all (G + 1) (A := F + 1) (B := 0))
  rw [show 0 + 4 * (G + 1) + 4 = 4 * G + 8 from by ring]
  apply stepStar_trans (growth_phase (F := F) (B := 4 * G + 8))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨7, 0, 0, 4, 0⟩) (by execute fm 26)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨F, G⟩ ↦ ⟨F + 3 * G + 7, 0, 0, 2 * G + 4, 0⟩) ⟨0, 0⟩
  intro ⟨F, G⟩
  refine ⟨⟨F + 2 * G + 2, 2 * G + 3⟩, ?_⟩
  show ⟨F + 3 * G + 7, 0, 0, 2 * G + 4, 0⟩ [fm]⊢⁺ ⟨(F + 2 * G + 2) + 3 * (2 * G + 3) + 7, 0, 0, 2 * (2 * G + 3) + 4, 0⟩
  rw [show (F + 2 * G + 2) + 3 * (2 * G + 3) + 7 = F + 8 * G + 18 from by ring,
      show 2 * (2 * G + 3) + 4 = 4 * G + 10 from by ring]
  exact main_trans

end Sz22_2003_unofficial_1932
