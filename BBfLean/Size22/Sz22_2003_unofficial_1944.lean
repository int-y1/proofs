import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1944: [9/70, 44/15, 25/2, 7/11, 3/5]

Vector representation:
```
-1  2 -1 -1  0
 2 -1 -1  0  1
-1  0  2  0  0
 0  0  0  1 -1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1944

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem a_to_c : ∀ k a c, ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + 2 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  rw [show a + (k + 1) = a + k + 1 from by ring]; step fm
  apply stepStar_trans (ih a (c + 2)); ring_nf; finish

theorem e_to_d : ∀ k d e, ⟨0, 0, c, d, e + k⟩ [fm]⊢* ⟨0, 0, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  rw [show e + (k + 1) = e + k + 1 from by ring]; step fm
  apply stepStar_trans (ih (d + 1) e); ring_nf; finish

theorem spiral : ∀ k b c d e, ⟨2, b, c + 3 * k, d + 2 * k, e⟩ [fm]⊢* ⟨2, b + 3 * k, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  rw [show c + 3 * (k + 1) = c + 3 * k + 1 + 1 + 1 from by ring,
      show d + 2 * (k + 1) = d + 2 * k + 1 + 1 from by ring]
  step fm; step fm
  rw [show b + 2 + 2 = b + 3 + 1 from by ring,
      show c + 3 * k + 1 = (c + 3 * k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih (b + 3) c d (e + 1)); ring_nf; finish

theorem r2_drain : ∀ k a b c e, ⟨a, b + k, c + k, 0, e⟩ [fm]⊢* ⟨a + 2 * k, b, c, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b c e
  · exists 0
  rw [show b + (k + 1) = b + k + 1 from by ring,
      show c + (k + 1) = c + k + 1 from by ring]
  step fm
  apply stepStar_trans (ih (a + 2) b c (e + 1)); ring_nf; finish

theorem tail_chain : ∀ k a e, ⟨a + 1, 2 * k, 0, 0, e⟩ [fm]⊢* ⟨a + 3 * k + 1, 0, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 from by ring]
  step fm
  rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih (a + 3) (e + 2)); ring_nf; finish

theorem tail_chain_odd : ∀ k a e, ⟨a + 1, 2 * k + 1, 0, 0, e⟩ [fm]⊢* ⟨a + 3 * k + 1, 1, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 from by ring]
  step fm
  rw [show 2 * k + 1 + 1 = (2 * k + 1) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih (a + 3) (e + 2)); ring_nf; finish

theorem main_trans (F G : ℕ) : ⟨3 * F + 2 * G + 2, 0, 0, 0, 2 * G + 2 * F + 1⟩ [fm]⊢⁺
    ⟨12 * F + 11 * G + 10, 0, 0, 0, 8 * F + 8 * G + 7⟩ := by
  -- First R3 step for ⊢⁺
  rw [show 3 * F + 2 * G + 2 = (3 * F + 2 * G + 1) + 1 from by ring]
  step fm
  -- R3 chain: remaining a steps
  rw [show 3 * F + 2 * G + 1 = 0 + (3 * F + 2 * G + 1) from by ring]
  apply stepStar_trans (a_to_c (3 * F + 2 * G + 1) 0 2)
  -- R4 chain
  rw [show 2 + 2 * (3 * F + 2 * G + 1) = 6 * F + 4 * G + 4 from by ring,
      show 2 * G + 2 * F + 1 = 0 + (2 * G + 2 * F + 1) from by ring]
  apply stepStar_trans (e_to_d (2 * G + 2 * F + 1) 0 0)
  -- R5 + R2 + first spiral + R1
  rw [show 0 + (2 * G + 2 * F + 1) = 2 * G + 2 * F + 1 from by ring,
      show 6 * F + 4 * G + 4 = (6 * F + 4 * G + 3) + 1 from by ring,
      show 2 * G + 2 * F + 1 = (2 * G + 2 * F) + 1 from by ring]
  step fm; step fm
  rw [show 6 * F + 4 * G + 2 = (3 * F + G + 2) + 3 * (G + F) from by ring,
      show 2 * G + 2 * F + 1 = 1 + 2 * (G + F) from by ring]
  apply stepStar_trans (spiral (G + F) 0 (3 * F + G + 2) 1 1)
  rw [show 0 + 3 * (G + F) = 3 * (G + F) from by ring,
      show 1 + (G + F) = G + F + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring,
      show 3 * F + G + 2 = (3 * F + G + 1) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  -- R2 drain
  apply stepStar_trans
    (show ⟨1, 3 * (G + F) + 2, 3 * F + G + 1, 0, G + F + 1⟩ [fm]⊢*
      ⟨6 * F + 2 * G + 3, 2 * G + 1, 0, 0, 4 * F + 2 * G + 2⟩ from by
      have := r2_drain (3 * F + G + 1) 1 (2 * G + 1) 0 (G + F + 1)
      convert this using 1; ring_nf)
  -- Tail chain G rounds (odd b = 2G+1)
  apply stepStar_trans
    (show ⟨6 * F + 2 * G + 3, 2 * G + 1, 0, 0, 4 * F + 2 * G + 2⟩ [fm]⊢*
      ⟨6 * F + 5 * G + 3, 1, 0, 0, 4 * F + 4 * G + 2⟩ from by
      have := tail_chain_odd G (6 * F + 2 * G + 2) (4 * F + 2 * G + 2)
      convert this using 1; ring_nf)
  -- R3 + R2 + R3 (from the B=1 tail)
  rw [show 6 * F + 5 * G + 3 = (6 * F + 5 * G + 2) + 1 from by ring]
  step fm
  rw [show 6 * F + 5 * G + 2 = (6 * F + 5 * G + 1) + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  rw [show 6 * F + 5 * G + 1 + 1 + 2 = (6 * F + 5 * G + 3) + 1 from by ring,
      show 4 * F + 4 * G + 2 + 1 = 4 * F + 4 * G + 3 from by ring]
  step fm
  -- R3 chain
  rw [show 6 * F + 5 * G + 3 = 0 + (6 * F + 5 * G + 3) from by ring]
  apply stepStar_trans (a_to_c (6 * F + 5 * G + 3) 0 3)
  -- R4 chain
  rw [show 3 + 2 * (6 * F + 5 * G + 3) = 12 * F + 10 * G + 9 from by ring,
      show 4 * F + 4 * G + 3 = 0 + (4 * F + 4 * G + 3) from by ring]
  apply stepStar_trans (e_to_d (4 * F + 4 * G + 3) 0 0)
  -- R5 + R2 + second spiral + R1
  rw [show 0 + (4 * F + 4 * G + 3) = 4 * F + 4 * G + 3 from by ring,
      show 12 * F + 10 * G + 9 = (12 * F + 10 * G + 8) + 1 from by ring,
      show 4 * F + 4 * G + 3 = (4 * F + 4 * G + 2) + 1 from by ring]
  step fm; step fm
  rw [show 12 * F + 10 * G + 7 = (6 * F + 4 * G + 4) + 3 * (2 * F + 2 * G + 1) from by ring,
      show 4 * F + 4 * G + 3 = 1 + 2 * (2 * F + 2 * G + 1) from by ring]
  apply stepStar_trans (spiral (2 * F + 2 * G + 1) 0 (6 * F + 4 * G + 4) 1 1)
  rw [show 0 + 3 * (2 * F + 2 * G + 1) = 3 * (2 * F + 2 * G + 1) from by ring,
      show 1 + (2 * F + 2 * G + 1) = 2 * F + 2 * G + 2 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring,
      show 6 * F + 4 * G + 4 = (6 * F + 4 * G + 3) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  -- R2 drain
  apply stepStar_trans
    (show ⟨1, 3 * (2 * F + 2 * G + 1) + 2, 6 * F + 4 * G + 3, 0, 2 * F + 2 * G + 2⟩ [fm]⊢*
      ⟨12 * F + 8 * G + 7, 2 * G + 2, 0, 0, 8 * F + 6 * G + 5⟩ from by
      have := r2_drain (6 * F + 4 * G + 3) 1 (2 * G + 2) 0 (2 * F + 2 * G + 2)
      convert this using 1; ring_nf)
  -- Tail chain G+1 rounds
  apply stepStar_trans
    (show ⟨12 * F + 8 * G + 7, 2 * G + 2, 0, 0, 8 * F + 6 * G + 5⟩ [fm]⊢*
      ⟨12 * F + 11 * G + 10, 0, 0, 0, 8 * F + 8 * G + 7⟩ from by
      have := tail_chain (G + 1) (12 * F + 8 * G + 6) (8 * F + 6 * G + 5)
      convert this using 1; ring_nf)
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨F, G⟩ ↦ ⟨3 * F + 2 * G + 2, 0, 0, 0, 2 * G + 2 * F + 1⟩) ⟨0, 0⟩
  intro ⟨F, G⟩
  refine ⟨⟨4 * F + 3 * G + 2, G + 1⟩, ?_⟩
  show ⟨3 * F + 2 * G + 2, 0, 0, 0, 2 * G + 2 * F + 1⟩ [fm]⊢⁺
    ⟨3 * (4 * F + 3 * G + 2) + 2 * (G + 1) + 2, 0, 0, 0, 2 * (G + 1) + 2 * (4 * F + 3 * G + 2) + 1⟩
  rw [show 3 * (4 * F + 3 * G + 2) + 2 * (G + 1) + 2 = 12 * F + 11 * G + 10 from by ring,
      show 2 * (G + 1) + 2 * (4 * F + 3 * G + 2) + 1 = 8 * F + 8 * G + 7 from by ring]
  exact main_trans F G

end Sz22_2003_unofficial_1944
