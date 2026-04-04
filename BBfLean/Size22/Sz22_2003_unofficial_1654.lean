import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz22_2003_unofficial #1654: [77/15, 297/14, 2/3, 5/11, 21/2]

Vector representation:
```
 0 -1 -1  1  1
-1  3  0 -1  1
 1 -1  0  0  0
 0  0  1  0 -1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Canonical states: (c + F + 2, 0, c, 0, 0) with recurrence (c, F) -> (2c+1, F+1).
The transition decomposes into: R5+R1+R2 opening, R1x3+R2 chain (q rounds),
R1 remainder drain (0-2 steps based on c mod 3), R2+R3+R4 tail chains.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1654

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+3, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

theorem r1_drain : ∀ k, ∀ a b c d e,
    ⟨a, b + k, c + k, d, e⟩ [fm]⊢* ⟨a, b, c, d + k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b c d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by omega,
        show c + (k + 1) = (c + k) + 1 from by omega]
    step fm
    apply stepStar_trans (ih a b c (d + 1) (e + 1))
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a b e,
    ⟨a + k, b, 0, k, e⟩ [fm]⊢* ⟨a, b + 3 * k, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by omega,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih a (b + 3) (e + 1))
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ a e,
    ⟨a, k, 0, 0, e⟩ [fm]⊢* ⟨a + k, 0, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a + 1) e)
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ a c,
    ⟨a, 0, c, 0, k⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih a (c + 1))
    ring_nf; finish

theorem r1x3_r2_chain : ∀ k, ∀ a c d e,
    ⟨a + k, 3, c + 3 * k, d, e⟩ [fm]⊢* ⟨a, 3, c, d + 2 * k, e + 4 * k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by omega,
        show c + 3 * (k + 1) = (c + 3 * k + 2) + 1 from by omega]
    step fm
    rw [show c + 3 * k + 2 = (c + 3 * k + 1) + 1 from by omega]
    step fm
    rw [show c + 3 * k + 1 = (c + 3 * k) + 1 from by omega]
    step fm
    rw [show a + k + 1 = (a + k) + 1 from by omega,
        show d + 1 + 1 + 1 = (d + 2) + 1 from by omega]
    step fm
    apply stepStar_trans (ih a c (d + 2) (e + 4))
    ring_nf; finish

theorem opening (c F : ℕ) :
    ⟨c + F + 3, 0, c + 1, 0, 0⟩ [fm]⊢⁺ ⟨c + F + 1, 3, c, 1, 2⟩ := by
  rw [show c + F + 3 = (c + F + 2) + 1 from by omega]
  step fm; step fm
  rw [show c + F + 2 = (c + F + 1) + 1 from by omega]
  step fm; finish

theorem trans_c0 (F : ℕ) :
    ⟨F + 2, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨F + 4, 0, 1, 0, 0⟩ := by
  rw [show F + 2 = (F + 1) + 1 from by omega]
  step fm; step fm
  have h1 := r3_chain 4 F 1
  have h2 := r4_chain 1 (F + 4) 0
  simp at h2
  exact stepStar_trans h1 h2

theorem trans_r0 (q F : ℕ) :
    ⟨3 * q + F + 3, 0, 3 * q + 1, 0, 0⟩ [fm]⊢⁺
    ⟨6 * q + F + 6, 0, 6 * q + 3, 0, 0⟩ := by
  have hop := opening (3 * q) F
  have h1 := r1x3_r2_chain q (2 * q + F + 1) 0 1 2
  rw [show 2 * q + F + 1 + q = 3 * q + F + 1 from by ring,
      show 0 + 3 * q = 3 * q from by ring,
      show 1 + 2 * q = 2 * q + 1 from by ring,
      show 2 + 4 * q = 4 * q + 2 from by ring] at h1
  have h2 := r2_chain (2 * q + 1) F 3 (4 * q + 2)
  rw [show F + (2 * q + 1) = 2 * q + F + 1 from by ring,
      show 3 + 3 * (2 * q + 1) = 6 * q + 6 from by ring,
      show 4 * q + 2 + (2 * q + 1) = 6 * q + 3 from by ring] at h2
  have h3 := r3_chain (6 * q + 6) F (6 * q + 3)
  rw [show F + (6 * q + 6) = 6 * q + F + 6 from by ring] at h3
  have h4 := r4_chain (6 * q + 3) (6 * q + F + 6) 0
  simp at h4
  exact stepPlus_stepStar_stepPlus hop
    (stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 h4)))

theorem trans_r1 (q F : ℕ) :
    ⟨3 * q + F + 4, 0, 3 * q + 2, 0, 0⟩ [fm]⊢⁺
    ⟨6 * q + F + 8, 0, 6 * q + 5, 0, 0⟩ := by
  have hop := opening (3 * q + 1) F
  rw [show 3 * q + 1 + F + 3 = 3 * q + F + 4 from by ring,
      show 3 * q + 1 + 1 = 3 * q + 2 from by ring,
      show 3 * q + 1 + F + 1 = 3 * q + F + 2 from by ring] at hop
  have h1 := r1x3_r2_chain q (2 * q + F + 2) 1 1 2
  rw [show 2 * q + F + 2 + q = 3 * q + F + 2 from by ring,
      show 1 + 3 * q = 3 * q + 1 from by ring,
      show 1 + 2 * q = 2 * q + 1 from by ring,
      show 2 + 4 * q = 4 * q + 2 from by ring] at h1
  have h1b := r1_drain 1 (2 * q + F + 2) 2 0 (2 * q + 1) (4 * q + 2)
  rw [show 2 + 1 = 3 from by ring, show 0 + 1 = 1 from by ring,
      show 2 * q + 1 + 1 = 2 * q + 2 from by ring,
      show 4 * q + 2 + 1 = 4 * q + 3 from by ring] at h1b
  have h2 := r2_chain (2 * q + 2) F 2 (4 * q + 3)
  rw [show F + (2 * q + 2) = 2 * q + F + 2 from by ring,
      show 2 + 3 * (2 * q + 2) = 6 * q + 8 from by ring,
      show 4 * q + 3 + (2 * q + 2) = 6 * q + 5 from by ring] at h2
  have h3 := r3_chain (6 * q + 8) F (6 * q + 5)
  rw [show F + (6 * q + 8) = 6 * q + F + 8 from by ring] at h3
  have h4 := r4_chain (6 * q + 5) (6 * q + F + 8) 0
  simp at h4
  exact stepPlus_stepStar_stepPlus hop
    (stepStar_trans h1 (stepStar_trans h1b
      (stepStar_trans h2 (stepStar_trans h3 h4))))

theorem trans_r2 (q F : ℕ) :
    ⟨3 * q + F + 5, 0, 3 * q + 3, 0, 0⟩ [fm]⊢⁺
    ⟨6 * q + F + 10, 0, 6 * q + 7, 0, 0⟩ := by
  have hop := opening (3 * q + 2) F
  rw [show 3 * q + 2 + F + 3 = 3 * q + F + 5 from by ring,
      show 3 * q + 2 + 1 = 3 * q + 3 from by ring,
      show 3 * q + 2 + F + 1 = 3 * q + F + 3 from by ring] at hop
  have h1 := r1x3_r2_chain q (2 * q + F + 3) 2 1 2
  rw [show 2 * q + F + 3 + q = 3 * q + F + 3 from by ring,
      show 2 + 3 * q = 3 * q + 2 from by ring,
      show 1 + 2 * q = 2 * q + 1 from by ring,
      show 2 + 4 * q = 4 * q + 2 from by ring] at h1
  have h1b := r1_drain 2 (2 * q + F + 3) 1 0 (2 * q + 1) (4 * q + 2)
  rw [show 1 + 2 = 3 from by ring, show 0 + 2 = 2 from by ring,
      show 2 * q + 1 + 2 = 2 * q + 3 from by ring,
      show 4 * q + 2 + 2 = 4 * q + 4 from by ring] at h1b
  have h2 := r2_chain (2 * q + 3) F 1 (4 * q + 4)
  rw [show F + (2 * q + 3) = 2 * q + F + 3 from by ring,
      show 1 + 3 * (2 * q + 3) = 6 * q + 10 from by ring,
      show 4 * q + 4 + (2 * q + 3) = 6 * q + 7 from by ring] at h2
  have h3 := r3_chain (6 * q + 10) F (6 * q + 7)
  rw [show F + (6 * q + 10) = 6 * q + F + 10 from by ring] at h3
  have h4 := r4_chain (6 * q + 7) (6 * q + F + 10) 0
  simp at h4
  exact stepPlus_stepStar_stepPlus hop
    (stepStar_trans h1 (stepStar_trans h1b
      (stepStar_trans h2 (stepStar_trans h3 h4))))

theorem main_trans (c F : ℕ) :
    ⟨c + F + 2, 0, c, 0, 0⟩ [fm]⊢⁺ ⟨2 * c + F + 4, 0, 2 * c + 1, 0, 0⟩ := by
  rcases c with _ | c
  · simp; exact trans_c0 F
  · have h3 : c % 3 < 3 := Nat.mod_lt _ (by omega)
    obtain ⟨q, hq⟩ : ∃ q, c = 3 * q + c % 3 := ⟨c / 3, by omega⟩
    interval_cases (c % 3)
    · rw [Nat.add_zero] at hq; subst hq
      rw [show 3 * q + 1 + F + 2 = 3 * q + F + 3 from by ring,
          show 2 * (3 * q + 1) + F + 4 = 6 * q + F + 6 from by ring,
          show 2 * (3 * q + 1) + 1 = 6 * q + 3 from by ring]
      exact trans_r0 q F
    · subst hq
      rw [show 3 * q + 1 + 1 + F + 2 = 3 * q + F + 4 from by ring,
          show 2 * (3 * q + 1 + 1) + F + 4 = 6 * q + F + 8 from by ring,
          show 2 * (3 * q + 1 + 1) + 1 = 6 * q + 5 from by ring]
      exact trans_r1 q F
    · subst hq
      rw [show 3 * q + 2 + 1 + F + 2 = 3 * q + F + 5 from by ring,
          show 2 * (3 * q + 2 + 1) + F + 4 = 6 * q + F + 10 from by ring,
          show 2 * (3 * q + 2 + 1) + 1 = 6 * q + 7 from by ring]
      exact trans_r2 q F

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 1, 0, 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨c, F⟩ ↦ ⟨c + F + 2, 0, c, 0, 0⟩) ⟨1, 0⟩
  intro ⟨c, F⟩
  refine ⟨⟨2 * c + 1, F + 1⟩, ?_⟩
  show ⟨c + F + 2, 0, c, 0, 0⟩ [fm]⊢⁺ ⟨2 * c + 1 + (F + 1) + 2, 0, 2 * c + 1, 0, 0⟩
  rw [show 2 * c + 1 + (F + 1) + 2 = 2 * c + F + 4 from by ring]
  exact main_trans c F

end Sz22_2003_unofficial_1654
