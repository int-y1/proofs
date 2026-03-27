import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #129: [1/45, 1078/15, 3/7, 275/2, 7/11]

Vector representation:
```
 0 -2 -1  0  0
 1 -1 -1  2  1
 0  1  0 -1  0
-1  0  2  0  1
 0  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_129

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+2, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

-- R4 chain: (a+j, 0, c, 0, e) ->* (a, 0, c+2j, 0, e+j)
theorem r4_chain : ∀ j, ∀ a c e,
    ⟨a+j, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+2*j, 0, e+j⟩ := by
  intro j; induction' j with j ih <;> intro a c e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R3 drain: (a, b, 0, d+j, e) ->* (a, b+j, 0, d, e)
theorem r3_drain : ∀ j, ∀ a b d e,
    ⟨a, b, 0, d+j, e⟩ [fm]⊢* ⟨a, b+j, 0, d, e⟩ := by
  intro j; induction' j with j ih <;> intro a b d e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (ih a (b+1) d e)
  ring_nf; finish

-- Phase A core: (a, 0, j+1, d+1, e) ->* (a+j+1, 0, 0, d+j+2, e+j+1)
theorem phase_a_core : ∀ j, ∀ a d e,
    ⟨a, 0, j+1, d+1, e⟩ [fm]⊢* ⟨a+j+1, 0, 0, d+j+2, e+j+1⟩ := by
  intro j; induction' j with j ih <;> intro a d e
  · step fm; step fm; ring_nf; finish
  rw [show (j + 1) + 1 = (j + 1) + 1 from rfl]
  step fm; step fm
  rw [show d + 2 = (d + 1) + 1 from by ring]
  apply stepStar_trans (ih (a+1) (d+1) (e+1))
  ring_nf; finish

-- Phase A: (0, 0, c+2, 0, e+1) ->* (c+2, c+3, 0, 0, e+c+2)
theorem phase_a (c e : ℕ) :
    ⟨0, 0, c+2, 0, e+1⟩ [fm]⊢* ⟨c+2, c+3, 0, 0, e+c+2⟩ := by
  step fm; step fm
  rw [show c + 2 = (c + 1) + 1 from by ring]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  apply stepStar_trans (phase_a_core c 1 1 (e+1))
  -- (1+c+1, 0, 0, 1+c+2, e+1+c+1)
  have h := r3_drain (1+c+2) (1+c+1) 0 0 (e+1+c+1)
  simp only [Nat.zero_add] at h
  apply stepStar_trans h
  ring_nf; finish

-- b4_iter: (a+j, b+4j, 0, 0, e) ->* (a, b, 0, 0, e+j)
theorem b4_iter : ∀ j, ∀ a b e,
    ⟨a+j, b+4*j, 0, 0, e⟩ [fm]⊢* ⟨a, b, 0, 0, e+j⟩ := by
  intro j; induction' j with j ih <;> intro a b e
  · exists 0
  rw [show a + (j + 1) = (a + j) + 1 from by ring,
      show b + 4 * (j + 1) = (b + 4 * j) + 4 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- b3_step: (a+1, 3, 0, 0, e) ->* (a+1, 2, 0, 0, e+2)
theorem b3_step (a e : ℕ) :
    ⟨a+1, 3, 0, 0, e⟩ [fm]⊢* ⟨a+1, 2, 0, 0, e+2⟩ := by
  step fm; step fm; step fm; step fm; step fm; ring_nf; finish

-- b1_step: (a+1, 1, 0, 0, e) ->* (a+2, 3, 0, 0, e+3)
theorem b1_step (a e : ℕ) :
    ⟨a+1, 1, 0, 0, e⟩ [fm]⊢* ⟨a+2, 3, 0, 0, e+3⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; ring_nf; finish

-- b2_finish: (a+2, 2, 0, 0, e) ->⁺ (0, 0, 2a+3, 0, e+a+2)
theorem b2_finish (a e : ℕ) :
    ⟨a+2, 2, 0, 0, e⟩ [fm]⊢⁺ ⟨0, 0, 2*a+3, 0, e+a+2⟩ := by
  step fm; step fm; step fm
  -- After R4, R1, R4, now at (a, 0, 3, 0, e') where e' should be e+2
  -- r4_chain a: (a, 0, 3, 0, e+2) ->* (0, 0, 2a+3, 0, e+a+2)
  have h := r4_chain a 0 3 (e+2)
  simp only [Nat.zero_add] at h
  rw [show 3 + 2 * a = 2 * a + 3 from by ring,
      show (e + 2) + a = e + a + 2 from by ring] at h
  apply stepStar_trans h
  ring_nf; finish

-- Main transition Case r2: C = 4q+2
theorem main_trans_r2 (q e : ℕ) :
    ⟨0, 0, 4*q+2, 0, e+1⟩ [fm]⊢⁺ ⟨0, 0, 6*q+3, 0, e+8*q+6⟩ := by
  apply stepStar_stepPlus_stepPlus
  · have h := phase_a (4*q) e
    rw [show e + (4 * q) + 2 = e + 4 * q + 2 from by ring] at h; exact h
  apply stepStar_stepPlus_stepPlus
  · have h := b4_iter q (3*q+2) 3 (e+4*q+2)
    rw [show (3 * q + 2) + q = 4 * q + 2 from by ring,
        show 3 + 4 * q = 4 * q + 3 from by ring,
        show (e + 4 * q + 2) + q = e + 5 * q + 2 from by ring] at h; exact h
  apply stepStar_stepPlus_stepPlus
  · have h := b3_step (3*q+1) (e+5*q+2)
    rw [show (3 * q + 1) + 1 = 3 * q + 2 from by ring] at h; exact h
  have h := b2_finish (3*q) (e+5*q+4)
  rw [show 2 * (3 * q) + 3 = 6 * q + 3 from by ring,
      show (e + 5 * q + 4) + 3 * q + 2 = e + 8 * q + 6 from by ring] at h; exact h

-- Main transition Case r3: C = 4q+3
theorem main_trans_r3 (q e : ℕ) :
    ⟨0, 0, 4*q+3, 0, e+1⟩ [fm]⊢⁺ ⟨0, 0, 6*q+4, 0, e+8*q+6⟩ := by
  apply stepStar_stepPlus_stepPlus
  · have h := phase_a (4*q+1) e
    rw [show 4 * q + 1 + 2 = 4 * q + 3 from by ring,
        show e + (4 * q + 1) + 2 = e + 4 * q + 3 from by ring] at h; exact h
  apply stepStar_stepPlus_stepPlus
  · have h := b4_iter (q+1) (3*q+2) 0 (e+4*q+3)
    rw [show (3 * q + 2) + (q + 1) = 4 * q + 3 from by ring,
        show 0 + 4 * (q + 1) = 4 * q + 4 from by ring,
        show (e + 4 * q + 3) + (q + 1) = e + 5 * q + 4 from by ring] at h; exact h
  -- (3q+2, 0, 0, 0, e+5q+4): R4 step then r4_chain
  step fm
  -- now at (3q+1, 0, 2, 0, e+5q+5)
  have h := r4_chain (3*q+1) 0 2 (e+5*q+5)
  simp only [Nat.zero_add] at h
  rw [show 2 + 2 * (3 * q + 1) = 6 * q + 4 from by ring,
      show (e + 5 * q + 5) + (3 * q + 1) = e + 8 * q + 6 from by ring] at h
  apply stepStar_trans h
  ring_nf; finish

-- Main transition Case r0: C = 4(q+1)
theorem main_trans_r0 (q e : ℕ) :
    ⟨0, 0, 4*(q+1), 0, e+1⟩ [fm]⊢⁺ ⟨0, 0, 6*q+7, 0, e+8*q+14⟩ := by
  apply stepStar_stepPlus_stepPlus
  · have h := phase_a (4*q+2) e
    rw [show 4 * q + 2 + 2 = 4 * (q + 1) from by ring,
        show e + (4 * q + 2) + 2 = e + 4 * q + 4 from by ring] at h; exact h
  apply stepStar_stepPlus_stepPlus
  · have h := b4_iter (q+1) (3*q+3) 1 (e+4*q+4)
    rw [show (3 * q + 3) + (q + 1) = 4 * (q + 1) from by ring,
        show 1 + 4 * (q + 1) = 4 * q + 5 from by ring,
        show (e + 4 * q + 4) + (q + 1) = e + 5 * q + 5 from by ring] at h; exact h
  apply stepStar_stepPlus_stepPlus
  · have h := b1_step (3*q+2) (e+5*q+5)
    rw [show (3 * q + 2) + 1 = 3 * q + 3 from by ring,
        show (3 * q + 2) + 2 = 3 * q + 4 from by ring,
        show (e + 5 * q + 5) + 3 = e + 5 * q + 8 from by ring] at h; exact h
  apply stepStar_stepPlus_stepPlus
  · have h := b3_step (3*q+3) (e+5*q+8)
    rw [show (3 * q + 3) + 1 = 3 * q + 4 from by ring] at h; exact h
  have h := b2_finish (3*q+2) (e+5*q+10)
  rw [show 2 * (3 * q + 2) + 3 = 6 * q + 7 from by ring,
      show (e + 5 * q + 10) + (3 * q + 2) + 2 = e + 8 * q + 14 from by ring] at h; exact h

-- Main transition Case r1: C = 4(q+1)+1
theorem main_trans_r1 (q e : ℕ) :
    ⟨0, 0, 4*(q+1)+1, 0, e+1⟩ [fm]⊢⁺ ⟨0, 0, 6*q+7, 0, e+8*q+10⟩ := by
  apply stepStar_stepPlus_stepPlus
  · have h := phase_a (4*q+3) e
    rw [show 4 * q + 3 + 2 = 4 * (q + 1) + 1 from by ring,
        show e + (4 * q + 3) + 2 = e + 4 * q + 5 from by ring] at h; exact h
  apply stepStar_stepPlus_stepPlus
  · have h := b4_iter (q+1) (3*q+4) 2 (e+4*q+5)
    rw [show (3 * q + 4) + (q + 1) = 4 * (q + 1) + 1 from by ring,
        show 2 + 4 * (q + 1) = 4 * q + 6 from by ring,
        show (e + 4 * q + 5) + (q + 1) = e + 5 * q + 6 from by ring] at h; exact h
  have h := b2_finish (3*q+2) (e+5*q+6)
  rw [show 2 * (3 * q + 2) + 3 = 6 * q + 7 from by ring,
      show (e + 5 * q + 6) + (3 * q + 2) + 2 = e + 8 * q + 10 from by ring] at h; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (fun state ↦ ∃ C E, state = (⟨0, 0, C+2, 0, E+1⟩ : Q))
  · intro state ⟨C, E, hstate⟩
    subst hstate
    rcases Nat.even_or_odd C with ⟨k, hk⟩ | ⟨k, hk⟩
    · rcases Nat.even_or_odd k with ⟨q, hq⟩ | ⟨q, hq⟩
      · -- C = 4q, C+2 = 4q+2
        refine ⟨⟨0, 0, 6*q+3, 0, E+8*q+6⟩, ⟨6*q+1, E+8*q+5, by ring_nf⟩, ?_⟩
        have hC : C + 2 = 4 * q + 2 := by omega
        rw [hC]; exact main_trans_r2 q E
      · -- C = 4q+2, C+2 = 4(q+1)
        refine ⟨⟨0, 0, 6*q+7, 0, E+8*q+14⟩, ⟨6*q+5, E+8*q+13, by ring_nf⟩, ?_⟩
        have hC : C + 2 = 4 * (q + 1) := by omega
        rw [hC]; exact main_trans_r0 q E
    · rcases Nat.even_or_odd k with ⟨q, hq⟩ | ⟨q, hq⟩
      · -- C = 4q+1, C+2 = 4q+3
        refine ⟨⟨0, 0, 6*q+4, 0, E+8*q+6⟩, ⟨6*q+2, E+8*q+5, by ring_nf⟩, ?_⟩
        have hC : C + 2 = 4 * q + 3 := by omega
        rw [hC]; exact main_trans_r3 q E
      · -- C = 4q+3, C+2 = 4(q+1)+1
        refine ⟨⟨0, 0, 6*q+7, 0, E+8*q+10⟩, ⟨6*q+5, E+8*q+9, by ring_nf⟩, ?_⟩
        have hC : C + 2 = 4 * (q + 1) + 1 := by omega
        rw [hC]; exact main_trans_r1 q E
  · exact ⟨0, 0, rfl⟩

end Sz22_2003_unofficial_129
