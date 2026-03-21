import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #102: [7/15, 27/77, 22/3, 5/11, 33/2]

Vector representation:
```
 0 -1 -1  1  0
 0  3  0 -1 -1
 1 -1  0  0  1
 0  0  1  0 -1
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_102

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R3 chain: b → a,e
theorem r3_chain : ∀ k, ∀ a b e, ⟨a, b+k, 0, 0, e⟩ [fm]⊢* ⟨a+k, b, 0, 0, e+k⟩ := by
  intro k; induction k with
  | zero => intro a b e; exists 0
  | succ k ih =>
    intro a b e
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R4 chain: e → c
theorem r4_chain : ∀ k, ∀ a c, ⟨a, 0, c, 0, k⟩ [fm]⊢* ⟨a, 0, c+k, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a c; exists 0
  | succ k ih =>
    intro a c
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- One round: 6 steps draining c by 4
theorem round6 : ∀ a c d, ⟨a+1, 0, c+4, d, 0⟩ [fm]⊢* ⟨a, 0, c, d+3, 0⟩ := by
  intro a c d
  step fm
  rw [show c + 4 = (c + 3) + 1 from by ring]
  step fm; step fm
  rw [show c + 3 = (c + 2) + 1 from by ring]
  step fm
  rw [show c + 2 = (c + 1) + 1 from by ring]
  step fm; step fm
  ring_nf; finish

-- Phase A: k rounds
theorem phaseA : ∀ k, ∀ a c d, ⟨a+k, 0, c+4*k, d, 0⟩ [fm]⊢* ⟨a, 0, c, d+3*k, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d; simp; exists 0
  | succ k ih =>
    intro a c d
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 4 * (k + 1) = (c + 4 * k) + 4 from by ring]
    apply stepStar_trans (round6 (a+k) (c+4*k) d)
    apply stepStar_trans (ih a c (d+3))
    ring_nf; finish

-- Tail for c=2
theorem tail2 : ∀ a d, ⟨a+1, 0, 2, d, 0⟩ [fm]⊢* ⟨a+1, 4, 0, d, 0⟩ := by
  intro a d
  step fm; step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

-- Phase B chain: R3+R2 pairs
theorem phaseBchain : ∀ k, ∀ a b, ⟨a, b+1, 0, k, 0⟩ [fm]⊢* ⟨a+k, b+1+2*k, 0, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a b; simp; exists 0
  | succ k ih =>
    intro a b
    step fm
    rw [show k + 1 = k + 1 from rfl]
    step fm
    rw [show b + 3 = (b + 2) + 1 from by ring]
    apply stepStar_trans (ih (a+1) (b+2))
    ring_nf; finish

-- R3 then R4
theorem r3r4 : ∀ b, ∀ a, ⟨a, b, 0, 0, 0⟩ [fm]⊢* ⟨a+b, 0, b, 0, 0⟩ := by
  intro b a
  apply stepStar_trans (c₂ := ⟨a+b, 0, 0, 0, b⟩)
  · have h := r3_chain b a 0 0
    simp only [Nat.zero_add] at h; exact h
  · have h := r4_chain b (a+b) 0
    simp only [Nat.zero_add] at h; exact h

-- R3 then R4 (plus version)
theorem r3r4_plus : ∀ b, ∀ a, ⟨a, b+1, 0, 0, 0⟩ [fm]⊢⁺ ⟨a+b+1, 0, b+1, 0, 0⟩ := by
  intro b a
  have h := r3r4 (b+1) a
  rw [show a + (b + 1) = a + b + 1 from by ring] at h
  exact stepStar_stepPlus h (by simp [Q])

-- Phase B: (a+1, 0, 0, d+1, 0) →* (a+d, 2*d+4, 0, 0, 0)
theorem phaseB : ∀ a d, ⟨a+1, 0, 0, d+1, 0⟩ [fm]⊢* ⟨a+d, 2*d+4, 0, 0, 0⟩ := by
  intro a d
  step fm; step fm
  rw [show (4 : ℕ) = 3 + 1 from by ring]
  apply stepStar_trans (phaseBchain d a 3)
  ring_nf; finish

-- Phase B from 4
theorem phaseBfrom4 : ∀ a d, ⟨a, 4, 0, d, 0⟩ [fm]⊢* ⟨a+d, 2*d+4, 0, 0, 0⟩ := by
  intro a d
  rw [show (4 : ℕ) = 3 + 1 from by ring]
  apply stepStar_trans (phaseBchain d a 3)
  ring_nf; finish

-- Full transition for c = 4*(k+1)
theorem trans_4k : ∀ k, ∀ a,
    ⟨a+k+2, 0, 4*(k+1), 0, 0⟩ [fm]⊢⁺ ⟨a+9*k+10, 0, 6*k+8, 0, 0⟩ := by
  intro k a
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+1, 0, 0, 3*k+3, 0⟩)
  · have h := phaseA (k+1) (a+1) 0 0
    rw [show a + 1 + (k + 1) = a + k + 2 from by ring,
        show 0 + 4 * (k + 1) = 4 * (k + 1) from by ring,
        show 0 + 3 * (k + 1) = 3 * k + 3 from by ring] at h
    exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+3*k+2, 6*k+8, 0, 0, 0⟩)
  · have h := phaseB a (3*k+2)
    rw [show (3 * k + 2) + 1 = 3 * k + 3 from by ring,
        show a + (3 * k + 2) = a + 3 * k + 2 from by ring,
        show 2 * (3 * k + 2) + 4 = 6 * k + 8 from by ring] at h
    exact h
  have h := r3r4_plus (6*k+7) (a+3*k+2)
  rw [show (6 * k + 7) + 1 = 6 * k + 8 from by ring,
      show a + 3 * k + 2 + (6 * k + 7) + 1 = a + 9 * k + 10 from by ring] at h
  exact h

-- Full transition for c = 4*k+2
theorem trans_4k2 : ∀ k, ∀ a,
    ⟨a+k+1, 0, 4*k+2, 0, 0⟩ [fm]⊢⁺ ⟨a+9*k+5, 0, 6*k+4, 0, 0⟩ := by
  intro k a
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+1, 0, 2, 3*k, 0⟩)
  · have h := phaseA k (a+1) 2 0
    rw [show a + 1 + k = a + k + 1 from by ring,
        show 2 + 4 * k = 4 * k + 2 from by ring,
        show 0 + 3 * k = 3 * k from by ring] at h
    exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+1, 4, 0, 3*k, 0⟩)
  · exact tail2 a (3*k)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+3*k+1, 6*k+4, 0, 0, 0⟩)
  · have h := phaseBfrom4 (a+1) (3*k)
    rw [show a + 1 + 3 * k = a + 3 * k + 1 from by ring,
        show 2 * (3 * k) + 4 = 6 * k + 4 from by ring] at h
    exact h
  have h := r3r4_plus (6*k+3) (a+3*k+1)
  rw [show (6 * k + 3) + 1 = 6 * k + 4 from by ring,
      show a + 3 * k + 1 + (6 * k + 3) + 1 = a + 9 * k + 5 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 4, 0, 0⟩) (by execute fm 18)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ A c, q = ⟨A, 0, c, 0, 0⟩ ∧ c % 2 = 0 ∧ c ≥ 2 ∧ A ≥ c + 1)
  · intro q ⟨A, c, hq, heven, hc2, hAc⟩; subst hq
    obtain ⟨m, rfl⟩ : ∃ m, c = 2 * m := ⟨c / 2, by omega⟩
    rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
    · subst hj
      have hj1 : j ≥ 1 := by omega
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      obtain ⟨a, rfl⟩ : ∃ a, A = a + j' + 2 := ⟨A - j' - 2, by omega⟩
      refine ⟨⟨a + 9*j' + 10, 0, 6*j' + 8, 0, 0⟩,
              ⟨a + 9*j' + 10, 6*j' + 8, rfl, ?_, ?_, ?_⟩, ?_⟩
      · omega
      · omega
      · omega
      · convert trans_4k j' a using 1; ring_nf
    · subst hj
      obtain ⟨a, rfl⟩ : ∃ a, A = a + j + 1 := ⟨A - j - 1, by omega⟩
      refine ⟨⟨a + 9*j + 5, 0, 6*j + 4, 0, 0⟩,
              ⟨a + 9*j + 5, 6*j + 4, rfl, ?_, ?_, ?_⟩, ?_⟩
      · omega
      · omega
      · omega
      · convert trans_4k2 j a using 1; ring_nf
  · exact ⟨5, 4, rfl, by omega, by omega, by omega⟩

end Sz21_140_unofficial_102
