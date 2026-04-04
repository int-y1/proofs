import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1946: [9/70, 50/21, 11/5, 7/11, 15/2]

Vector representation:
```
-1  2 -1 -1  0
 1 -1  2 -1  0
 0  0 -1  0  1
 0  0  0  1 -1
-1  1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1946

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

theorem e_to_d : ∀ k d, ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · step fm
    apply stepStar_trans (ih (d + 1))
    ring_nf; finish

theorem c_to_e : ∀ k e, ⟨a, 0, k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro e
  · exists 0
  · step fm
    apply stepStar_trans (ih (e + 1))
    ring_nf; finish

theorem phase2_cycle : ∀ k a e, ⟨a, k, 2, 0, e⟩ [fm]⊢* ⟨a + k, 0, 2, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · step fm; step fm; step fm; step fm
    apply stepStar_trans (ih (a + 1) (e + 1))
    ring_nf; finish

theorem phase2_tail : ⟨a, b, 2, 0, e⟩ [fm]⊢* ⟨a + b, 0, 0, 0, e + b + 2⟩ := by
  apply stepStar_trans (phase2_cycle b a e)
  apply c_to_e 2 (e + b) (a := a + b)

theorem round3 : ⟨a + 2, b, 2, d + 3, 0⟩ [fm]⊢* ⟨a + 1, b + 3, 2, d, 0⟩ := by
  step fm; step fm; step fm
  ring_nf; finish

theorem rounds : ∀ k a b d, ⟨a + k + 1, b, 2, d + 3 * k, 0⟩ [fm]⊢*
    ⟨a + 1, b + 3 * k, 2, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show a + (k + 1) + 1 = (a + 1) + k + 1 from by ring,
        show d + 3 * (k + 1) = (d + 3) + 3 * k from by ring]
    apply stepStar_trans (ih (a + 1) b (d + 3))
    apply stepStar_trans (round3 (a := a) (b := b + 3 * k) (d := d))
    ring_nf; finish

theorem c1_to_c2 : ⟨a, b + 1, 1, 0, 0⟩ [fm]⊢⁺ ⟨a + 1, b, 2, 0, 0⟩ := by
  step fm; step fm; step fm; finish

theorem r2_sym (a b d : ℕ) : (a, b + 1, 0, d + 1, 0) [fm]⊢ (a + 1, b, 2, d, 0) := by
  simp only [fm]; rfl

theorem r1_sym (a b d : ℕ) : (a + 1, b, 2, d + 1, 0) [fm]⊢ (a, b + 2, 1, d, 0) := by
  simp only [fm]; rfl

-- d ≡ 2 mod 3: (f+k+2, 0, 0, 3k+2, 0) ->+ (f+3k+3, 0, 0, 3k+4, 0)
theorem trans_mod2 : ⟨f + k + 2, 0, 0, 3 * k + 2, 0⟩ [fm]⊢⁺
    ⟨f + 3 * k + 3, 0, 0, 3 * k + 4, 0⟩ := by
  -- R5
  step fm
  -- R1
  step fm
  -- R2 (symbolic a = f+k)
  apply stepStar_trans (step_stepStar (r2_sym (f + k) 2 (3 * k)))
  -- rounds
  have h := rounds k f 2 0
  rw [show 0 + 3 * k = 3 * k from by ring, show 2 + 3 * k = 3 * k + 2 from by ring] at h
  apply stepStar_trans h
  -- phase2_tail + c_to_e + e_to_d
  apply stepStar_trans (phase2_tail (a := f + 1) (b := 3 * k + 2) (e := 0))
  rw [show 0 + (3 * k + 2) + 2 = 3 * k + 4 from by ring]
  apply stepStar_trans (e_to_d (3 * k + 4) 0 (a := f + 1 + (3 * k + 2)))
  ring_nf; finish

-- d ≡ 0 mod 3: (f+k+2, 0, 0, 3k+3, 0) ->+ (f+3k+4, 0, 0, 3k+5, 0)
theorem trans_mod0 : ⟨f + k + 2, 0, 0, 3 * k + 3, 0⟩ [fm]⊢⁺
    ⟨f + 3 * k + 4, 0, 0, 3 * k + 5, 0⟩ := by
  -- R5
  step fm
  -- R1
  step fm
  -- R2 (symbolic a)
  apply stepStar_trans (step_stepStar (r2_sym (f + k) 2 (3 * k + 1)))
  -- rounds
  rw [show 3 * k + 1 = 1 + 3 * k from by ring]
  have h := rounds k f 2 1
  rw [show 2 + 3 * k = 3 * k + 2 from by ring] at h
  apply stepStar_trans h
  -- R1 (tail step: from (f+1, 3k+2, 2, 1, 0) -> (f, 3k+4, 1, 0, 0))
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (step_stepStar (r1_sym f (3 * k + 2) 0))
  rw [show 3 * k + 2 + 2 = 3 * k + 4 from by ring]
  -- c1_to_c2
  rw [show 3 * k + 4 = (3 * k + 3) + 1 from by ring]
  apply stepStar_trans (stepPlus_stepStar (c1_to_c2 (a := f) (b := 3 * k + 3)))
  -- phase2_tail + e_to_d
  apply stepStar_trans (phase2_tail (a := f + 1) (b := 3 * k + 3) (e := 0))
  rw [show 0 + (3 * k + 3) + 2 = 3 * k + 5 from by ring]
  apply stepStar_trans (e_to_d (3 * k + 5) 0 (a := f + 1 + (3 * k + 3)))
  ring_nf; finish

-- d ≡ 1 mod 3: (f+k+4, 0, 0, 3k+4, 0) ->+ (f+3k+7, 0, 0, 3k+8, 0)
theorem trans_mod1 : ⟨f + k + 4, 0, 0, 3 * k + 4, 0⟩ [fm]⊢⁺
    ⟨f + 3 * k + 7, 0, 0, 3 * k + 8, 0⟩ := by
  -- R5
  step fm
  -- R1
  step fm
  -- R2 (symbolic a)
  apply stepStar_trans (step_stepStar (r2_sym (f + k + 2) 2 (3 * k + 2)))
  -- rounds
  rw [show f + k + 2 + 1 = (f + 2) + k + 1 from by ring,
      show 3 * k + 2 = 2 + 3 * k from by ring]
  apply stepStar_trans (rounds k (f + 2) 2 2)
  rw [show 2 + 3 * k = 3 * k + 2 from by ring]
  -- R1, R1 (two tail steps)
  step fm; step fm
  -- R5
  step fm
  -- c1_to_c2
  rw [show 3 * k + 6 + 1 = (3 * k + 6) + 1 from by ring]
  apply stepStar_trans (stepPlus_stepStar (c1_to_c2 (a := f) (b := 3 * k + 6)))
  -- phase2_tail + e_to_d
  apply stepStar_trans (phase2_tail (a := f + 1) (b := 3 * k + 6) (e := 0))
  rw [show 0 + (3 * k + 6) + 2 = 3 * k + 8 from by ring]
  apply stepStar_trans (e_to_d (3 * k + 8) 0 (a := f + 1 + (3 * k + 6)))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨8, 0, 0, 8, 0⟩) (by execute fm 95)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ d ≥ 2 ∧ 3 * a ≥ 2 * d + 3)
  · intro c ⟨a, d, hq, hd, ha⟩; subst hq
    have hd3' : d % 3 = 0 ∨ d % 3 = 1 ∨ d % 3 = 2 := by omega
    rcases hd3' with h0 | h1 | h2
    · have hd3 : d ≥ 3 := by omega
      obtain ⟨k, rfl⟩ : ∃ k, d = 3 * k + 3 := ⟨d / 3 - 1, by omega⟩
      obtain ⟨f, rfl⟩ : ∃ f, a = f + k + 2 := ⟨a - k - 2, by omega⟩
      exact ⟨⟨f + 3 * k + 4, 0, 0, 3 * k + 5, 0⟩,
        ⟨f + 3 * k + 4, 3 * k + 5, rfl, by omega, by omega⟩, trans_mod0⟩
    · have hd4 : d ≥ 4 := by omega
      obtain ⟨k, rfl⟩ : ∃ k, d = 3 * k + 4 := ⟨(d - 4) / 3, by omega⟩
      obtain ⟨f, rfl⟩ : ∃ f, a = f + k + 4 := ⟨a - k - 4, by omega⟩
      exact ⟨⟨f + 3 * k + 7, 0, 0, 3 * k + 8, 0⟩,
        ⟨f + 3 * k + 7, 3 * k + 8, rfl, by omega, by omega⟩, trans_mod1⟩
    · obtain ⟨k, rfl⟩ : ∃ k, d = 3 * k + 2 := ⟨(d - 2) / 3, by omega⟩
      obtain ⟨f, rfl⟩ : ∃ f, a = f + k + 2 := ⟨a - k - 2, by omega⟩
      exact ⟨⟨f + 3 * k + 3, 0, 0, 3 * k + 4, 0⟩,
        ⟨f + 3 * k + 3, 3 * k + 4, rfl, by omega, by omega⟩, trans_mod2⟩
  · exact ⟨8, 8, rfl, by omega, by omega⟩
