import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz21_140_unofficial #132: [9/10, 77/2, 4/21, 5/7, 14/11]

Vector representation:
```
-1  2 -1  0  0
-1  0  0  1  1
 2 -1  0 -1  0
 0  0  1 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_132

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- Phase 1: d → c
theorem d_to_c : ∀ k, ∀ c d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih (c + 1) d e)
  ring_nf; finish

-- Phase 2: one round (0, B, C+3, 0, E+1) →* (0, B+5, C, 0, E)
theorem phase2_one_round :
    ⟨0, B, C + 3, 0, E + 1⟩ [fm]⊢* ⟨0, B + 5, C, 0, E⟩ := by
  rw [show C + 3 = (C + 1 + 1) + 1 from by ring]
  step fm
  rw [show (C + 1 + 1) + 1 = (C + 1) + 1 + 1 from by ring]
  step fm
  step fm
  rw [show (C + 1) + 1 = C + 1 + 1 from by ring]
  step fm
  step fm
  finish

-- Phase 2: k rounds
theorem phase2_rounds_v2 : ∀ k, ∀ B C E,
    ⟨0, B, C + 3 * k, 0, E + k⟩ [fm]⊢* ⟨0, B + 5 * k, C, 0, E⟩ := by
  intro k; induction' k with k ih <;> intro B C E
  · exists 0
  rw [show C + 3 * (k + 1) = (C + 3 * k) + 3 from by ring,
      show E + (k + 1) = (E + k) + 1 from by ring]
  apply stepStar_trans (phase2_one_round)
  apply stepStar_trans (ih (B + 5) C E)
  ring_nf; finish

-- Phase 2 tail c=1
theorem phase2_tail1 : ⟨0, B, 1, 0, E + 1⟩ [fm]⊢* ⟨2, B + 1, 0, 0, E⟩ := by
  step fm; step fm; step fm; finish

-- Phase 2 tail c=2
theorem phase2_tail2 : ⟨0, B, 2, 0, E + 1⟩ [fm]⊢* ⟨1, B + 3, 0, 0, E⟩ := by
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  step fm; step fm; step fm; step fm; finish

-- Phase 3: R3,R2,R2 chain
theorem r3r2r2_chain : ∀ k, ∀ B D E,
    ⟨0, B + k, 0, D + 1, E⟩ [fm]⊢* ⟨0, B, 0, D + 1 + k, E + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro B D E
  · exists 0
  rw [show B + (k + 1) = (B + k) + 1 from by ring]
  step fm; step fm; step fm
  rw [show D + 2 = (D + 1) + 1 from by ring]
  apply stepStar_trans (ih B (D + 1) (E + 2))
  ring_nf; finish

-- Phase 3 mod 0: (0, 5(k+1), 0, 0, E+1) ⊢⁺ (0, 0, 0, 5k+7, E+10k+11)
theorem phase3_mod0 (k E : ℕ) :
    ⟨0, 5 * (k + 1), 0, 0, E + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 5 * k + 7, E + 10 * k + 11⟩ := by
  rw [show 5 * (k + 1) = 5 * k + 5 from by ring]
  apply step_stepStar_stepPlus
    (show fm ⟨0, 5 * k + 5, 0, 0, E + 1⟩ = some ⟨1, 5 * k + 5, 0, 1, E⟩ by simp [fm])
  apply stepStar_trans (step_stepStar
    (show fm ⟨1, 5 * k + 5, 0, 1, E⟩ = some ⟨0, 5 * k + 5, 0, 2, E + 1⟩ by
      show fm ⟨0 + 1, 5 * k + 5, 0, 1, E⟩ = some ⟨0, 5 * k + 5, 0, 1 + 1, E + 1⟩
      simp [fm]))
  have h := r3r2r2_chain (5 * k + 5) 0 1 (E + 1)
  rw [show 0 + (5 * k + 5) = 5 * k + 5 from by ring,
      show 1 + 1 + (5 * k + 5) = 5 * k + 7 from by ring,
      show E + 1 + 2 * (5 * k + 5) = E + 10 * k + 11 from by ring] at h
  exact h

-- Phase 3 mod 1: (2, 5k+1, 0, 0, E) ⊢⁺ (0, 0, 0, 5k+3, E+10k+4)
theorem phase3_mod1 (k E : ℕ) :
    ⟨2, 5 * k + 1, 0, 0, E⟩ [fm]⊢⁺ ⟨0, 0, 0, 5 * k + 3, E + 10 * k + 4⟩ := by
  apply step_stepStar_stepPlus
    (show fm ⟨2, 5 * k + 1, 0, 0, E⟩ = some ⟨1, 5 * k + 1, 0, 1, E + 1⟩ by
      show fm ⟨1 + 1, 5 * k + 1, 0, 0, E⟩ = some ⟨1, 5 * k + 1, 0, 0 + 1, E + 1⟩
      simp [fm])
  apply stepStar_trans (step_stepStar
    (show fm ⟨1, 5 * k + 1, 0, 1, E + 1⟩ = some ⟨0, 5 * k + 1, 0, 2, E + 2⟩ by
      show fm ⟨0 + 1, 5 * k + 1, 0, 1, E + 1⟩ = some ⟨0, 5 * k + 1, 0, 1 + 1, E + 1 + 1⟩
      simp [fm]))
  have h := r3r2r2_chain (5 * k + 1) 0 1 (E + 2)
  rw [show 0 + (5 * k + 1) = 5 * k + 1 from by ring,
      show 1 + 1 + (5 * k + 1) = 5 * k + 3 from by ring,
      show E + 2 + 2 * (5 * k + 1) = E + 10 * k + 4 from by ring] at h
  exact h

-- Phase 3 mod 2: (1, 5k+3, 0, 0, E) ⊢⁺ (0, 0, 0, 5k+4, E+10k+7)
theorem phase3_mod2 (k E : ℕ) :
    ⟨1, 5 * k + 3, 0, 0, E⟩ [fm]⊢⁺ ⟨0, 0, 0, 5 * k + 4, E + 10 * k + 7⟩ := by
  apply step_stepStar_stepPlus
    (show fm ⟨1, 5 * k + 3, 0, 0, E⟩ = some ⟨0, 5 * k + 3, 0, 1, E + 1⟩ by
      show fm ⟨0 + 1, 5 * k + 3, 0, 0, E⟩ = some ⟨0, 5 * k + 3, 0, 0 + 1, E + 1⟩
      simp [fm])
  apply stepStar_trans (step_stepStar
    (show fm ⟨0, (5 * k + 2) + 1, 0, 0 + 1, E + 1⟩ = some ⟨0 + 2, 5 * k + 2, 0, 0, E + 1⟩ by
      simp [fm]))
  apply stepStar_trans (step_stepStar
    (show fm ⟨2, 5 * k + 2, 0, 0, E + 1⟩ = some ⟨1, 5 * k + 2, 0, 1, E + 2⟩ by
      show fm ⟨1 + 1, 5 * k + 2, 0, 0, E + 1⟩ = some ⟨1, 5 * k + 2, 0, 0 + 1, E + 1 + 1⟩
      simp [fm]))
  apply stepStar_trans (step_stepStar
    (show fm ⟨1, 5 * k + 2, 0, 1, E + 2⟩ = some ⟨0, 5 * k + 2, 0, 2, E + 3⟩ by
      show fm ⟨0 + 1, 5 * k + 2, 0, 1, E + 2⟩ = some ⟨0, 5 * k + 2, 0, 1 + 1, E + 2 + 1⟩
      simp [fm]))
  have h := r3r2r2_chain (5 * k + 2) 0 1 (E + 3)
  rw [show 0 + (5 * k + 2) = 5 * k + 2 from by ring,
      show 1 + 1 + (5 * k + 2) = 5 * k + 4 from by ring,
      show E + 3 + 2 * (5 * k + 2) = E + 10 * k + 7 from by ring] at h
  exact h

-- Full transition d ≡ 0 (mod 3): d = 3(k+1)
theorem full_trans_mod0 (k E : ℕ) :
    ⟨0, 0, 0, 3 * (k + 1), E + k + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 5 * k + 7, E + 10 * k + 11⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 3 * (k + 1), 0, E + k + 2⟩)
  · have h := d_to_c (3 * (k + 1)) 0 0 (E + k + 2)
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 5 * k + 5, 0, 0, E + 1⟩)
  · have h := phase2_rounds_v2 (k + 1) 0 0 (E + 1)
    rw [show 0 + 3 * (k + 1) = 3 * (k + 1) from by ring,
        show 0 + 5 * (k + 1) = 5 * k + 5 from by ring,
        show E + 1 + (k + 1) = E + k + 2 from by ring] at h
    exact h
  exact phase3_mod0 k E

-- Full transition d ≡ 1 (mod 3): d = 3k+1
theorem full_trans_mod1 (k E : ℕ) :
    ⟨0, 0, 0, 3 * k + 1, E + k + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 5 * k + 3, E + 10 * k + 4⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 3 * k + 1, 0, E + k + 1⟩)
  · have h := d_to_c (3 * k + 1) 0 0 (E + k + 1)
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 5 * k, 1, 0, E + 1⟩)
  · have h := phase2_rounds_v2 k 0 1 (E + 1)
    rw [show 1 + 3 * k = 3 * k + 1 from by ring,
        show 0 + 5 * k = 5 * k from by ring,
        show E + 1 + k = E + k + 1 from by ring] at h
    exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨2, 5 * k + 1, 0, 0, E⟩)
  · exact phase2_tail1
  exact phase3_mod1 k E

-- Full transition d ≡ 2 (mod 3): d = 3k+2
theorem full_trans_mod2 (k E : ℕ) :
    ⟨0, 0, 0, 3 * k + 2, E + k + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 5 * k + 4, E + 10 * k + 7⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 3 * k + 2, 0, E + k + 1⟩)
  · have h := d_to_c (3 * k + 2) 0 0 (E + k + 1)
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 5 * k, 2, 0, E + 1⟩)
  · have h := phase2_rounds_v2 k 0 2 (E + 1)
    rw [show 2 + 3 * k = 3 * k + 2 from by ring,
        show 0 + 5 * k = 5 * k from by ring,
        show E + 1 + k = E + k + 1 from by ring] at h
    exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨1, 5 * k + 3, 0, 0, E⟩)
  · exact phase2_tail2
  exact phase3_mod2 k E

-- Main transition with mod-3 dispatch
theorem main_trans (d e : ℕ) (he : e ≥ d + 1) :
    ∃ d' e', (⟨0, 0, 0, d + 1, e⟩ [fm]⊢⁺ ⟨0, 0, 0, d' + 1, e'⟩) ∧ e' ≥ d' + 1 := by
  have hmod : (d + 1) % 3 < 3 := Nat.mod_lt _ (by omega)
  have hdiv : d + 1 = 3 * ((d + 1) / 3) + (d + 1) % 3 := (Nat.div_add_mod (d + 1) 3).symm
  interval_cases ((d + 1) % 3)
  · -- d+1 ≡ 0 (mod 3)
    have hq1 : (d + 1) / 3 ≥ 1 := by omega
    have hd1 : d + 1 = 3 * ((d + 1) / 3) := by omega
    set q' := (d + 1) / 3 - 1
    have hq'eq : (d + 1) / 3 = q' + 1 := by omega
    have hd1' : d + 1 = 3 * (q' + 1) := by omega
    obtain ⟨E, rfl⟩ : ∃ E, e = E + q' + 2 := ⟨e - q' - 2, by omega⟩
    refine ⟨5 * q' + 6, E + 10 * q' + 11, ?_, ?_⟩
    · rw [show d + 1 = 3 * (q' + 1) from hd1',
          show 5 * q' + 6 + 1 = 5 * q' + 7 from by ring]
      exact full_trans_mod0 q' E
    · omega
  · -- d+1 ≡ 1 (mod 3)
    have hd1 : d + 1 = 3 * ((d + 1) / 3) + 1 := by omega
    set q := (d + 1) / 3
    obtain ⟨E, rfl⟩ : ∃ E, e = E + q + 1 := ⟨e - q - 1, by omega⟩
    refine ⟨5 * q + 2, E + 10 * q + 4, ?_, ?_⟩
    · rw [show d + 1 = 3 * q + 1 from hd1,
          show 5 * q + 2 + 1 = 5 * q + 3 from by ring]
      exact full_trans_mod1 q E
    · omega
  · -- d+1 ≡ 2 (mod 3)
    have hd1 : d + 1 = 3 * ((d + 1) / 3) + 2 := by omega
    set q := (d + 1) / 3
    obtain ⟨E, rfl⟩ : ∃ E, e = E + q + 1 := ⟨e - q - 1, by omega⟩
    refine ⟨5 * q + 3, E + 10 * q + 7, ?_, ?_⟩
    · rw [show d + 1 = 3 * q + 2 from hd1,
          show 5 * q + 3 + 1 = 5 * q + 4 from by ring]
      exact full_trans_mod2 q E
    · omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 1⟩) (by execute fm 1)
  apply progress_nonhalt
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d + 1, e⟩ ∧ e ≥ d + 1)
  · intro c ⟨d, e, hc, he⟩
    have ⟨d', e', htrans, he'⟩ := main_trans d e he
    exact ⟨⟨0, 0, 0, d' + 1, e'⟩, ⟨d', e', rfl, he'⟩, hc ▸ htrans⟩
  · exact ⟨0, 1, rfl, by omega⟩
