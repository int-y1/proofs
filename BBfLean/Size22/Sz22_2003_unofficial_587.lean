import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #587: [35/6, 121/2, 100/77, 3/5, 7/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 2  0  2 -1 -1
 0  1 -1  0  0
 0  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_587

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

-- R4 repeated: convert c to b
theorem c_to_b : ∀ k, ∀ b, ⟨0, b, c + k, 0, e⟩ [fm]⊢* ⟨0, b + k, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih (b + 1))
  ring_nf; finish

-- R3+R2+R2 drain chain
theorem drain : ∀ k, ∀ C d e, ⟨0, 0, C, d + k, e + 1⟩ [fm]⊢* ⟨0, 0, C + 2 * k, d, e + 3 * k + 1⟩ := by
  intro k; induction' k with k ih <;> intro C d e
  · simp; exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm; step fm; step fm
  rw [show e + 2 + 2 = (e + 3) + 1 from by ring]
  apply stepStar_trans (ih (C + 2) d (e + 3))
  ring_nf; finish

-- Generalized interleaving + drain phase
theorem gen_phase : ∀ b, ∀ C D E, D ≥ 1 → 2 * E ≥ b + 1 →
    ⟨0, b, C, D, E⟩ [fm]⊢* ⟨0, 0, C + 3 * b + 2 * D, 0, E + b + 3 * D⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih; intro C D E hD hE
  rcases b with _ | _ | b
  · -- b = 0: drain D rounds
    obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
    obtain ⟨E', rfl⟩ : ∃ E', E = E' + 1 := ⟨E - 1, by omega⟩
    have h := drain (D' + 1) C 0 E'
    rw [show 0 + (D' + 1) = D' + 1 from by ring] at h
    refine stepStar_trans h ?_
    ring_nf; finish
  · -- b = 1: R3+R1+R2 then drain
    obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
    obtain ⟨E', rfl⟩ : ∃ E', E = E' + 1 := ⟨E - 1, by omega⟩
    show ⟨0, 1, C, D' + 1, E' + 1⟩ [fm]⊢* _
    step fm; step fm; step fm
    -- state: (0, 0, C+2+1, D'+1, E'+2)
    rw [show E' + 2 = (E' + 1) + 1 from by ring]
    have h := drain (D' + 1) (C + 2 + 1) 0 (E' + 1)
    rw [show 0 + (D' + 1) = D' + 1 from by ring] at h
    refine stepStar_trans h ?_
    ring_nf; finish
  · -- b + 2: R3+R1+R1 then IH
    obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
    obtain ⟨E', rfl⟩ : ∃ E', E = E' + 2 := ⟨E - 2, by omega⟩
    show ⟨0, b + 1 + 1, C, D' + 1, E' + 2⟩ [fm]⊢* _
    rw [show E' + 2 = (E' + 1) + 1 from by ring]
    step fm; step fm; step fm
    -- state: (0, b, C+2+1+1, D'+1+1, E'+1)
    have h := ih b (by omega) (C + 2 + 1 + 1) (D' + 1 + 1) (E' + 1) (by omega) (by omega)
    refine stepStar_trans h ?_
    ring_nf; finish

-- c=0: R5+R3+R2+R2
theorem case_c0 : ⟨0, 0, 0, 0, e + 2⟩ [fm]⊢⁺ ⟨0, 0, 2, 0, e + 4⟩ := by
  rw [show e + 2 = (e + 1) + 1 from by ring]
  step fm; step fm; step fm; step fm
  ring_nf; finish

-- c=1: R4+R5+R3+R1+R2+drain(1)
theorem case_c1 : ⟨0, 0, 1, 0, e + 3⟩ [fm]⊢⁺ ⟨0, 0, 5, 0, e + 6⟩ := by
  step fm
  rw [show e + 3 = (e + 2) + 1 from by ring]
  step fm
  rw [show e + 2 = (e + 1) + 1 from by ring]
  step fm; step fm; step fm
  -- state: (0, 0, 3, 1, e+2+1)
  rw [show e + 2 + 1 = (e + 2) + 1 from by ring]
  have h := drain 1 3 0 (e + 2)
  rw [show 0 + 1 = 1 from by ring] at h
  apply stepStar_trans h
  ring_nf; finish

-- c+2 case: c_to_b + opening + gen_phase
theorem case_c2 : 2 * e ≥ c + 6 →
    ⟨0, 0, c + 2, 0, e⟩ [fm]⊢⁺ ⟨0, 0, 3 * c + 8, 0, c + e + 4⟩ := by
  intro he
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 2 := ⟨e - 2, by omega⟩
  rw [show c + 2 = 0 + (c + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (c_to_b (c + 2) 0 (c := 0) (e := e' + 2))
  simp only [Nat.zero_add]
  rw [show e' + 2 = (e' + 1) + 1 from by ring]
  step fm
  step fm; step fm; step fm
  -- state: (0, c, 0+2+1+1, 1+1, e')
  -- Actually let me check: after R5 from (0, c+2, 0, 0, (e'+1)+1):
  -- R5: (0, c+2, 0, 1, e'+1). Then R3 (d+1=1, e+1=e'+1, so e'=e'): (2, c+2, 2, 0, e')
  -- R1 (a+1=2, b+1=c+2): (1, c+1, 3, 1, e'). R1: (0, c, 4, 2, e')
  -- But Lean sees: (0, c, 0+2+1+1, 1+1, e')
  have h := gen_phase c (0 + 2 + 1 + 1) (1 + 1) e' (by omega) (by omega)
  refine stepStar_trans h ?_
  ring_nf; finish

-- Main transition
theorem main_trans : 2 * e ≥ c + 4 →
    ⟨0, 0, c, 0, e⟩ [fm]⊢⁺ ⟨0, 0, 3 * c + 2, 0, c + e + 2⟩ := by
  intro he
  rcases c with _ | _ | c
  · -- c = 0
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 2 := ⟨e - 2, by omega⟩
    show ⟨0, 0, 0, 0, e' + 2⟩ [fm]⊢⁺ ⟨0, 0, 3 * 0 + 2, 0, 0 + (e' + 2) + 2⟩
    have h := case_c0 (e := e')
    refine stepPlus_stepStar_stepPlus h ?_
    ring_nf; finish
  · -- c = 1
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 3 := ⟨e - 3, by omega⟩
    show ⟨0, 0, 1, 0, e' + 3⟩ [fm]⊢⁺ ⟨0, 0, 3 * 1 + 2, 0, 1 + (e' + 3) + 2⟩
    have h := case_c1 (e := e')
    refine stepPlus_stepStar_stepPlus h ?_
    ring_nf; finish
  · -- c + 2
    show ⟨0, 0, c + 1 + 1, 0, e⟩ [fm]⊢⁺ ⟨0, 0, 3 * (c + 1 + 1) + 2, 0, c + 1 + 1 + e + 2⟩
    rw [show c + 1 + 1 = c + 2 from by ring]
    have h := case_c2 (c := c) (e := e) (by omega)
    refine stepPlus_stepStar_stepPlus h ?_
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 4⟩) (by execute fm 5)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c e, q = ⟨0, 0, c, 0, e⟩ ∧ 2 * e ≥ c + 4)
  · intro q ⟨c, e, hq, he⟩; subst hq
    exact ⟨⟨0, 0, 3 * c + 2, 0, c + e + 2⟩,
      ⟨3 * c + 2, c + e + 2, rfl, by omega⟩, main_trans he⟩
  · exact ⟨2, 4, rfl, by omega⟩
