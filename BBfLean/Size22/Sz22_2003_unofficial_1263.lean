import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1263: [5/6, 8/35, 77/2, 3/7, 98/11]

Vector representation:
```
-1 -1  1  0  0
 3  0 -1 -1  0
-1  0  0  1  1
 0  1  0 -1  0
 1  0  0  2 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1263

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+2, e⟩
  | _ => none

theorem d_to_b : ∀ k b d e, ⟨(0 : ℕ), b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (b + 1) d e); ring_nf; finish

theorem a_drain : ∀ k a d e, ⟨a + k, (0 : ℕ), 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih a (d + 1) (e + 1)); ring_nf; finish

theorem r3r2_drain : ∀ k a e, ⟨a + 1, (0 : ℕ), k, 0, e⟩ [fm]⊢* ⟨a + 2 * k + 1, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm; step fm; apply stepStar_trans (ih (a + 2) (e + 1)); ring_nf; finish

-- 10-step reduction for d >= 7
theorem middle_reduce : ∀ d c e,
    ⟨(3 : ℕ), d + 7, c, 1, e + 1⟩ [fm]⊢* ⟨3, d, c + 5, 1, e⟩ := by
  intro d c e
  step fm; step fm; step fm; step fm; step fm; step fm; step fm
  step fm; step fm; step fm; finish

theorem base_d0 : ∀ c e,
    ⟨(3 : ℕ), 0, c, 1, e⟩ [fm]⊢* ⟨0, 0, 0, 2 * c + 4, e + 3 * c + 3⟩ := by
  intro c; induction' c with c ih <;> intro e
  · step fm; step fm; step fm; finish
  · step fm
    rw [show (6 : ℕ) = 5 + 1 from by ring]
    apply stepStar_trans (r3r2_drain c 5 e)
    rw [show 5 + 2 * c + 1 = 0 + (2 * c + 6) from by ring]
    apply stepStar_trans (a_drain (2 * c + 6) 0 0 (e + c))
    ring_nf; finish

theorem base_d1 : ∀ c e,
    ⟨(3 : ℕ), 1, c, 1, e⟩ [fm]⊢* ⟨0, 0, 0, 2 * c + 5, e + 3 * c + 5⟩ := by
  intro c e
  step fm; step fm
  rw [show (5 : ℕ) = 4 + 1 from by ring]
  apply stepStar_trans (r3r2_drain c 4 e)
  rw [show 4 + 2 * c + 1 = 0 + (2 * c + 5) from by ring]
  apply stepStar_trans (a_drain (2 * c + 5) 0 0 (e + c))
  ring_nf; finish

theorem base_d2 : ∀ c e,
    ⟨(3 : ℕ), 2, c, 1, e⟩ [fm]⊢* ⟨0, 0, 0, 2 * c + 6, e + 3 * c + 7⟩ := by
  intro c e
  step fm; step fm; step fm
  rw [show (4 : ℕ) = 3 + 1 from by ring, show c + 1 = c + 1 from rfl]
  apply stepStar_trans (r3r2_drain (c + 1) 3 e)
  rw [show 3 + 2 * (c + 1) + 1 = 0 + (2 * c + 6) from by ring]
  apply stepStar_trans (a_drain (2 * c + 6) 0 0 (e + (c + 1)))
  ring_nf; finish

theorem base_d3 : ∀ c e,
    ⟨(3 : ℕ), 3, c, 1, e⟩ [fm]⊢* ⟨0, 0, 0, 2 * c + 7, e + 3 * c + 9⟩ := by
  intro c e
  step fm; step fm; step fm; step fm
  rw [show (3 : ℕ) = 2 + 1 from by ring, show c + 2 = c + 2 from rfl]
  apply stepStar_trans (r3r2_drain (c + 2) 2 e)
  rw [show 2 + 2 * (c + 2) + 1 = 0 + (2 * c + 7) from by ring]
  apply stepStar_trans (a_drain (2 * c + 7) 0 0 (e + (c + 2)))
  ring_nf; finish

theorem base_d4 : ∀ c e,
    ⟨(3 : ℕ), 4, c, 1, e⟩ [fm]⊢* ⟨0, 0, 0, 2 * c + 8, e + 3 * c + 11⟩ := by
  intro c e
  step fm; step fm; step fm; step fm; step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring, show c + 3 = c + 3 from rfl]
  apply stepStar_trans (r3r2_drain (c + 3) 1 e)
  rw [show 1 + 2 * (c + 3) + 1 = 0 + (2 * c + 8) from by ring]
  apply stepStar_trans (a_drain (2 * c + 8) 0 0 (e + (c + 3)))
  ring_nf; finish

theorem base_d5 : ∀ c e,
    ⟨(3 : ℕ), 5, c, 1, e⟩ [fm]⊢* ⟨0, 0, 0, 2 * c + 9, e + 3 * c + 13⟩ := by
  intro c e
  step fm; step fm; step fm; step fm; step fm; step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring, show c + 4 = c + 4 from rfl]
  apply stepStar_trans (r3r2_drain (c + 4) 0 e)
  rw [show 0 + 2 * (c + 4) + 1 = 0 + (2 * c + 9) from by ring]
  apply stepStar_trans (a_drain (2 * c + 9) 0 0 (e + (c + 4)))
  ring_nf; finish

theorem base_d6 : ∀ c e,
    ⟨(3 : ℕ), 6, c, 1, e + 1⟩ [fm]⊢* ⟨0, 0, 0, 2 * c + 13, e + 3 * c + 16⟩ := by
  intro c e
  -- R1x3: (0, 3, c+3, 1, e+1)
  step fm; step fm; step fm
  -- R2: (3, 3, c+2, 0, e+1)
  step fm
  -- R1x3: (0, 0, c+5, 0, e+1)
  step fm; step fm; step fm
  -- R5: (1, 0, c+5, 2, e)
  step fm
  -- R2: (4, 0, c+4, 1, e)
  step fm
  -- R2: (7, 0, c+3, 0, e)
  step fm
  rw [show (7 : ℕ) = 6 + 1 from by ring, show c + 3 = c + 3 from rfl]
  apply stepStar_trans (r3r2_drain (c + 3) 6 e)
  rw [show 6 + 2 * (c + 3) + 1 = 0 + (2 * c + 13) from by ring]
  apply stepStar_trans (a_drain (2 * c + 13) 0 0 (e + (c + 3)))
  ring_nf; finish

theorem middle_trans : ∀ d, ∀ c e, 7 * e ≥ d →
    ∃ d' e', ⟨(3 : ℕ), d, c, 1, e⟩ [fm]⊢* ⟨0, 0, 0, d' + 1, e' + 2⟩ ∧ 7 * e' ≥ d' := by
  intro d; induction' d using Nat.strongRecOn with d ih
  intro c e hd
  rcases d with _ | _ | _ | _ | _ | _ | _ | d
  · exact ⟨2 * c + 3, e + 3 * c + 1, base_d0 c e, by omega⟩
  · exact ⟨2 * c + 4, e + 3 * c + 3, base_d1 c e, by omega⟩
  · exact ⟨2 * c + 5, e + 3 * c + 5, base_d2 c e, by omega⟩
  · exact ⟨2 * c + 6, e + 3 * c + 7, base_d3 c e, by omega⟩
  · exact ⟨2 * c + 7, e + 3 * c + 9, base_d4 c e, by omega⟩
  · exact ⟨2 * c + 8, e + 3 * c + 11, base_d5 c e, by omega⟩
  · -- d = 6, need e >= 1
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    exact ⟨2 * c + 12, e' + 3 * c + 14, base_d6 c e', by omega⟩
  · -- d + 7, inductive step
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    have h_reduce := middle_reduce d c e'
    have ⟨d', e'', h_rest, h_inv⟩ := ih d (by omega) (c + 5) e' (by omega)
    exact ⟨d', e'', stepStar_trans h_reduce h_rest, h_inv⟩

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 4, 3⟩) (by execute fm 8)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d + 1, e + 2⟩ ∧ 7 * e ≥ d)
  · intro c ⟨d, e, hq, hd⟩; subst hq
    -- R4 first step for ⊢⁺
    have h_first : (⟨0, 0, 0, d + 1, e + 2⟩ : Q) [fm]⊢ ⟨0, 1, 0, d, e + 2⟩ := by
      simp [fm]
    -- R4 remaining d steps
    have h_r4 : ⟨(0 : ℕ), 1, 0, d, e + 2⟩ [fm]⊢* ⟨0, d + 1, 0, 0, e + 2⟩ := by
      rw [show d = 0 + d from by ring]
      apply stepStar_trans (d_to_b d 1 0 (e + 2))
      ring_nf; finish
    -- R5 + R1 + R2
    have h_init : ⟨(0 : ℕ), d + 1, 0, 0, e + 2⟩ [fm]⊢* ⟨3, d, 0, 1, e + 1⟩ := by
      rw [show d + 1 = d + 1 from rfl, show e + 2 = (e + 1) + 1 from by ring]
      step fm; step fm; step fm; finish
    -- Middle transition
    have h_7e : 7 * (e + 1) ≥ d := by omega
    obtain ⟨d', e', h_middle, h_inv⟩ := middle_trans d 0 (e + 1) h_7e
    -- Compose: first step ⊢, rest ⊢*, gives ⊢⁺
    have h_star : ⟨(0 : ℕ), 1, 0, d, e + 2⟩ [fm]⊢* ⟨0, 0, 0, d' + 1, e' + 2⟩ :=
      stepStar_trans h_r4 (stepStar_trans h_init h_middle)
    exact ⟨⟨0, 0, 0, d' + 1, e' + 2⟩, ⟨d', e', rfl, h_inv⟩,
      step_stepStar_stepPlus h_first h_star⟩
  · exact ⟨3, 1, by ring_nf, by omega⟩

end Sz22_2003_unofficial_1263
