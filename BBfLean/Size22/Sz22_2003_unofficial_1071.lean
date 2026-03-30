import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1071: [5/6, 16/35, 77/2, 3/7, 14/11]

Vector representation:
```
-1 -1  1  0  0
 4  0 -1 -1  0
-1  0  0  1  1
 0  1  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1071

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+4, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

private theorem r3_drain : ∀ k, ∀ d e,
    ⟨k, (0 : ℕ), 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + 1) + k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    step fm; exact ih (d + 1) (e + 1)

private theorem r4_drain : ∀ k, ∀ b e,
    ⟨(0 : ℕ), b, 0, k, e⟩ [fm]⊢* ⟨0, b + k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · ring_nf; finish
  · rw [show b + (k + 1) = (b + 1) + k from by ring]
    step fm; exact ih (b + 1) e

private theorem r3r2_chain : ∀ k, ∀ a e,
    ⟨a + 1, (0 : ℕ), k, 0, e⟩ [fm]⊢* ⟨a + 1 + 3 * k, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · ring_nf; finish
  · rw [show a + 1 + 3 * (k + 1) = (a + 3) + 1 + 3 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    step fm; step fm; exact ih (a + 3) (e + 1)

private theorem r1_chain : ∀ k, ∀ a b c e,
    ⟨a + k, b + k, c, (0 : ℕ), e⟩ [fm]⊢* ⟨a, b, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a b c e
  · ring_nf; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + (k + 1) = (b + k) + 1 from by ring,
        show c + (k + 1) = (c + 1) + k from by ring]
    step fm; exact ih a b (c + 1) e

private theorem tail_b0 (C E : ℕ) :
    ⟨(0 : ℕ), 0, C + 1, 0, E + 1⟩ [fm]⊢⁺ ⟨5 + 3 * C, 0, 0, 0, E + C⟩ := by
  rw [show 5 + 3 * C = 4 + 1 + 3 * C from by ring]
  step fm; step fm
  exact r3r2_chain C 4 E

private theorem tail_b1 (C E : ℕ) :
    ⟨(0 : ℕ), 1, C, 0, E + 1⟩ [fm]⊢⁺ ⟨4 + 3 * C, 0, 0, 0, E + C⟩ := by
  rw [show 4 + 3 * C = 3 + 1 + 3 * C from by ring]
  step fm; step fm; step fm
  exact r3r2_chain C 3 E

private theorem tail_b2 (C E : ℕ) :
    ⟨(0 : ℕ), 2, C, 0, E + 1⟩ [fm]⊢⁺ ⟨6 + 3 * C, 0, 0, 0, E + C + 1⟩ := by
  rw [show 6 + 3 * C = 2 + 1 + 3 * (C + 1) from by ring,
      show E + C + 1 = E + (C + 1) from by ring]
  step fm; step fm; step fm
  apply stepStar_trans
  · rw [show (4 : ℕ) = 3 + 1 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
    exact r1_chain 1 3 0 C E
  exact r3r2_chain (C + 1) 2 E

private theorem tail_b3 (C E : ℕ) :
    ⟨(0 : ℕ), 3, C, 0, E + 1⟩ [fm]⊢⁺ ⟨8 + 3 * C, 0, 0, 0, E + C + 2⟩ := by
  rw [show 8 + 3 * C = 1 + 1 + 3 * (C + 2) from by ring,
      show E + C + 2 = E + (C + 2) from by ring]
  step fm; step fm; step fm
  apply stepStar_trans
  · rw [show (4 : ℕ) = 2 + 2 from by ring, show (2 : ℕ) = 0 + 2 from by ring]
    exact r1_chain 2 2 0 C E
  exact r3r2_chain (C + 2) 1 E

private theorem tail_b4 (C E : ℕ) :
    ⟨(0 : ℕ), 4, C, 0, E + 1⟩ [fm]⊢⁺ ⟨10 + 3 * C, 0, 0, 0, E + C + 3⟩ := by
  rw [show 10 + 3 * C = 0 + 1 + 3 * (C + 3) from by ring,
      show E + C + 3 = E + (C + 3) from by ring]
  step fm; step fm; step fm
  apply stepStar_trans
  · rw [show (4 : ℕ) = 1 + 3 from by ring, show (3 : ℕ) = 0 + 3 from by ring]
    exact r1_chain 3 1 0 C E
  exact r3r2_chain (C + 3) 0 E

private theorem round_step (B C E : ℕ) :
    ⟨(0 : ℕ), B + 5, C, 0, E + 1⟩ [fm]⊢* ⟨0, B, C + 4, 0, E⟩ := by
  rw [show B + 5 = (B + 4) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans
  · rw [show (4 : ℕ) = 0 + 4 from by ring]
    exact r1_chain 4 0 B C E
  ring_nf; finish

private theorem phase_c : ∀ B, ∀ C E, E ≥ B → (B = 0 → C ≥ 1 ∧ E ≥ 1) →
    ∃ a' e', a' ≥ 4 ∧
    ⟨(0 : ℕ), B, C, 0, E⟩ [fm]⊢⁺ ⟨a', 0, 0, 0, e'⟩ := by
  intro B; induction' B using Nat.strongRecOn with B IH; intro C E hEB hCB
  by_cases hB5 : B ≥ 5
  · obtain ⟨B', rfl⟩ := Nat.exists_eq_add_of_le hB5
    rw [show 5 + B' = B' + 5 from by ring]
    obtain ⟨E', rfl⟩ := Nat.exists_eq_add_of_le (show E ≥ 1 by omega)
    rw [show 1 + E' = E' + 1 from by ring]
    have hround := round_step B' C E'
    have ⟨a', e', ha', htrans⟩ := IH B' (by omega) (C + 4) E' (by omega)
      (by intro h; subst h; exact ⟨by omega, by omega⟩)
    exact ⟨a', e', ha', stepStar_stepPlus_stepPlus hround htrans⟩
  · have hE1 : E ≥ 1 := by
      rcases B with _ | B'
      · exact (hCB rfl).2
      · omega
    obtain ⟨E', rfl⟩ := Nat.exists_eq_add_of_le hE1
    rw [show 1 + E' = E' + 1 from by ring]
    rcases B with _ | _ | _ | _ | _ | B'
    · obtain ⟨hC, _⟩ := hCB rfl
      obtain ⟨C', rfl⟩ := Nat.exists_eq_add_of_le hC
      rw [show 1 + C' = C' + 1 from by ring]
      exact ⟨5 + 3 * C', E' + C', by omega, tail_b0 C' E'⟩
    · exact ⟨4 + 3 * C, E' + C, by omega, tail_b1 C E'⟩
    · exact ⟨6 + 3 * C, E' + C + 1, by omega, tail_b2 C E'⟩
    · exact ⟨8 + 3 * C, E' + C + 2, by omega, tail_b3 C E'⟩
    · exact ⟨10 + 3 * C, E' + C + 3, by omega, tail_b4 C E'⟩
    · omega

private theorem main_trans (a e : ℕ) (ha : a ≥ 1) :
    ∃ a' e', a' ≥ 4 ∧
    ⟨a, (0 : ℕ), 0, 0, e⟩ [fm]⊢⁺ ⟨a', 0, 0, 0, e'⟩ := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le ha
  rw [show 1 + a = a + 1 from by ring]
  have h1 : ⟨a + 1, (0 : ℕ), 0, 0, e⟩ [fm]⊢* ⟨0, 0, 0, 0 + (a + 1), e + (a + 1)⟩ :=
    r3_drain (a + 1) 0 e
  rw [show (0 : ℕ) + (a + 1) = a + 1 from by ring] at h1
  have h2 : ⟨(0 : ℕ), 0, 0, a + 1, e + (a + 1)⟩ [fm]⊢* ⟨0, 0 + (a + 1), 0, 0, e + (a + 1)⟩ :=
    r4_drain (a + 1) 0 (e + (a + 1))
  rw [show (0 : ℕ) + (a + 1) = a + 1 from by ring] at h2
  have ⟨a', e', ha', htrans⟩ := phase_c (a + 1) 0 (e + (a + 1)) (by omega)
    (by intro h; omega)
  exact ⟨a', e', ha', stepStar_stepPlus_stepPlus (stepStar_trans h1 h2) htrans⟩

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 0, 0⟩) (by execute fm 5)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ a ≥ 4)
  · intro c ⟨a, e, hc, ha⟩
    subst hc
    have ⟨a', e', ha', htrans⟩ := main_trans a e (by omega)
    exact ⟨⟨a', 0, 0, 0, e'⟩, ⟨a', e', rfl, ha'⟩, htrans⟩
  · exact ⟨4, 0, rfl, le_refl 4⟩

end Sz22_2003_unofficial_1071
