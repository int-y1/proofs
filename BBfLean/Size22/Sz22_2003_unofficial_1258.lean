import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1258: [5/6, 77/2, 8/35, 3/7, 98/11]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  1  1
 3  0 -1 -1  0
 0  1  0 -1  0
 1  0  0  2 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1258

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+2, e⟩
  | _ => none

theorem d_to_b : ∀ k b d e, ⟨(0:ℕ), b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (b + 1) d e); ring_nf; finish

theorem drain : ∀ k c d e, ⟨(3:ℕ), 0, c + k, d, e⟩ [fm]⊢* ⟨3, 0, c, d + 2 * k, e + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · simp; exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show d + 3 = (d + 2) + 1 from by ring]
    step fm
    apply stepStar_trans (ih c (d + 2) (e + 3)); ring_nf; finish

theorem drain_full (C D Ef : ℕ) :
    ⟨(3:ℕ), 0, C, D, Ef⟩ [fm]⊢⁺ ⟨0, 0, 0, D + 2 * C + 3, Ef + 3 * C + 3⟩ := by
  rw [show C = 0 + C from by ring]
  have hd := drain C 0 D Ef
  rw [show (0:ℕ) = 0 from rfl] at hd
  apply stepStar_stepPlus_stepPlus hd
  step fm; step fm; step fm; ring_nf; finish

theorem recurrence : ∀ B C E, ⟨(3:ℕ), B + 7, C, 1, E + 1⟩ [fm]⊢* ⟨3, B, C + 5, 1, E⟩ := by
  intro B C E
  step fm; step fm; step fm
  rw [show C + 3 = (C + 2) + 1 from by ring, show (1:ℕ) = 0 + 1 from by ring]
  step fm; step fm; step fm; step fm
  step fm; step fm
  rw [show C + 6 = (C + 5) + 1 from by ring, show (2:ℕ) = 1 + 1 from by ring]
  step fm; finish

theorem recurrence_iter : ∀ k B C E, ⟨(3:ℕ), B + 7 * k, C, 1, E + k⟩ [fm]⊢* ⟨3, B, C + 5 * k, 1, E⟩ := by
  intro k; induction' k with k ih <;> intro B C E
  · simp; exists 0
  · rw [show B + 7 * (k + 1) = (B + 7) + 7 * k from by ring,
        show E + (k + 1) = (E + 1) + k from by ring]
    apply stepStar_trans (ih (B + 7) C (E + 1))
    apply stepStar_trans (recurrence B (C + 5 * k) E)
    ring_nf; finish

theorem opening (D E : ℕ) : ⟨(0:ℕ), D + 1, 0, 0, E + 1⟩ [fm]⊢⁺ ⟨3, D, 0, 1, E⟩ := by
  step fm; step fm
  rw [show (1:ℕ) = 0 + 1 from by ring, show (2:ℕ) = 1 + 1 from by ring]
  step fm; finish

theorem phase12 (D E : ℕ) :
    ⟨(0:ℕ), 0, 0, D + 1, E + 1⟩ [fm]⊢⁺ ⟨3, D, 0, 1, E⟩ := by
  rw [show D + 1 = 0 + (D + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (D + 1) 0 0 (E + 1))
  rw [show (0:ℕ) + (D + 1) = D + 1 from by ring]
  exact opening D E

theorem base0 (C E : ℕ) :
    ⟨(3:ℕ), 0, C, 1, E⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * C + 4, E + 3 * C + 3⟩ := by
  have h := drain_full C 1 E; convert h using 2 ; all_goals ring_nf

theorem base1 (C E : ℕ) :
    ⟨(3:ℕ), 1, C, 1, E⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * C + 5, E + 3 * C + 5⟩ := by
  step fm; step fm; step fm
  rw [show C + 1 = C + 1 from rfl, show (3:ℕ) = 2 + 1 from by ring]
  step fm
  have h := drain_full C 2 (E + 2)
  apply stepStar_trans (stepPlus_stepStar h); ring_nf; finish

theorem base2 (C E : ℕ) :
    ⟨(3:ℕ), 2, C, 1, E⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * C + 6, E + 3 * C + 7⟩ := by
  step fm; step fm; step fm
  rw [show C + 2 = (C + 1) + 1 from by ring, show (2:ℕ) = 1 + 1 from by ring]
  step fm
  have h := drain_full (C + 1) 1 (E + 1)
  apply stepStar_trans (stepPlus_stepStar h); ring_nf; finish

theorem base3 (C E : ℕ) :
    ⟨(3:ℕ), 3, C, 1, E⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * C + 7, E + 3 * C + 9⟩ := by
  step fm; step fm; step fm
  rw [show C + 3 = (C + 2) + 1 from by ring, show (1:ℕ) = 0 + 1 from by ring]
  step fm; step fm; step fm; step fm
  rw [show C + 2 = (C + 1) + 1 from by ring, show (3:ℕ) = 2 + 1 from by ring]
  step fm
  have h := drain_full (C + 1) 2 (E + 3)
  apply stepStar_trans (stepPlus_stepStar h); ring_nf; finish

theorem base4 (C E : ℕ) :
    ⟨(3:ℕ), 4, C, 1, E⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * C + 8, E + 3 * C + 11⟩ := by
  step fm; step fm; step fm
  rw [show C + 3 = (C + 2) + 1 from by ring, show (1:ℕ) = 0 + 1 from by ring]
  step fm; step fm; step fm; step fm
  rw [show C + 3 = (C + 2) + 1 from by ring, show (2:ℕ) = 1 + 1 from by ring]
  step fm
  have h := drain_full (C + 2) 1 (E + 2)
  apply stepStar_trans (stepPlus_stepStar h); ring_nf; finish

theorem base5 (C E : ℕ) :
    ⟨(3:ℕ), 5, C, 1, E⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * C + 9, E + 3 * C + 13⟩ := by
  step fm; step fm; step fm
  rw [show C + 3 = (C + 2) + 1 from by ring, show (1:ℕ) = 0 + 1 from by ring]
  step fm; step fm; step fm; step fm
  rw [show C + 4 = (C + 3) + 1 from by ring, show (1:ℕ) = 0 + 1 from by ring]
  step fm; step fm; step fm; step fm
  rw [show C + 3 = (C + 2) + 1 from by ring, show (3:ℕ) = 2 + 1 from by ring]
  step fm
  have h := drain_full (C + 2) 2 (E + 4)
  apply stepStar_trans (stepPlus_stepStar h); ring_nf; finish

theorem base6 (C E : ℕ) :
    ⟨(3:ℕ), 6, C, 1, E + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * C + 13, E + 3 * C + 16⟩ := by
  step fm; step fm; step fm
  rw [show C + 3 = (C + 2) + 1 from by ring, show (1:ℕ) = 0 + 1 from by ring]
  step fm; step fm; step fm; step fm
  step fm; step fm
  rw [show C + 5 = (C + 4) + 1 from by ring, show (3:ℕ) = 2 + 1 from by ring]
  step fm
  have h := drain_full (C + 4) 2 (E + 1)
  apply stepStar_trans (stepPlus_stepStar h); ring_nf; finish

theorem trans0 (k E : ℕ) :
    ⟨(0:ℕ), 0, 0, 7 * k + 1, E + k + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 10 * k + 4, E + 15 * k + 3⟩ := by
  have h1 := phase12 (7 * k + 0) (E + k)
  rw [show 7 * k + 0 + 1 = 7 * k + 1 from by ring,
      show (E + k) + 1 = E + k + 1 from by ring] at h1
  have h2 := recurrence_iter k 0 0 E
  rw [show (0:ℕ) + 7 * k = 7 * k from by ring,
      show (0:ℕ) + 5 * k = 5 * k from by ring] at h2
  have h3 := base0 (5 * k) E
  apply stepPlus_trans (stepPlus_stepStar_stepPlus h1 h2)
  convert h3 using 2 ; all_goals ring_nf

theorem trans1 (k E : ℕ) :
    ⟨(0:ℕ), 0, 0, 7 * k + 2, E + k + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 10 * k + 5, E + 15 * k + 5⟩ := by
  have h1 := phase12 (7 * k + 1) (E + k)
  rw [show 7 * k + 1 + 1 = 7 * k + 2 from by ring,
      show (E + k) + 1 = E + k + 1 from by ring] at h1
  have h2 := recurrence_iter k 1 0 E
  rw [show 1 + 7 * k = 7 * k + 1 from by ring,
      show (0:ℕ) + 5 * k = 5 * k from by ring] at h2
  have h3 := base1 (5 * k) E
  apply stepPlus_trans (stepPlus_stepStar_stepPlus h1 h2)
  convert h3 using 2 ; all_goals ring_nf

theorem trans2 (k E : ℕ) :
    ⟨(0:ℕ), 0, 0, 7 * k + 3, E + k + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 10 * k + 6, E + 15 * k + 7⟩ := by
  have h1 := phase12 (7 * k + 2) (E + k)
  rw [show 7 * k + 2 + 1 = 7 * k + 3 from by ring,
      show (E + k) + 1 = E + k + 1 from by ring] at h1
  have h2 := recurrence_iter k 2 0 E
  rw [show 2 + 7 * k = 7 * k + 2 from by ring,
      show (0:ℕ) + 5 * k = 5 * k from by ring] at h2
  have h3 := base2 (5 * k) E
  apply stepPlus_trans (stepPlus_stepStar_stepPlus h1 h2)
  convert h3 using 2 ; all_goals ring_nf

theorem trans3 (k E : ℕ) :
    ⟨(0:ℕ), 0, 0, 7 * k + 4, E + k + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 10 * k + 7, E + 15 * k + 9⟩ := by
  have h1 := phase12 (7 * k + 3) (E + k)
  rw [show 7 * k + 3 + 1 = 7 * k + 4 from by ring,
      show (E + k) + 1 = E + k + 1 from by ring] at h1
  have h2 := recurrence_iter k 3 0 E
  rw [show 3 + 7 * k = 7 * k + 3 from by ring,
      show (0:ℕ) + 5 * k = 5 * k from by ring] at h2
  have h3 := base3 (5 * k) E
  apply stepPlus_trans (stepPlus_stepStar_stepPlus h1 h2)
  convert h3 using 2 ; all_goals ring_nf

theorem trans4 (k E : ℕ) :
    ⟨(0:ℕ), 0, 0, 7 * k + 5, E + k + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 10 * k + 8, E + 15 * k + 11⟩ := by
  have h1 := phase12 (7 * k + 4) (E + k)
  rw [show 7 * k + 4 + 1 = 7 * k + 5 from by ring,
      show (E + k) + 1 = E + k + 1 from by ring] at h1
  have h2 := recurrence_iter k 4 0 E
  rw [show 4 + 7 * k = 7 * k + 4 from by ring,
      show (0:ℕ) + 5 * k = 5 * k from by ring] at h2
  have h3 := base4 (5 * k) E
  apply stepPlus_trans (stepPlus_stepStar_stepPlus h1 h2)
  convert h3 using 2 ; all_goals ring_nf

theorem trans5 (k E : ℕ) :
    ⟨(0:ℕ), 0, 0, 7 * k + 6, E + k + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 10 * k + 9, E + 15 * k + 13⟩ := by
  have h1 := phase12 (7 * k + 5) (E + k)
  rw [show 7 * k + 5 + 1 = 7 * k + 6 from by ring,
      show (E + k) + 1 = E + k + 1 from by ring] at h1
  have h2 := recurrence_iter k 5 0 E
  rw [show 5 + 7 * k = 7 * k + 5 from by ring,
      show (0:ℕ) + 5 * k = 5 * k from by ring] at h2
  have h3 := base5 (5 * k) E
  apply stepPlus_trans (stepPlus_stepStar_stepPlus h1 h2)
  convert h3 using 2 ; all_goals ring_nf

theorem trans6 (k E : ℕ) :
    ⟨(0:ℕ), 0, 0, 7 * (k + 1), E + k + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, 10 * k + 13, E + 15 * k + 16⟩ := by
  have h1 := phase12 (7 * k + 6) (E + k + 1)
  rw [show 7 * k + 6 + 1 = 7 * (k + 1) from by ring,
      show (E + k + 1) + 1 = E + k + 2 from by ring] at h1
  have h2 := recurrence_iter k 6 0 (E + 1)
  rw [show 6 + 7 * k = 7 * k + 6 from by ring,
      show (0:ℕ) + 5 * k = 5 * k from by ring,
      show (E + 1) + k = E + k + 1 from by ring] at h2
  have h3 := base6 (5 * k) E
  apply stepPlus_trans (stepPlus_stepStar_stepPlus h1 h2)
  convert h3 using 2 ; all_goals ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 4, 3⟩) (by execute fm 8)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d Ef, q = ⟨0, 0, 0, d, Ef⟩ ∧ d ≥ 1 ∧ Ef ≥ 1 ∧ 7 * Ef ≥ d + 7)
  · intro c ⟨d, Ef, hq, hd, hEf, hI⟩; subst hq
    obtain ⟨k, rfl | rfl | rfl | rfl | rfl | rfl | rfl⟩ : ∃ k,
        d = 7 * k + 1 ∨ d = 7 * k + 2 ∨ d = 7 * k + 3 ∨ d = 7 * k + 4 ∨
        d = 7 * k + 5 ∨ d = 7 * k + 6 ∨ d = 7 * (k + 1) :=
      ⟨(d - 1) / 7, by omega⟩
    · obtain ⟨e, rfl⟩ : ∃ e, Ef = e + k + 1 := ⟨Ef - k - 1, by omega⟩
      exact ⟨_, ⟨10*k+4, e+15*k+3, rfl, by omega, by omega, by omega⟩, trans0 k e⟩
    · obtain ⟨e, rfl⟩ : ∃ e, Ef = e + k + 1 := ⟨Ef - k - 1, by omega⟩
      exact ⟨_, ⟨10*k+5, e+15*k+5, rfl, by omega, by omega, by omega⟩, trans1 k e⟩
    · obtain ⟨e, rfl⟩ : ∃ e, Ef = e + k + 1 := ⟨Ef - k - 1, by omega⟩
      exact ⟨_, ⟨10*k+6, e+15*k+7, rfl, by omega, by omega, by omega⟩, trans2 k e⟩
    · obtain ⟨e, rfl⟩ : ∃ e, Ef = e + k + 1 := ⟨Ef - k - 1, by omega⟩
      exact ⟨_, ⟨10*k+7, e+15*k+9, rfl, by omega, by omega, by omega⟩, trans3 k e⟩
    · obtain ⟨e, rfl⟩ : ∃ e, Ef = e + k + 1 := ⟨Ef - k - 1, by omega⟩
      exact ⟨_, ⟨10*k+8, e+15*k+11, rfl, by omega, by omega, by omega⟩, trans4 k e⟩
    · obtain ⟨e, rfl⟩ : ∃ e, Ef = e + k + 1 := ⟨Ef - k - 1, by omega⟩
      exact ⟨_, ⟨10*k+9, e+15*k+13, rfl, by omega, by omega, by omega⟩, trans5 k e⟩
    · obtain ⟨e, rfl⟩ : ∃ e, Ef = e + k + 2 := ⟨Ef - k - 2, by omega⟩
      exact ⟨_, ⟨10*k+13, e+15*k+16, rfl, by omega, by omega, by omega⟩, trans6 k e⟩
  · exact ⟨4, 3, rfl, by omega, by omega, by omega⟩

end Sz22_2003_unofficial_1258
