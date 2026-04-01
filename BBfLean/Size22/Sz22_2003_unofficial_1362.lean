import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1362: [63/10, 4/33, 143/2, 5/7, 15/13]

Vector representation:
```
-1  2 -1  1  0  0
 2 -1  0  0 -1  0
-1  0  0  0  1  1
 0  0  1 -1  0  0
 0  1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1362

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e, f⟩ => some ⟨a, b+2, c, d+1, e, f⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c+1, d, e, f⟩
  | _ => none

theorem r3_drain : ∀ k, ∀ d e f,
    ⟨k, (0 : ℕ), (0 : ℕ), d, e, f⟩ [fm]⊢*
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), d, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro d e f
  · exists 0
  · rw [show k + 1 = k + 1 from rfl]; step fm
    apply stepStar_trans (ih d (e + 1) (f + 1)); ring_nf; finish

theorem r4_transfer : ∀ k, ∀ c d e f,
    ⟨(0 : ℕ), (0 : ℕ), c, d + k, e, f⟩ [fm]⊢*
    ⟨(0 : ℕ), (0 : ℕ), c + k, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (c + 1) d e f); ring_nf; finish

theorem r2_drain : ∀ k, ∀ a b d e f,
    ⟨a, b + k, (0 : ℕ), d, e + k, f⟩ [fm]⊢*
    ⟨a + 2 * k, b, (0 : ℕ), d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro a b d e f
  · simp; exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) b d e f); ring_nf; finish

theorem r112_even_chain : ∀ k, ∀ b d e f,
    ⟨(2 : ℕ), b, 2 * k, d, e + k, f⟩ [fm]⊢*
    ⟨(2 : ℕ), b + 3 * k, (0 : ℕ), d + 2 * k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · simp; exists 0
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show d + 1 + 1 = d + 2 from by ring]
    apply stepStar_trans (ih (b + 3) (d + 2) e f); ring_nf; finish

theorem r112_odd_chain : ∀ k, ∀ b d e f,
    ⟨(2 : ℕ), b, 2 * k + 1, d, e + k, f⟩ [fm]⊢*
    ⟨(1 : ℕ), b + 3 * k + 2, (0 : ℕ), d + 2 * k + 1, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · step fm; ring_nf; finish
  · rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show d + 1 + 1 = d + 2 from by ring]
    apply stepStar_trans (ih (b + 3) (d + 2) e f); ring_nf; finish

theorem main_even (m e f' : ℕ) (hm : m ≥ 2) (he : e ≥ 4 * m + 3) :
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 2 * m, e, f' + 1⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 2 * m + 1, e + 2 * m + 2, f' + 6 * m + 5⟩ := by
  have h1 := r4_transfer (2 * m) 0 0 e (f' + 1)
  simp only [Nat.zero_add] at h1
  have h2 : ⟨(0 : ℕ), (0 : ℕ), 2 * m, (0 : ℕ), e, f' + 1⟩ [fm]⊢*
      ⟨(2 : ℕ), (0 : ℕ), 2 * m + 1, (0 : ℕ), e - 1, f'⟩ := by
    rw [show (f' + 1 : ℕ) = f' + 1 from rfl]
    step fm  -- R5: (0, 1, 2m+1, 0, e, f')
    rw [show (e : ℕ) = (e - 1) + 1 from by omega]
    step fm  -- R2: (2, 0, 2m+1, 0, e-1, f')
    finish
  have h3 := r112_odd_chain m 0 0 (e - 1 - m) f'
  rw [show 0 + 3 * m + 2 = 3 * m + 2 from by ring,
      show 0 + 2 * m + 1 = 2 * m + 1 from by ring,
      show (e - 1 - m) + m = e - 1 from by omega] at h3
  have h4 := r2_drain (3 * m + 2) 1 0 (2 * m + 1) (e - 4 * m - 3) f'
  rw [show 0 + (3 * m + 2) = 3 * m + 2 from by ring,
      show (e - 4 * m - 3) + (3 * m + 2) = e - 1 - m from by omega,
      show 1 + 2 * (3 * m + 2) = 6 * m + 5 from by ring] at h4
  have h5 := r3_drain (6 * m + 5) (2 * m + 1) (e - 4 * m - 3) f'
  rw [show (e - 4 * m - 3) + (6 * m + 5) = e + 2 * m + 2 from by omega,
      show f' + (6 * m + 5) = f' + 6 * m + 5 from by ring] at h5
  have hall := stepStar_trans (stepStar_trans (stepStar_trans (stepStar_trans h1 h2) h3) h4) h5
  exact stepStar_stepPlus hall (by simp [Q])

theorem main_odd (m e f' : ℕ) (hm : m ≥ 1) (he : e ≥ 4 * m + 5) :
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 2 * m + 1, e, f' + 1⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 2 * m + 2, e + 2 * m + 3, f' + 6 * m + 8⟩ := by
  have h1 := r4_transfer (2 * m + 1) 0 0 e (f' + 1)
  simp only [Nat.zero_add] at h1
  have h2 : ⟨(0 : ℕ), (0 : ℕ), 2 * m + 1, (0 : ℕ), e, f' + 1⟩ [fm]⊢*
      ⟨(2 : ℕ), (0 : ℕ), 2 * (m + 1), (0 : ℕ), e - 1, f'⟩ := by
    rw [show (f' + 1 : ℕ) = f' + 1 from rfl]
    step fm  -- R5: (0, 1, 2m+2, 0, e, f')
    rw [show 2 * m + 1 + 1 = 2 * (m + 1) from by ring,
        show (e : ℕ) = (e - 1) + 1 from by omega]
    step fm  -- R2: (2, 0, 2(m+1), 0, e-1, f')
    finish
  have h3 := r112_even_chain (m + 1) 0 0 (e - 1 - (m + 1)) f'
  rw [show 0 + 3 * (m + 1) = 3 * m + 3 from by ring,
      show 0 + 2 * (m + 1) = 2 * m + 2 from by ring,
      show (e - 1 - (m + 1)) + (m + 1) = e - 1 from by omega] at h3
  have h4 := r2_drain (3 * m + 3) 2 0 (2 * m + 2) (e - 4 * m - 5) f'
  rw [show 0 + (3 * m + 3) = 3 * m + 3 from by ring,
      show (e - 4 * m - 5) + (3 * m + 3) = e - 1 - (m + 1) from by omega,
      show 2 + 2 * (3 * m + 3) = 6 * m + 8 from by ring] at h4
  have h5 := r3_drain (6 * m + 8) (2 * m + 2) (e - 4 * m - 5) f'
  rw [show (e - 4 * m - 5) + (6 * m + 8) = e + 2 * m + 3 from by omega,
      show f' + (6 * m + 8) = f' + 6 * m + 8 from by ring] at h5
  have hall := stepStar_trans (stepStar_trans (stepStar_trans (stepStar_trans h1 h2) h3) h4) h5
  exact stepStar_stepPlus hall (by simp [Q])

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 10, 22⟩) (by execute fm 52)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e f', q = ⟨0, 0, 0, d, e, f' + 1⟩ ∧ d ≥ 3 ∧ e ≥ 2 * d + 3)
  · intro c ⟨d, e, f', hq, hd, he⟩
    subst hq
    rcases Nat.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
    · rw [show m + m = 2 * m from by ring] at hm; subst hm
      exact ⟨⟨0, 0, 0, 2 * m + 1, e + 2 * m + 2, f' + 6 * m + 5⟩,
        ⟨2 * m + 1, e + 2 * m + 2, f' + 6 * m + 4,
         by ring_nf, by omega, by omega⟩,
        main_even m e f' (by omega) (by omega)⟩
    · subst hm
      rcases m with _ | m
      · omega
      · exact ⟨⟨0, 0, 0, 2 * (m + 1) + 2, e + 2 * (m + 1) + 3, f' + 6 * (m + 1) + 8⟩,
          ⟨2 * (m + 1) + 2, e + 2 * (m + 1) + 3, f' + 6 * (m + 1) + 7,
           by ring_nf, by omega, by omega⟩,
          main_odd (m + 1) e f' (by omega) (by omega)⟩
  · exact ⟨3, 10, 21, by ring_nf, by omega, by omega⟩

end Sz22_2003_unofficial_1362
