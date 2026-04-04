import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1975: [99/35, 25/6, 2/5, 7/11, 165/2]

Vector representation:
```
 0  2 -1 -1  1
-1 -1  2  0  0
 1  0 -1  0  0
 0  0  0  1 -1
-1  1  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1975

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e+1⟩
  | _ => none

theorem e_to_d : ∀ k d, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · rw [show e + (k + 1) = e + k + 1 from by ring]; step fm
    apply stepStar_trans (ih (d + 1)); ring_nf; finish

theorem c_to_a : ∀ k a, ⟨a, 0, c + k, 0, e⟩ [fm]⊢* ⟨a + k, 0, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a
  · exists 0
  · rw [show c + (k + 1) = c + k + 1 from by ring]; step fm
    apply stepStar_trans (ih (a + 1)); ring_nf; finish

theorem r2_chain : ∀ k a b c, ⟨a + k, b + k, c, 0, e⟩ [fm]⊢* ⟨a, b, c + 2 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a b c
  · exists 0
  · rw [show a + (k + 1) = a + k + 1 from by ring,
        show b + (k + 1) = b + k + 1 from by ring]; step fm
    apply stepStar_trans (ih a b (c + 2)); ring_nf; finish

theorem r3r2_alt : ∀ k b c, ⟨0, b + k, c + 1, 0, e⟩ [fm]⊢* ⟨0, b, c + k + 1, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c
  · exists 0
  · rw [show b + (k + 1) = b + k + 1 from by ring]; step fm; step fm
    apply stepStar_trans (ih b (c + 1)); ring_nf; finish

theorem interleaved : ∀ k a b d e, ⟨a + k, b + 1, 0, d + 2 * k, e⟩ [fm]⊢* ⟨a, b + 1 + 3 * k, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show a + (k + 1) = a + k + 1 from by ring,
        show d + 2 * (k + 1) = d + 2 * k + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih a (b + 3) d (e + 2)); ring_nf; finish

theorem drain_ge (hBA : B ≤ A) : ⟨A, B, 0, 0, E⟩ [fm]⊢* ⟨A + B, 0, 0, 0, E⟩ := by
  have h1 := r2_chain B (A - B) 0 0 (e := E)
  rw [show A - B + B = A from by omega, show 0 + B = B from by omega,
      show 0 + 2 * B = 2 * B from by ring] at h1
  have h2 := c_to_a (2 * B) (A - B) (c := 0) (e := E)
  rw [show 0 + 2 * B = 2 * B from by ring,
      show A - B + 2 * B = A + B from by omega] at h2
  exact stepStar_trans h1 h2

theorem drain_lt (hAB : A < B) (hA : A ≥ 1) : ⟨A, B, 0, 0, E⟩ [fm]⊢* ⟨A + B, 0, 0, 0, E⟩ := by
  have h1 := r2_chain A 0 (B - A) 0 (e := E)
  rw [show 0 + A = A from by omega, show B - A + A = B from by omega,
      show 0 + 2 * A = 2 * A from by ring] at h1
  have h2 := r3r2_alt (B - A) 0 (2 * A - 1) (e := E)
  rw [show 0 + (B - A) = B - A from by ring,
      show (2 * A - 1) + 1 = 2 * A from by omega,
      show 2 * A - 1 + (B - A) + 1 = A + B from by omega] at h2
  have h3 := c_to_a (A + B) 0 (c := 0) (e := E)
  rw [show 0 + (A + B) = A + B from by ring] at h3
  exact stepStar_trans h1 (stepStar_trans h2 h3)

theorem drain (hA : A ≥ 1) : ⟨A, B, 0, 0, E⟩ [fm]⊢* ⟨A + B, 0, 0, 0, E⟩ := by
  rcases le_or_gt B A with hBA | hAB
  · exact drain_ge hBA
  · exact drain_lt hAB hA

theorem drain_c (hA : A ≥ 1 ∨ C ≥ 1) : ⟨A, B, C, 0, E⟩ [fm]⊢* ⟨A + B + C, 0, 0, 0, E⟩ := by
  rcases Nat.eq_zero_or_pos C with hC | hC
  · rw [hC]; simp; exact drain (by rcases hA with h | h <;> omega)
  · rcases le_or_gt B A with hBA | hABlt
    · have h1 := r2_chain B (A - B) 0 C (e := E)
      rw [show A - B + B = A from by omega, show 0 + B = B from by omega] at h1
      have h2 := c_to_a (C + 2 * B) (A - B) (c := 0) (e := E)
      rw [show 0 + (C + 2 * B) = C + 2 * B from by ring,
          show A - B + (C + 2 * B) = A + B + C from by omega] at h2
      exact stepStar_trans h1 h2
    · have h1 := r2_chain A 0 (B - A) C (e := E)
      rw [show 0 + A = A from by omega, show B - A + A = B from by omega] at h1
      have h2 := r3r2_alt (B - A) 0 (C + 2 * A - 1) (e := E)
      rw [show 0 + (B - A) = B - A from by ring,
          show (C + 2 * A - 1) + 1 = C + 2 * A from by omega,
          show C + 2 * A - 1 + (B - A) + 1 = A + B + C from by omega] at h2
      have h3 := c_to_a (A + B + C) 0 (c := 0) (e := E)
      rw [show 0 + (A + B + C) = A + B + C from by ring] at h3
      exact stepStar_trans h1 (stepStar_trans h2 h3)

theorem r5_step : ⟨a + 1, 0, 0, d, 0⟩ [fm]⊢ ⟨a, 1, 1, d, 1⟩ := by simp [fm]

-- e odd: e = 2m+1, a >= 2m+2
theorem main_odd (ha : a ≥ 2 * m + 2) :
    ⟨a, 0, 0, 0, 2 * m + 1⟩ [fm]⊢⁺ ⟨a + 2 * m + 2, 0, 0, 0, 2 * m + 2⟩ := by
  obtain ⟨F, rfl⟩ : ∃ F, a = F + 2 * m + 2 := ⟨a - 2 * m - 2, by omega⟩
  have h1 : ⟨F + 2 * m + 2, 0, 0, 0, 2 * m + 1⟩ [fm]⊢* ⟨F + 2 * m + 2, 0, 0, 2 * m + 1, 0⟩ := by
    rw [show 2 * m + 1 = 0 + (2 * m + 1) from by ring]; exact e_to_d (2 * m + 1) 0
  have h2 : ⟨F + 2 * m + 2, 0, 0, 2 * m + 1, 0⟩ [fm]⊢ ⟨F + 2 * m + 1, 1, 1, 2 * m + 1, 1⟩ := by
    rw [show F + 2 * m + 2 = (F + 2 * m + 1) + 1 from by ring]; exact r5_step
  have h3 : ⟨F + 2 * m + 1, 1, 1, 2 * m + 1, 1⟩ [fm]⊢ ⟨F + 2 * m + 1, 3, 0, 2 * m, 2⟩ := by
    show fm ⟨F + 2 * m + 1, 1, 0 + 1, (2 * m) + 1, 1⟩ = some ⟨F + 2 * m + 1, 1 + 2, 0, 2 * m, 1 + 1⟩; rfl
  have h4 : ⟨F + 2 * m + 1, 3, 0, 2 * m, 2⟩ [fm]⊢* ⟨F + m + 1, 3 * m + 3, 0, 0, 2 * m + 2⟩ := by
    have h := interleaved m (F + m + 1) 2 0 2
    rw [show (F + m + 1) + m = F + 2 * m + 1 from by ring,
        show 2 + 1 = 3 from by ring,
        show 0 + 2 * m = 2 * m from by ring,
        show 2 + 1 + 3 * m = 3 * m + 3 from by ring,
        show 2 + 2 * m = 2 * m + 2 from by ring] at h; exact h
  have h5 : ⟨F + m + 1, 3 * m + 3, 0, 0, 2 * m + 2⟩ [fm]⊢* ⟨F + 2 * m + 2 + (2 * m + 2), 0, 0, 0, 2 * m + 2⟩ := by
    rw [show F + 2 * m + 2 + (2 * m + 2) = F + m + 1 + (3 * m + 3) from by ring]
    exact drain (by omega)
  exact stepStar_stepPlus_stepPlus h1
    (step_stepStar_stepPlus h2 (stepStar_trans (step_stepStar h3) (stepStar_trans h4 h5)))

-- e even >= 2: e = 2*(m+1), a >= 2m+3
theorem main_even (ha : a ≥ 2 * m + 3) :
    ⟨a, 0, 0, 0, 2 * (m + 1)⟩ [fm]⊢⁺ ⟨a + 2 * m + 3, 0, 0, 0, 2 * m + 3⟩ := by
  obtain ⟨F, rfl⟩ : ∃ F, a = F + 2 * m + 3 := ⟨a - 2 * m - 3, by omega⟩
  have h1 : ⟨F + 2 * m + 3, 0, 0, 0, 2 * (m + 1)⟩ [fm]⊢* ⟨F + 2 * m + 3, 0, 0, 2 * (m + 1), 0⟩ := by
    rw [show 2 * (m + 1) = 0 + 2 * (m + 1) from by ring]; exact e_to_d (2 * (m + 1)) 0
  have h2 : ⟨F + 2 * m + 3, 0, 0, 2 * (m + 1), 0⟩ [fm]⊢ ⟨F + 2 * m + 2, 1, 1, 2 * (m + 1), 1⟩ := by
    rw [show F + 2 * m + 3 = (F + 2 * m + 2) + 1 from by ring]; exact r5_step
  have h3 : ⟨F + 2 * m + 2, 1, 1, 2 * (m + 1), 1⟩ [fm]⊢ ⟨F + 2 * m + 2, 3, 0, 2 * m + 1, 2⟩ := by
    show fm ⟨F + 2 * m + 2, 1, 0 + 1, (2 * m + 1) + 1, 1⟩ = some ⟨F + 2 * m + 2, 1 + 2, 0, 2 * m + 1, 1 + 1⟩; rfl
  have h4 : ⟨F + 2 * m + 2, 3, 0, 2 * m + 1, 2⟩ [fm]⊢* ⟨F + m + 2, 3 * m + 3, 0, 1, 2 * m + 2⟩ := by
    have h := interleaved m (F + m + 2) 2 1 2
    rw [show (F + m + 2) + m = F + 2 * m + 2 from by ring,
        show 2 + 1 = 3 from by ring,
        show 1 + 2 * m = 2 * m + 1 from by ring,
        show 2 + 1 + 3 * m = 3 * m + 3 from by ring,
        show 2 + 2 * m = 2 * m + 2 from by ring] at h; exact h
  -- tail: R2, R1, R2 (3 steps)
  have h5 : ⟨F + m + 2, 3 * m + 3, 0, 1, 2 * m + 2⟩ [fm]⊢* ⟨F + m, 3 * m + 3, 3, 0, 2 * m + 3⟩ := by
    rw [show F + m + 2 = (F + m + 1) + 1 from by ring,
        show 3 * m + 3 = (3 * m + 2) + 1 from by ring]
    step fm -- R2
    step fm -- R1
    rw [show F + m + 1 = (F + m) + 1 from by ring,
        show 3 * m + 2 + 2 = (3 * m + 3) + 1 from by ring]
    step fm -- R2
    rw [show 2 * m + 2 + 1 = 2 * m + 3 from by ring]
    finish
  -- drain with c
  have h6 : ⟨F + m, 3 * m + 3, 3, 0, 2 * m + 3⟩ [fm]⊢* ⟨F + 2 * m + 3 + (2 * m + 3), 0, 0, 0, 2 * m + 3⟩ := by
    rw [show F + 2 * m + 3 + (2 * m + 3) = F + m + (3 * m + 3) + 3 from by ring]
    exact drain_c (by omega)
  exact stepStar_stepPlus_stepPlus h1
    (step_stepStar_stepPlus h2 (stepStar_trans (step_stepStar h3) (stepStar_trans h4 (stepStar_trans h5 h6))))

-- e = 0
theorem main_e0 (ha : a ≥ 1) :
    ⟨a, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + 1, 0, 0, 0, 1⟩ := by
  obtain ⟨F, rfl⟩ : ∃ F, a = F + 1 := ⟨a - 1, by omega⟩
  apply step_stepStar_stepPlus r5_step
  rcases F with _ | F
  · execute fm 4
  · step fm
    rw [show (3 : ℕ) = 0 + 3 from by ring]
    have h := c_to_a 3 F (c := 0) (e := 1)
    rw [show 0 + 3 = 3 from by ring, show F + 3 = F + 1 + 1 + 1 from by ring] at h; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1⟩)
  · execute fm 5
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ a ≥ e + 1)
  · intro q ⟨a, e, hq, ha⟩; subst hq
    rcases e with _ | e
    · exact ⟨⟨a + 1, 0, 0, 0, 1⟩, ⟨a + 1, 1, rfl, by omega⟩, main_e0 (by omega)⟩
    · rcases Nat.even_or_odd (e + 1) with ⟨m, hm⟩ | ⟨m, hm⟩
      · obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        have he : e + 1 = 2 * (m + 1) := by omega
        have ha2 : a ≥ 2 * m + 3 := by omega
        rw [he]
        exact ⟨⟨a + 2 * m + 3, 0, 0, 0, 2 * m + 3⟩,
          ⟨a + 2 * m + 3, 2 * m + 3, rfl, by omega⟩,
          main_even ha2⟩
      · have he : e + 1 = 2 * m + 1 := by omega
        have ha2 : a ≥ 2 * m + 2 := by omega
        rw [he]
        exact ⟨⟨a + 2 * m + 2, 0, 0, 0, 2 * m + 2⟩,
          ⟨a + 2 * m + 2, 2 * m + 2, rfl, by omega⟩,
          main_odd ha2⟩
  · exact ⟨2, 1, rfl, by omega⟩
