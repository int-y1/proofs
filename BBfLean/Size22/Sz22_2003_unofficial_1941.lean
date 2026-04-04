import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz22_2003_unofficial #1941: [9/70, 4/15, 77/2, 5/11, 4/7]

Vector representation:
```
-1  2 -1 -1  0
 2 -1 -1  0  0
-1  0  0  1  1
 0  0  1  0 -1
 2  0  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1941

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | _ => none

-- R4 chain: (0,0,c,d,k) →* (0,0,c+k,d,0)
theorem r4_chain : ∀ k d c, ⟨(0 : ℕ), (0 : ℕ), c, d, k⟩ [fm]⊢*
    ⟨(0 : ℕ), (0 : ℕ), c + k, d, (0 : ℕ)⟩ := by
  intro k; induction' k with k ih <;> intro d c
  · exists 0
  · apply stepStar_trans
    · apply step_stepStar
      show fm ⟨0, 0, c, d, k + 1⟩ = some ⟨0, 0, c + 1, d, k⟩
      simp [fm]
    rw [show c + (k + 1) = (c + 1) + k from by ring]
    exact ih d (c + 1)

-- R1R1R2 chain: k rounds. (2,0,c+3k,d+2k,0) →* (2,3k,c,d,0)
theorem r1r1r2_chain : ∀ k c d, ⟨(2 : ℕ), (0 : ℕ), c + 3 * k, d + 2 * k, (0 : ℕ)⟩ [fm]⊢*
    ⟨(2 : ℕ), 3 * k, c, d, (0 : ℕ)⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show c + 3 * (k + 1) = (c + 3) + 3 * k from by ring,
        show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring]
    apply stepStar_trans (ih (c + 3) (d + 2))
    rw [show 3 * (k + 1) = 3 * k + 3 from by ring]
    step fm; step fm; step fm; finish

-- Drain: k rounds. (0,b+k,0,d,e+1) →* (0,b,0,d+2k,e+1+k)
theorem drain : ∀ k b d e, ⟨(0 : ℕ), b + k, (0 : ℕ), d, e + 1⟩ [fm]⊢*
    ⟨(0 : ℕ), b, (0 : ℕ), d + 2 * k, e + 1 + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · apply stepStar_trans
    · apply step_stepStar
      show fm ⟨0, (b + k) + 1, 0, d, e + 1⟩ = some ⟨0, (b + k) + 1, 1, d, e⟩
      simp [fm]
    apply stepStar_trans
    · apply step_stepStar
      show fm ⟨0, (b + k) + 1, 1, d, e⟩ = some ⟨2, b + k, 0, d, e⟩
      simp [fm]
    apply stepStar_trans
    · apply step_stepStar
      show fm ⟨2, b + k, 0, d, e⟩ = some ⟨1, b + k, 0, d + 1, e + 1⟩
      simp [fm]
    apply stepStar_trans
    · apply step_stepStar
      show fm ⟨1, b + k, 0, d + 1, e + 1⟩ = some ⟨0, b + k, 0, d + 2, e + 2⟩
      simp [fm]
    rw [show e + 2 = (e + 1) + 1 from by ring]
    apply stepStar_trans (ih b (d + 2) (e + 1))
    ring_nf; finish

-- Macro transition for e ≡ 0 (mod 3): e = 3m.
-- (0,0,0,D+2m+1,3m) →⁺ (0,0,0,D+6m+2,3m+2)
-- Phases: R4(3m), R5, R1R1R2(m), R3, R3, drain(3m)
theorem trans_mod0 (m D : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), D + 2 * m + 1, 3 * m⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), D + 6 * m + 2, 3 * m + 2⟩ := by
  apply stepStar_stepPlus
  · -- R4 x 3m: → (0,0,3m,D+2m+1,0)
    have h1 := r4_chain (3 * m) (D + 2 * m + 1) 0
    simp only [Nat.zero_add] at h1
    apply stepStar_trans h1
    -- R5: → (2,0,3m,D+2m,0)
    apply stepStar_trans
      (step_stepStar (show (⟨0, 0, 3 * m, (D + 2 * m) + 1, 0⟩ : Q) [fm]⊢ ⟨2, 0, 3 * m, D + 2 * m, 0⟩ from by simp [fm]))
    -- R1R1R2 x m: → (2,3m,0,D,0)
    have h2 := r1r1r2_chain m 0 D
    simp only [Nat.zero_add] at h2
    apply stepStar_trans h2
    -- R3: → (1,3m,0,D+1,1)
    apply stepStar_trans
      (step_stepStar (show (⟨(2 : ℕ), 3 * m, 0, D, 0⟩ : Q) [fm]⊢ ⟨1, 3 * m, 0, D + 1, 1⟩ from by simp [fm]))
    -- R3: → (0,3m,0,D+2,2)
    apply stepStar_trans
      (step_stepStar (show (⟨(1 : ℕ), 3 * m, 0, D + 1, 1⟩ : Q) [fm]⊢ ⟨0, 3 * m, 0, D + 2, 2⟩ from by simp [fm]))
    -- Drain x 3m: → (0,0,0,D+6m+2,3m+2)
    have h3 := drain (3 * m) 0 (D + 2) 1
    simp only [Nat.zero_add] at h3
    apply stepStar_trans h3
    ring_nf; finish
  · intro h; simp only [Q, Prod.mk.injEq] at h; omega

-- Macro transition for e ≡ 2 (mod 3): e = 3m+2.
-- (0,0,0,D+2m+4,3m+2) →⁺ (0,0,0,D+6m+10,3m+6)
-- Phases: R4(3m+2), R5, R1R1R2(m), R1, R1, R5, R3, R3, drain(3m+4)
theorem trans_mod2 (m D : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), D + 2 * m + 4, 3 * m + 2⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), D + 6 * m + 10, 3 * m + 6⟩ := by
  apply stepStar_stepPlus
  · have h1 := r4_chain (3 * m + 2) (D + 2 * m + 4) 0
    simp only [Nat.zero_add] at h1
    apply stepStar_trans h1
    apply stepStar_trans
      (step_stepStar (show (⟨0, 0, 3 * m + 2, (D + 2 * m + 3) + 1, 0⟩ : Q) [fm]⊢
        ⟨2, 0, 3 * m + 2, D + 2 * m + 3, 0⟩ from by simp [fm]))
    have h2 : (⟨(2 : ℕ), (0 : ℕ), 2 + 3 * m, (D + 3) + 2 * m, (0 : ℕ)⟩ : Q) [fm]⊢*
        ⟨(2 : ℕ), 3 * m, 2, D + 3, (0 : ℕ)⟩ := r1r1r2_chain m 2 (D + 3)
    rw [show 2 + 3 * m = 3 * m + 2 from by ring,
        show (D + 3) + 2 * m = D + 2 * m + 3 from by ring] at h2
    apply stepStar_trans h2
    apply stepStar_trans
      (step_stepStar (show (⟨(2 : ℕ), 3 * m, 2, (D + 2) + 1, 0⟩ : Q) [fm]⊢
        ⟨1, 3 * m + 2, 1, D + 2, 0⟩ from by simp [fm]))
    apply stepStar_trans
      (step_stepStar (show (⟨(1 : ℕ), 3 * m + 2, 1, (D + 1) + 1, 0⟩ : Q) [fm]⊢
        ⟨0, 3 * m + 4, 0, D + 1, 0⟩ from by simp [fm]))
    apply stepStar_trans
      (step_stepStar (show (⟨0, 3 * m + 4, 0, D + 1, 0⟩ : Q) [fm]⊢
        ⟨2, 3 * m + 4, 0, D, 0⟩ from by simp [fm]))
    apply stepStar_trans
      (step_stepStar (show (⟨(2 : ℕ), 3 * m + 4, 0, D, 0⟩ : Q) [fm]⊢
        ⟨1, 3 * m + 4, 0, D + 1, 1⟩ from by simp [fm]))
    apply stepStar_trans
      (step_stepStar (show (⟨(1 : ℕ), 3 * m + 4, 0, D + 1, 1⟩ : Q) [fm]⊢
        ⟨0, 3 * m + 4, 0, D + 2, 2⟩ from by simp [fm]))
    have h3 := drain (3 * m + 4) 0 (D + 2) 1
    simp only [Nat.zero_add] at h3
    apply stepStar_trans h3
    ring_nf; finish
  · intro h; simp only [Q, Prod.mk.injEq] at h; omega

-- Macro transition for e ≡ 1 (mod 3): e = 3m+1.
-- (0,0,0,D+2m+3,3m+1) →⁺ (0,0,0,D+6m+6,3m+3)
-- Phases: R4(3m+1), R5, R1R1R2(m), R1, R3, drain(3m+2)
theorem trans_mod1 (m D : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), D + 2 * m + 3, 3 * m + 1⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), D + 6 * m + 6, 3 * m + 3⟩ := by
  apply stepStar_stepPlus
  · have h1 := r4_chain (3 * m + 1) (D + 2 * m + 3) 0
    simp only [Nat.zero_add] at h1
    apply stepStar_trans h1
    apply stepStar_trans
      (step_stepStar (show (⟨0, 0, 3 * m + 1, (D + 2 * m + 2) + 1, 0⟩ : Q) [fm]⊢
        ⟨2, 0, 3 * m + 1, D + 2 * m + 2, 0⟩ from by simp [fm]))
    have h2 : (⟨(2 : ℕ), (0 : ℕ), 1 + 3 * m, (D + 2) + 2 * m, (0 : ℕ)⟩ : Q) [fm]⊢*
        ⟨(2 : ℕ), 3 * m, 1, D + 2, (0 : ℕ)⟩ := r1r1r2_chain m 1 (D + 2)
    rw [show 1 + 3 * m = 3 * m + 1 from by ring,
        show (D + 2) + 2 * m = D + 2 * m + 2 from by ring] at h2
    apply stepStar_trans h2
    apply stepStar_trans
      (step_stepStar (show (⟨(2 : ℕ), 3 * m, 1, (D + 1) + 1, 0⟩ : Q) [fm]⊢
        ⟨1, 3 * m + 2, 0, D + 1, 0⟩ from by simp [fm]))
    apply stepStar_trans
      (step_stepStar (show (⟨(1 : ℕ), 3 * m + 2, 0, D + 1, 0⟩ : Q) [fm]⊢
        ⟨0, 3 * m + 2, 0, D + 2, 1⟩ from by simp [fm]))
    have h3 := drain (3 * m + 2) 0 (D + 2) 0
    simp only [Nat.zero_add] at h3
    apply stepStar_trans h3
    ring_nf; finish
  · intro h; simp only [Q, Prod.mk.injEq] at h; omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 9, 5⟩) (by execute fm 34)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ e ≥ 3 ∧ 3 * d ≥ 2 * e + 8)
  · intro c ⟨d, e, hq, he, hd⟩; subst hq
    have h3 : e % 3 < 3 := Nat.mod_lt _ (by omega)
    obtain ⟨k, hk⟩ : ∃ k, e = 3 * k + e % 3 := ⟨e / 3, by omega⟩
    interval_cases (e % 3)
    · rw [Nat.add_zero] at hk; subst hk
      obtain ⟨D, rfl⟩ : ∃ D, d = D + 2 * k + 1 := ⟨d - 2 * k - 1, by omega⟩
      exact ⟨⟨0, 0, 0, D + 6 * k + 2, 3 * k + 2⟩,
        ⟨D + 6 * k + 2, 3 * k + 2, rfl, by omega, by omega⟩, trans_mod0 k D⟩
    · subst hk
      obtain ⟨D, rfl⟩ : ∃ D, d = D + 2 * k + 3 := ⟨d - 2 * k - 3, by omega⟩
      exact ⟨⟨0, 0, 0, D + 6 * k + 6, 3 * k + 3⟩,
        ⟨D + 6 * k + 6, 3 * k + 3, rfl, by omega, by omega⟩, trans_mod1 k D⟩
    · subst hk
      obtain ⟨D, rfl⟩ : ∃ D, d = D + 2 * k + 4 := ⟨d - 2 * k - 4, by omega⟩
      exact ⟨⟨0, 0, 0, D + 6 * k + 10, 3 * k + 6⟩,
        ⟨D + 6 * k + 10, 3 * k + 6, rfl, by omega, by omega⟩, trans_mod2 k D⟩
  · exact ⟨9, 5, rfl, by omega, by omega⟩
