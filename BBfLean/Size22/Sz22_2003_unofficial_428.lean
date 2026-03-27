import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #428: [27/10, 77/2, 4/21, 5/7, 14/11]

Vector representation:
```
-1  3 -1  0  0
-1  0  0  1  1
 2 -1  0 -1  0
 0  0  1 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_428

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

theorem d_to_c : ∀ j c e,
    ⟨0, 0, c, j, e⟩ [fm]⊢* ⟨0, 0, c + j, 0, e⟩ := by
  intro j; induction j with
  | zero => intro c e; simp; exists 0
  | succ j ih =>
    intro c e
    step fm
    have := ih (c + 1) e
    rw [show c + 1 + j = c + (j + 1) from by ring] at this
    exact this

theorem eat3 : ∀ b c e,
    ⟨0, b, c + 3, 0, e + 1⟩ [fm]⊢* ⟨0, b + 8, c, 0, e⟩ := by
  intro b c e
  step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

theorem eat3_iter : ∀ j b c e,
    ⟨0, b, c + 3 * j, 0, e + j⟩ [fm]⊢* ⟨0, b + 8 * j, c, 0, e⟩ := by
  intro j; induction j with
  | zero => intro b c e; simp; exists 0
  | succ j ih =>
    intro b c e
    rw [show c + 3 * (j + 1) = (c + 3 * j) + 3 from by ring,
        show e + (j + 1) = (e + j) + 1 from by ring]
    apply stepStar_trans (eat3 _ _ _)
    have := ih (b + 8) c e
    rw [show b + 8 + 8 * j = b + 8 * (j + 1) from by ring] at this
    exact this

theorem tail_c0 : ∀ b e,
    ⟨0, b, 0, 0, e + 1⟩ [fm]⊢* ⟨0, b, 0, 2, e + 1⟩ := by
  intro b e; step fm; step fm; finish

theorem tail_c1 : ∀ b e,
    ⟨0, b, 1, 0, e + 1⟩ [fm]⊢* ⟨0, b + 2, 0, 2, e + 2⟩ := by
  intro b e; step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

theorem tail_c2 : ∀ b e,
    ⟨0, b, 2, 0, e + 1⟩ [fm]⊢* ⟨0, b + 4, 0, 2, e + 3⟩ := by
  intro b e; step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

theorem b_drain : ∀ j b d e,
    ⟨0, b + j, 0, d + 1, e⟩ [fm]⊢* ⟨0, b, 0, d + 1 + j, e + 2 * j⟩ := by
  intro j; induction j with
  | zero => intro b d e; simp; exists 0
  | succ j ih =>
    intro b d e
    rw [show b + (j + 1) = (b + j) + 1 from by ring]
    step fm; step fm; step fm
    have := ih b (d + 1) (e + 2)
    rw [show d + 1 + 1 + j = d + 1 + (j + 1) from by ring,
        show e + 2 + 2 * j = e + 2 * (j + 1) from by ring] at this
    exact this

-- D = 3k+1 case (d = 3k)
theorem cycle_mod0 (k m : ℕ) :
    ⟨0, 0, 0, 3 * k + 1, m + k + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 8 * k + 4, m + 16 * k + 6⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, 3 * k + 1, m + k + 1⟩ = some ⟨0, 0, 1, 3 * k, m + k + 1⟩
    simp [fm]
  apply stepStar_trans
  · have := d_to_c (3 * k) 1 (m + k + 1)
    rw [show 1 + 3 * k = 3 * k + 1 from by ring] at this; exact this
  apply stepStar_trans
  · have := eat3_iter k 0 1 (m + 1)
    rw [show 1 + 3 * k = 3 * k + 1 from by ring,
        show m + 1 + k = m + k + 1 from by ring,
        show 0 + 8 * k = 8 * k from by ring] at this; exact this
  apply stepStar_trans (tail_c1 (8 * k) m)
  have := b_drain (8 * k + 2) 0 1 (m + 2)
  rw [show 0 + (8 * k + 2) = 8 * k + 2 from by ring,
      show 1 + 1 + (8 * k + 2) = 8 * k + 4 from by ring,
      show m + 2 + 2 * (8 * k + 2) = m + 16 * k + 6 from by ring] at this; exact this

-- D = 3k+2 case (d = 3k+1)
theorem cycle_mod1 (k m : ℕ) :
    ⟨0, 0, 0, 3 * k + 2, m + k + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 8 * k + 6, m + 16 * k + 11⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, 3 * k + 2, m + k + 1⟩ = some ⟨0, 0, 1, 3 * k + 1, m + k + 1⟩
    simp [fm]
  apply stepStar_trans
  · have := d_to_c (3 * k + 1) 1 (m + k + 1)
    rw [show 1 + (3 * k + 1) = 3 * k + 2 from by ring] at this; exact this
  apply stepStar_trans
  · have := eat3_iter k 0 2 (m + 1)
    rw [show 2 + 3 * k = 3 * k + 2 from by ring,
        show m + 1 + k = m + k + 1 from by ring,
        show 0 + 8 * k = 8 * k from by ring] at this; exact this
  apply stepStar_trans (tail_c2 (8 * k) m)
  have := b_drain (8 * k + 4) 0 1 (m + 3)
  rw [show 0 + (8 * k + 4) = 8 * k + 4 from by ring,
      show 1 + 1 + (8 * k + 4) = 8 * k + 6 from by ring,
      show m + 3 + 2 * (8 * k + 4) = m + 16 * k + 11 from by ring] at this; exact this

-- D = 3(k+1) case (d = 3k+2)
theorem cycle_mod2 (k m : ℕ) :
    ⟨0, 0, 0, 3 * k + 3, m + k + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 8 * k + 10, m + 16 * k + 17⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, 3 * k + 3, m + k + 2⟩ = some ⟨0, 0, 1, 3 * k + 2, m + k + 2⟩
    simp [fm]
  apply stepStar_trans
  · have := d_to_c (3 * k + 2) 1 (m + k + 2)
    rw [show 1 + (3 * k + 2) = 3 * k + 3 from by ring] at this; exact this
  apply stepStar_trans
  · have := eat3_iter (k + 1) 0 0 (m + 1)
    rw [show 0 + 3 * (k + 1) = 3 * k + 3 from by ring,
        show m + 1 + (k + 1) = m + k + 2 from by ring,
        show 0 + 8 * (k + 1) = 8 * k + 8 from by ring] at this; exact this
  apply stepStar_trans (tail_c0 (8 * k + 8) m)
  have := b_drain (8 * k + 8) 0 1 (m + 1)
  rw [show 0 + (8 * k + 8) = 8 * k + 8 from by ring,
      show 1 + 1 + (8 * k + 8) = 8 * k + 10 from by ring,
      show m + 1 + 2 * (8 * k + 8) = m + 16 * k + 17 from by ring] at this; exact this

private lemma nat_mod3 (n : ℕ) :
    (∃ k, n = 3 * k) ∨ (∃ k, n = 3 * k + 1) ∨ (∃ k, n = 3 * k + 2) := by
  have h : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h with h | h | h
  · left; exact ⟨n / 3, by omega⟩
  · right; left; exact ⟨n / 3, by omega⟩
  · right; right; exact ⟨n / 3, by omega⟩

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d + 1, e + 1⟩ ∧ e ≥ d)
  · intro c ⟨d, e, hq, hge⟩; subst hq
    rcases nat_mod3 d with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
    · obtain ⟨m, rfl⟩ : ∃ m, e = m + k := ⟨e - k, by omega⟩
      exact ⟨⟨0, 0, 0, 8 * k + 4, m + 16 * k + 6⟩,
             ⟨8 * k + 3, m + 16 * k + 5, rfl, by omega⟩,
             cycle_mod0 k m⟩
    · obtain ⟨m, rfl⟩ : ∃ m, e = m + k := ⟨e - k, by omega⟩
      exact ⟨⟨0, 0, 0, 8 * k + 6, m + 16 * k + 11⟩,
             ⟨8 * k + 5, m + 16 * k + 10, rfl, by omega⟩,
             cycle_mod1 k m⟩
    · obtain ⟨m, rfl⟩ : ∃ m, e = m + k + 1 := ⟨e - k - 1, by omega⟩
      exact ⟨⟨0, 0, 0, 8 * k + 10, m + 16 * k + 17⟩,
             ⟨8 * k + 9, m + 16 * k + 16, rfl, by omega⟩,
             cycle_mod2 k m⟩
  · exact ⟨0, 0, rfl, by omega⟩

end Sz22_2003_unofficial_428
