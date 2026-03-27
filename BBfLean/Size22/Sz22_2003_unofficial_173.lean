import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz22_2003_unofficial #173: [1/45, 98/15, 3/7, 3025/2, 7/11]

Vector representation:
```
 0 -2 -1  0  0
 1 -1 -1  2  0
 0  1  0 -1  0
-1  0  2  0  2
 0  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_173

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

theorem d_to_b : ∀ k, ∀ a b e,
    (⟨a, b, 0, k, e⟩ : Q) [fm]⊢* ⟨a, b + k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  rw [show (k + 1 : ℕ) = k + 1 from rfl]
  step fm
  rw [show b + (k + 1) = (b + 1) + k from by ring]
  exact ih _ _ _

theorem rule4_drain : ∀ k, ∀ c e,
    (⟨k, 0, c, 0, e⟩ : Q) [fm]⊢* ⟨0, 0, c + 2 * k, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  rw [show (k + 1 : ℕ) = k + 1 from rfl]
  step fm
  rw [show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring,
      show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring]
  exact ih _ _

theorem pump_r2r3 : ∀ k, ∀ a c e,
    (⟨a, 1, c + k + 1, a, e⟩ : Q) [fm]⊢* ⟨a + k, 1, c + 1, a + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  rw [show c + (k + 1) + 1 = (c + k + 1) + 1 from by ring]
  step fm; step fm
  rw [show a + (k + 1) = (a + 1) + k from by ring]
  exact ih _ _ _

theorem lifting : ∀ c e,
    (⟨0, 0, c + 1, 0, e + 1⟩ : Q) [fm]⊢* ⟨c + 1, c + 2, 0, 0, e⟩ := by
  intro c e
  step fm; step fm
  apply stepStar_trans
  · have h := pump_r2r3 c 0 0 e
    simp only [Nat.zero_add] at h; exact h
  step fm
  have h := d_to_b (c + 2) (c + 1) 0 e
  simp only [Nat.zero_add] at h; exact h

theorem drain4 : ∀ a b e,
    (⟨a + 1, b + 4, 0, 0, e⟩ : Q) [fm]⊢* ⟨a, b, 0, 0, e + 2⟩ := by
  intro a b e; step fm; step fm; step fm; finish

theorem drain4_repeat : ∀ k, ∀ a b e,
    (⟨a + k, b + 4 * k, 0, 0, e⟩ : Q) [fm]⊢* ⟨a, b, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show b + 4 * (k + 1) = (b + 4 * k) + 4 from by ring]
  apply stepStar_trans (drain4 _ _ _)
  rw [show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring]
  exact ih _ _ _

theorem b1_handle : ∀ a e,
    (⟨a + 1, 1, 0, 0, e⟩ : Q) [fm]⊢* ⟨a + 2, 3, 0, 0, e + 2⟩ := by
  intro a e; step fm; step fm; step fm; step fm; step fm; step fm; step fm; finish

theorem b3_handle : ∀ a e,
    (⟨a + 1, 3, 0, 0, e⟩ : Q) [fm]⊢* ⟨a + 1, 2, 0, 0, e + 2⟩ := by
  intro a e; step fm; step fm; step fm; step fm; step fm; finish

theorem b2_handle : ∀ a e,
    (⟨a + 1, 2, 0, 0, e⟩ : Q) [fm]⊢* ⟨0, 0, 2 * a + 1, 0, e + 2 * a + 2⟩ := by
  intro a e
  step fm; step fm
  have h := rule4_drain a 1 (e + 2)
  rw [show 1 + 2 * a = 2 * a + 1 from by ring,
      show e + 2 + 2 * a = e + 2 * a + 2 from by ring] at h
  exact h

-- c = 4(k+1): lifting -> drain (k+1) -> b1 -> b3 -> b2
theorem trans_mod0 (k : ℕ) (E : ℕ) (hE : E ≥ 1) :
    (⟨0, 0, 4 * (k + 1), 0, E⟩ : Q) [fm]⊢⁺ ⟨0, 0, 6 * (k + 1) + 1, 0, E + 8 * (k + 1) + 5⟩ := by
  obtain ⟨E', rfl⟩ := Nat.exists_eq_add_of_le hE
  rw [show (1 : ℕ) + E' = E' + 1 from by ring,
      show 4 * (k + 1) = (4 * k + 3) + 1 from by ring]
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  -- After first step (rule 5): (0, 0, 4k+3+1, 1, E')
  step fm  -- rule 3: (0, 1, 4k+3+1, 0, E')
  apply stepStar_trans
  · have h := pump_r2r3 (4 * k + 3) 0 0 E'
    simp only [Nat.zero_add] at h
    exact h
  -- (4k+3, 1, 1, 4k+3, E'). Rule 2: (4k+4, 0, 0, 4k+5, E').
  step fm
  apply stepStar_trans
  · have h := d_to_b (4 * k + 5) (4 * k + 4) 0 E'
    simp only [Nat.zero_add] at h; exact h
  -- (4k+4, 4k+5, 0, 0, E'). drain (k+1) times to (3k+3, 1, 0, 0, E'+2k+2).
  apply stepStar_trans
  · have h := drain4_repeat (k + 1) (3 * k + 3) 1 E'
    rw [show 3 * k + 3 + (k + 1) = 4 * k + 4 from by ring,
        show 1 + 4 * (k + 1) = 4 * k + 5 from by ring,
        show E' + 2 * (k + 1) = E' + 2 * k + 2 from by ring] at h
    exact h
  -- b1: (3k+3, 1, 0, 0, E'+2k+2) -> (3k+4, 3, 0, 0, E'+2k+4)
  apply stepStar_trans
  · have h := b1_handle (3 * k + 2) (E' + 2 * k + 2)
    rw [show 3 * k + 2 + 1 = 3 * k + 3 from by ring,
        show 3 * k + 2 + 2 = 3 * k + 4 from by ring,
        show E' + 2 * k + 2 + 2 = E' + 2 * k + 4 from by ring] at h
    exact h
  -- b3: (3k+4, 3, 0, 0, E'+2k+4) -> (3k+4, 2, 0, 0, E'+2k+6)
  apply stepStar_trans
  · have h := b3_handle (3 * k + 3) (E' + 2 * k + 4)
    rw [show 3 * k + 3 + 1 = 3 * k + 4 from by ring,
        show E' + 2 * k + 4 + 2 = E' + 2 * k + 6 from by ring] at h
    exact h
  -- b2: (3k+4, 2, 0, 0, E'+2k+6) -> (0, 0, 6k+7, 0, E'+8k+14)
  have h := b2_handle (3 * k + 3) (E' + 2 * k + 6)
  rw [show 2 * (3 * k + 3) + 1 = 6 * (k + 1) + 1 from by ring,
      show E' + 2 * k + 6 + 2 * (3 * k + 3) + 2 = (E' + 1) + 8 * (k + 1) + 5 from by ring] at h
  ring_nf; ring_nf at h; exact h

-- c = 4k+1: lifting -> drain k -> b2
theorem trans_mod1 (k : ℕ) (E : ℕ) (hE : E ≥ 1) :
    (⟨0, 0, 4 * k + 1, 0, E⟩ : Q) [fm]⊢⁺ ⟨0, 0, 6 * k + 1, 0, E + 8 * k + 1⟩ := by
  obtain ⟨E', rfl⟩ := Nat.exists_eq_add_of_le hE
  rw [show (1 : ℕ) + E' = E' + 1 from by ring]
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  step fm
  apply stepStar_trans
  · have h := pump_r2r3 (4 * k) 0 0 E'
    simp only [Nat.zero_add] at h; exact h
  step fm
  apply stepStar_trans
  · have h := d_to_b (4 * k + 2) (4 * k + 1) 0 E'
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_trans
  · have h := drain4_repeat k (3 * k + 1) 2 E'
    rw [show 3 * k + 1 + k = 4 * k + 1 from by ring,
        show 2 + 4 * k = 4 * k + 2 from by ring] at h
    exact h
  have h := b2_handle (3 * k) (E' + 2 * k)
  rw [show 2 * (3 * k) + 1 = 6 * k + 1 from by ring,
      show E' + 2 * k + 2 * (3 * k) + 2 = (E' + 1) + 8 * k + 1 from by ring] at h
  ring_nf; ring_nf at h; exact h

-- c = 4k+2: lifting -> drain k -> b3 -> b2
theorem trans_mod2 (k : ℕ) (E : ℕ) (hE : E ≥ 1) :
    (⟨0, 0, 4 * k + 2, 0, E⟩ : Q) [fm]⊢⁺ ⟨0, 0, 6 * k + 3, 0, E + 8 * k + 5⟩ := by
  obtain ⟨E', rfl⟩ := Nat.exists_eq_add_of_le hE
  rw [show (1 : ℕ) + E' = E' + 1 from by ring]
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  step fm
  apply stepStar_trans
  · have h := pump_r2r3 (4 * k + 1) 0 0 E'
    simp only [Nat.zero_add] at h
    rw [show (4 * k + 1) + 1 = 4 * k + 2 from by ring] at h
    exact h
  step fm
  apply stepStar_trans
  · have h := d_to_b (4 * k + 3) (4 * k + 2) 0 E'
    simp only [Nat.zero_add] at h; exact h
  -- (4k+2, 4k+3, 0, 0, E'). drain k times to (3k+2, 3, 0, 0, E'+2k).
  apply stepStar_trans
  · have h := drain4_repeat k (3 * k + 2) 3 E'
    rw [show 3 * k + 2 + k = 4 * k + 2 from by ring,
        show 3 + 4 * k = 4 * k + 3 from by ring] at h
    exact h
  -- b3: (3k+2, 3, 0, 0, E'+2k) -> (3k+2, 2, 0, 0, E'+2k+2)
  apply stepStar_trans
  · have h := b3_handle (3 * k + 1) (E' + 2 * k)
    rw [show 3 * k + 1 + 1 = 3 * k + 2 from by ring,
        show E' + 2 * k + 2 = E' + 2 * k + 2 from rfl] at h
    exact h
  -- b2: (3k+2, 2, 0, 0, E'+2k+2) -> (0, 0, 6k+3, 0, E'+8k+6)
  have h := b2_handle (3 * k + 1) (E' + 2 * k + 2)
  rw [show 2 * (3 * k + 1) + 1 = 6 * k + 3 from by ring,
      show E' + 2 * k + 2 + 2 * (3 * k + 1) + 2 = (E' + 1) + 8 * k + 5 from by ring] at h
  ring_nf; ring_nf at h; exact h

-- c = 4k+3: lifting -> drain (k+1) -> rule4_drain
theorem trans_mod3 (k : ℕ) (E : ℕ) (hE : E ≥ 1) :
    (⟨0, 0, 4 * k + 3, 0, E⟩ : Q) [fm]⊢⁺ ⟨0, 0, 6 * k + 4, 0, E + 8 * k + 5⟩ := by
  obtain ⟨E', rfl⟩ := Nat.exists_eq_add_of_le hE
  rw [show (1 : ℕ) + E' = E' + 1 from by ring]
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  step fm
  apply stepStar_trans
  · have h := pump_r2r3 (4 * k + 2) 0 0 E'
    simp only [Nat.zero_add] at h
    rw [show (4 * k + 2) + 1 = 4 * k + 3 from by ring] at h
    exact h
  step fm
  apply stepStar_trans
  · have h := d_to_b (4 * k + 4) (4 * k + 3) 0 E'
    simp only [Nat.zero_add] at h; exact h
  -- (4k+3, 4k+4, 0, 0, E'). drain (k+1) times to (3k+2, 0, 0, 0, E'+2k+2).
  apply stepStar_trans
  · have h := drain4_repeat (k + 1) (3 * k + 2) 0 E'
    rw [show 3 * k + 2 + (k + 1) = 4 * k + 3 from by ring,
        show 0 + 4 * (k + 1) = 4 * k + 4 from by ring,
        show E' + 2 * (k + 1) = E' + 2 * k + 2 from by ring] at h
    exact h
  -- rule4_drain: (3k+2, 0, 0, 0, E'+2k+2) -> (0, 0, 6k+4, 0, E'+8k+6)
  have h := rule4_drain (3 * k + 2) 0 (E' + 2 * k + 2)
  rw [show 0 + 2 * (3 * k + 2) = 6 * k + 4 from by ring,
      show E' + 2 * k + 2 + 2 * (3 * k + 2) = (E' + 1) + 8 * k + 5 from by ring] at h
  ring_nf; ring_nf at h; exact h

theorem main_trans : ∀ c E, c ≥ 1 → E ≥ 1 →
    ∃ c' E', c' ≥ 1 ∧ E' ≥ 1 ∧ (⟨0, 0, c, 0, E⟩ : Q) [fm]⊢⁺ ⟨0, 0, c', 0, E'⟩ := by
  intro c E hc hE
  have hmod := Nat.div_add_mod c 4
  set q := c / 4
  set r := c % 4
  have hr : r < 4 := Nat.mod_lt c (by omega)
  interval_cases r
  · -- c = 4q, q ≥ 1
    have hq : q ≥ 1 := by omega
    obtain ⟨q', hq'⟩ := Nat.exists_eq_add_of_le hq
    rw [show c = 4 * (q' + 1) from by omega]
    exact ⟨6 * (q' + 1) + 1, E + 8 * (q' + 1) + 5, by omega, by omega, trans_mod0 q' E hE⟩
  · -- c = 4q + 1
    rw [show c = 4 * q + 1 from by omega]
    exact ⟨6 * q + 1, E + 8 * q + 1, by omega, by omega, trans_mod1 q E hE⟩
  · -- c = 4q + 2
    rw [show c = 4 * q + 2 from by omega]
    exact ⟨6 * q + 3, E + 8 * q + 5, by omega, by omega, trans_mod2 q E hE⟩
  · -- c = 4q + 3
    rw [show c = 4 * q + 3 from by omega]
    exact ⟨6 * q + 4, E + 8 * q + 5, by omega, by omega, trans_mod3 q E hE⟩

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c E, q = ⟨0, 0, c, 0, E⟩ ∧ c ≥ 1 ∧ E ≥ 1)
  · intro q ⟨c, E, hq, hc, hE⟩
    subst hq
    obtain ⟨c', E', hc', hE', htrans⟩ := main_trans c E hc hE
    exact ⟨⟨0, 0, c', 0, E'⟩, ⟨c', E', rfl, hc', hE'⟩, htrans⟩
  · exact ⟨2, 2, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_173
