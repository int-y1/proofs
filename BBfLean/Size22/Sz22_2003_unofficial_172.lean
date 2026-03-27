import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #172: [1/45, 98/15, 3/7, 3025/2, 3/11]

Vector representation:
```
 0 -2 -1  0  0
 1 -1 -1  2  0
 0  1  0 -1  0
-1  0  2  0  2
 0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_172

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem d_to_b : ∀ j a b e,
    ⟨a, b, 0, j, e⟩ [fm]⊢* ⟨a, b+j, 0, 0, e⟩ := by
  intro j; induction' j with j ih <;> intro a b e
  · exists 0
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

theorem r4_chain : ∀ j c e,
    ⟨j, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c+2*j, 0, e+2*j⟩ := by
  intro j; induction' j with j ih <;> intro c e
  · exists 0
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

theorem climb_r2r3 : ∀ j a d e,
    ⟨a, 0, j+1, d+1, e⟩ [fm]⊢* ⟨a+j+1, 0, 0, d+j+2, e⟩ := by
  intro j; induction' j with j ih <;> intro a d e
  · step fm; step fm; finish
  step fm; step fm
  apply stepStar_trans (ih (a + 1) (d + 1) e)
  ring_nf; finish

theorem full_climb : ∀ c e,
    ⟨0, 0, c+2, 0, e+1⟩ [fm]⊢* ⟨c+2, c+3, 0, 0, e⟩ := by
  intro c e
  step fm -- R5
  step fm -- R2
  apply stepStar_trans (climb_r2r3 c 1 1 e)
  have h := d_to_b (c + 3) (c + 2) 0 e
  simp only [Nat.zero_add] at h
  rw [show 1 + c + 1 = c + 2 from by ring,
      show 1 + c + 2 = c + 3 from by ring]
  exact h

theorem descent_round : ∀ a b e,
    ⟨a+1, b+4, 0, 0, e⟩ [fm]⊢* ⟨a, b, 0, 0, e+2⟩ := by
  intro a b e
  step fm; step fm; step fm; finish

theorem descent_iter : ∀ j a b e,
    ⟨a+j, b+4*j, 0, 0, e⟩ [fm]⊢* ⟨a, b, 0, 0, e+2*j⟩ := by
  intro j; induction' j with j ih <;> intro a b e
  · exists 0
  rw [show a + (j + 1) = (a + j) + 1 from by ring,
      show b + 4 * (j + 1) = (b + 4 * j) + 4 from by ring]
  apply stepStar_trans (descent_round _ _ _)
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

theorem tail_b1 : ∀ a e,
    ⟨a+1, 1, 0, 0, e⟩ [fm]⊢* ⟨a+2, 3, 0, 0, e+2⟩ := by
  intro a e
  step fm; step fm; step fm; step fm
  have h := d_to_b 3 (a + 2) 0 (e + 2)
  simp only [Nat.zero_add] at h; exact h

theorem tail_b3 : ∀ a e,
    ⟨a+1, 3, 0, 0, e⟩ [fm]⊢* ⟨a+1, 2, 0, 0, e+2⟩ := by
  intro a e
  step fm; step fm; step fm
  have h := d_to_b 2 (a + 1) 0 (e + 2)
  simp only [Nat.zero_add] at h; exact h

-- c ≡ 2 (mod 4): c = 4m+2
theorem main_trans_r2 (m e : ℕ) :
    ⟨0, 0, 4*m+2, 0, e+2⟩ [fm]⊢⁺ ⟨0, 0, 6*m+3, 0, e+8*m+7⟩ := by
  -- Climb
  apply stepStar_stepPlus_stepPlus
  · have h := full_climb (4*m) (e+1)
    rw [show 4 * m + 2 = 4 * m + 2 from rfl,
        show e + 1 + 1 = e + 2 from by ring,
        show 4 * m + 3 = 4 * m + 3 from rfl] at h
    exact h
  -- Descent m rounds
  apply stepStar_stepPlus_stepPlus
  · have h := descent_iter m (3*m+2) 3 (e+1)
    rw [show 3 * m + 2 + m = 4 * m + 2 from by ring,
        show 3 + 4 * m = 4 * m + 3 from by ring,
        show e + 1 + 2 * m = e + 2 * m + 1 from by ring] at h
    exact h
  -- Tail b=3
  apply stepStar_stepPlus_stepPlus
  · have h := tail_b3 (3*m+1) (e+2*m+1)
    rw [show 3 * m + 1 + 1 = 3 * m + 2 from by ring,
        show e + 2 * m + 1 + 2 = e + 2 * m + 3 from by ring] at h
    exact h
  -- Tail b=2: (3m+2, 2, 0, 0, e+2m+3) -> R4 -> R1 -> r4_chain
  apply step_stepStar_stepPlus
  · show fm ⟨3*m+2, 2, 0, 0, e+2*m+3⟩ = some ⟨3*m+1, 2, 2, 0, e+2*m+5⟩; rfl
  step fm -- R1: (3m+1, 0, 1, 0, e+2m+5)
  have h := r4_chain (3*m+1) 1 (e+2*m+5)
  rw [show 1 + 2 * (3 * m + 1) = 6 * m + 3 from by ring,
      show e + 2 * m + 5 + 2 * (3 * m + 1) = e + 8 * m + 7 from by ring] at h
  exact h

-- c ≡ 3 (mod 4): c = 4m+3
theorem main_trans_r3 (m e : ℕ) :
    ⟨0, 0, 4*m+3, 0, e+2⟩ [fm]⊢⁺ ⟨0, 0, 6*m+4, 0, e+8*m+7⟩ := by
  apply stepStar_stepPlus_stepPlus
  · have h := full_climb (4*m+1) (e+1)
    rw [show 4 * m + 1 + 2 = 4 * m + 3 from by ring,
        show e + 1 + 1 = e + 2 from by ring,
        show 4 * m + 1 + 3 = 4 * m + 4 from by ring] at h
    exact h
  -- Descent m+1 rounds
  apply stepStar_stepPlus_stepPlus
  · have h := descent_iter (m+1) (3*m+2) 0 (e+1)
    rw [show 3 * m + 2 + (m + 1) = 4 * m + 3 from by ring,
        show 0 + 4 * (m + 1) = 4 * m + 4 from by ring,
        show e + 1 + 2 * (m + 1) = e + 2 * m + 3 from by ring] at h
    exact h
  -- Tail b=0: (3m+2, 0, 0, 0, e+2m+3) -> R4 -> r4_chain
  apply step_stepStar_stepPlus
  · show fm ⟨3*m+2, 0, 0, 0, e+2*m+3⟩ = some ⟨3*m+1, 0, 2, 0, e+2*m+5⟩; rfl
  have h := r4_chain (3*m+1) 2 (e+2*m+5)
  rw [show 2 + 2 * (3 * m + 1) = 6 * m + 4 from by ring,
      show e + 2 * m + 5 + 2 * (3 * m + 1) = e + 8 * m + 7 from by ring] at h
  exact h

-- c ≡ 0 (mod 4): c = 4m+4
theorem main_trans_r0 (m e : ℕ) :
    ⟨0, 0, 4*m+4, 0, e+2⟩ [fm]⊢⁺ ⟨0, 0, 6*m+7, 0, e+8*m+15⟩ := by
  apply stepStar_stepPlus_stepPlus
  · have h := full_climb (4*m+2) (e+1)
    rw [show 4 * m + 2 + 2 = 4 * m + 4 from by ring,
        show e + 1 + 1 = e + 2 from by ring,
        show 4 * m + 2 + 3 = 4 * m + 5 from by ring] at h
    exact h
  -- Descent m+1 rounds
  apply stepStar_stepPlus_stepPlus
  · have h := descent_iter (m+1) (3*m+3) 1 (e+1)
    rw [show 3 * m + 3 + (m + 1) = 4 * m + 4 from by ring,
        show 1 + 4 * (m + 1) = 4 * m + 5 from by ring,
        show e + 1 + 2 * (m + 1) = e + 2 * m + 3 from by ring] at h
    exact h
  -- Tail b=1
  apply stepStar_stepPlus_stepPlus
  · have h := tail_b1 (3*m+2) (e+2*m+3)
    rw [show 3 * m + 2 + 1 = 3 * m + 3 from by ring,
        show 3 * m + 2 + 2 = 3 * m + 4 from by ring,
        show e + 2 * m + 3 + 2 = e + 2 * m + 5 from by ring] at h
    exact h
  -- Tail b=3
  apply stepStar_stepPlus_stepPlus
  · have h := tail_b3 (3*m+3) (e+2*m+5)
    rw [show 3 * m + 3 + 1 = 3 * m + 4 from by ring,
        show e + 2 * m + 5 + 2 = e + 2 * m + 7 from by ring] at h
    exact h
  -- Tail b=2: (3m+4, 2, 0, 0, e+2m+7) -> R4 -> R1 -> r4_chain
  apply step_stepStar_stepPlus
  · show fm ⟨3*m+4, 2, 0, 0, e+2*m+7⟩ = some ⟨3*m+3, 2, 2, 0, e+2*m+9⟩; rfl
  step fm -- R1: (3m+3, 0, 1, 0, e+2m+9)
  have h := r4_chain (3*m+3) 1 (e+2*m+9)
  rw [show 1 + 2 * (3 * m + 3) = 6 * m + 7 from by ring,
      show e + 2 * m + 9 + 2 * (3 * m + 3) = e + 8 * m + 15 from by ring] at h
  exact h

-- c ≡ 1 (mod 4): c = 4m+5
theorem main_trans_r1 (m e : ℕ) :
    ⟨0, 0, 4*m+5, 0, e+2⟩ [fm]⊢⁺ ⟨0, 0, 6*m+7, 0, e+8*m+11⟩ := by
  apply stepStar_stepPlus_stepPlus
  · have h := full_climb (4*m+3) (e+1)
    rw [show 4 * m + 3 + 2 = 4 * m + 5 from by ring,
        show e + 1 + 1 = e + 2 from by ring,
        show 4 * m + 3 + 3 = 4 * m + 6 from by ring] at h
    exact h
  -- Descent m+1 rounds
  apply stepStar_stepPlus_stepPlus
  · have h := descent_iter (m+1) (3*m+4) 2 (e+1)
    rw [show 3 * m + 4 + (m + 1) = 4 * m + 5 from by ring,
        show 2 + 4 * (m + 1) = 4 * m + 6 from by ring,
        show e + 1 + 2 * (m + 1) = e + 2 * m + 3 from by ring] at h
    exact h
  -- Tail b=2: (3m+4, 2, 0, 0, e+2m+3) -> R4 -> R1 -> r4_chain
  apply step_stepStar_stepPlus
  · show fm ⟨3*m+4, 2, 0, 0, e+2*m+3⟩ = some ⟨3*m+3, 2, 2, 0, e+2*m+5⟩; rfl
  step fm -- R1: (3m+3, 0, 1, 0, e+2m+5)
  have h := r4_chain (3*m+3) 1 (e+2*m+5)
  rw [show 1 + 2 * (3 * m + 3) = 6 * m + 7 from by ring,
      show e + 2 * m + 5 + 2 * (3 * m + 3) = e + 8 * m + 11 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt (fun q ↦ ∃ c e, c ≥ 2 ∧ e ≥ 2 ∧ q = (⟨0, 0, c, 0, e⟩ : Q))
  · intro q ⟨c, e, hc, he, hq⟩
    subst hq
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 2 := ⟨e - 2, by omega⟩
    obtain ⟨k, rfl⟩ : ∃ k, c = k + 2 := ⟨c - 2, by omega⟩
    -- Case split on k mod 4
    obtain ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩ :
        (∃ m, k = 4*m) ∨ (∃ m, k = 4*m+1) ∨ (∃ m, k = 4*m+2) ∨ (∃ m, k = 4*m+3) := by
      have := Nat.div_add_mod k 4
      have h4 := Nat.mod_lt k (show 4 > 0 by omega)
      rcases h : k % 4 with _ | _ | _ | _ | n
      · exact Or.inl ⟨k / 4, by omega⟩
      · exact Or.inr (Or.inl ⟨k / 4, by omega⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨k / 4, by omega⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨k / 4, by omega⟩))
      · omega
    -- k=4m: c=4m+2
    · exact ⟨_, ⟨6*m+3, e'+8*m+7, by omega, by omega, rfl⟩, main_trans_r2 m e'⟩
    -- k=4m+1: c=4m+3
    · exact ⟨_, ⟨6*m+4, e'+8*m+7, by omega, by omega, rfl⟩, main_trans_r3 m e'⟩
    -- k=4m+2: c=4m+4
    · exact ⟨_, ⟨6*m+7, e'+8*m+15, by omega, by omega, rfl⟩, by
        rw [show 4 * m + 2 + 2 = 4 * m + 4 from by ring]; exact main_trans_r0 m e'⟩
    -- k=4m+3: c=4m+5
    · exact ⟨_, ⟨6*m+7, e'+8*m+11, by omega, by omega, rfl⟩, by
        rw [show 4 * m + 3 + 2 = 4 * m + 5 from by ring]; exact main_trans_r1 m e'⟩
  · exact ⟨2, 2, by omega, by omega, rfl⟩

end Sz22_2003_unofficial_172
