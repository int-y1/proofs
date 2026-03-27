import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz22_2003_unofficial #281: [14/15, 63/2, 1/567, 5/7, 3/5]

Vector representation:
```
 1 -1 -1  1
-1  2  0  1
 0 -4  0 -1
 0  0  1 -1
 0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_281

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+1, b, c, d+1⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b+2, c, d+1⟩
  | ⟨a, b+4, c, d+1⟩ => some ⟨a, b, c, d⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b, c+1, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b+1, c, d⟩
  | _ => none

theorem d_to_c_gen : ∀ d c, ⟨0, 0, c, d⟩ [fm]⊢* ⟨0, 0, c+d, 0⟩ := by
  intro d; induction d with
  | zero => intro c; exists 0
  | succ d ih =>
    intro c; step fm
    apply stepStar_trans (ih _)
    ring_nf; finish

theorem setup (c : ℕ) : ⟨0, 0, c+2, 0⟩ [fm]⊢⁺ ⟨0, 2, c, 2⟩ := by
  execute fm 3

theorem consume_pair : ⟨a, 2, c+2, d⟩ [fm]⊢* ⟨a+1, 2, c, d+3⟩ := by
  step fm; step fm; step fm; ring_nf; finish

theorem consume_chain : ∀ k a c d,
    ⟨a, 2, c + 2*k, d⟩ [fm]⊢* ⟨a+k, 2, c, d + 3*k⟩ := by
  intro k; induction k with
  | zero => intro a c d; ring_nf; exists 0
  | succ k ih =>
    intro a c d
    rw [show c + 2 * (k + 1) = (c + 2*k) + 2 from by ring]
    apply stepStar_trans consume_pair
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

theorem rule2_chain : ∀ a b d, ⟨a+1, b, 0, d⟩ [fm]⊢* ⟨0, b+2*(a+1), 0, d+a+1⟩ := by
  intro a; induction a with
  | zero => intro b d; step fm; ring_nf; finish
  | succ a ih =>
    intro b d; step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

theorem rule3_chain : ∀ k b d, ⟨0, b+4*k, 0, d+k⟩ [fm]⊢* ⟨0, b, 0, d⟩ := by
  intro k; induction k with
  | zero => intro b d; ring_nf; exists 0
  | succ k ih =>
    intro b d
    have h1 : fm ⟨0, (b+4*k)+4, 0, (d+k)+1⟩ = some ⟨0, b+4*k, 0, d+k⟩ := by unfold fm; rfl
    rw [show b + 4*(k+1) = (b+4*k)+4 from by ring, show d+(k+1) = (d+k)+1 from by ring]
    exact stepStar_trans (step_stepStar h1) (ih b d)

theorem close_1 (d : ℕ) : ⟨0, 1, 0, d+1⟩ [fm]⊢⁺ ⟨0, 0, 0, d+3⟩ := by
  execute fm 10

theorem close_2 (d : ℕ) : ⟨0, 2, 0, d+1⟩ [fm]⊢⁺ ⟨0, 0, 0, d+2⟩ := by
  execute fm 7

theorem close_3 (d : ℕ) : ⟨0, 3, 0, d+1⟩ [fm]⊢⁺ ⟨0, 0, 0, d+1⟩ := by
  execute fm 4

-- (0,0,0,4m+3) →⁺ (0,0,0,7m+4)
theorem trans_3 (m : ℕ) : ⟨0, 0, 0, 4*m+3⟩ [fm]⊢⁺ ⟨0, 0, 0, 7*m+4⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, (4*m+2)+1⟩ = some ⟨0, 0, 1, 4*m+2⟩; unfold fm; rfl
  apply stepStar_trans (d_to_c_gen _ _)
  rw [show 1 + (4*m+2) = (4*m+1) + 2 from by ring]
  apply stepStar_trans (stepPlus_stepStar (setup _))
  rw [show 4*m+1 = 1 + 2*(2*m) from by ring]
  apply stepStar_trans (consume_chain (2*m) 0 1 2)
  rw [show 0 + 2*m = 2*m from by ring, show 2 + 3*(2*m) = 6*m+2 from by ring]
  step fm
  rw [show 2*m + 1 = (2*m) + 1 from by ring]
  apply stepStar_trans (rule2_chain (2*m) 1 (6*m+3))
  rw [show 1+2*(2*m+1) = 3+4*m from by ring, show 6*m+3+(2*m)+1 = (7*m+4)+m from by ring]
  apply stepStar_trans (rule3_chain m 3 (7*m+4))
  rw [show 7*m+4 = (7*m+3)+1 from by ring]
  exact stepPlus_stepStar (close_3 _)

-- (0,0,0,4m+4) →⁺ (0,0,0,7m+5)
theorem trans_0 (m : ℕ) : ⟨0, 0, 0, 4*m+4⟩ [fm]⊢⁺ ⟨0, 0, 0, 7*m+5⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, (4*m+3)+1⟩ = some ⟨0, 0, 1, 4*m+3⟩; unfold fm; rfl
  apply stepStar_trans (d_to_c_gen _ _)
  rw [show 1 + (4*m+3) = (4*m+2) + 2 from by ring]
  apply stepStar_trans (stepPlus_stepStar (setup _))
  rw [show 4*m+2 = 0 + 2*(2*m+1) from by ring]
  apply stepStar_trans (consume_chain (2*m+1) 0 0 2)
  rw [show 0 + (2*m+1) = 2*m+1 from by ring, show 2 + 3*(2*m+1) = 6*m+5 from by ring]
  rw [show 2*m+1 = (2*m)+1 from by ring]
  apply stepStar_trans (rule2_chain (2*m) 2 (6*m+5))
  rw [show 2+2*(2*m+1) = 0+4*(m+1) from by ring, show 6*m+5+(2*m)+1 = (7*m+5)+(m+1) from by ring]
  exact rule3_chain (m+1) 0 (7*m+5)

-- (0,0,0,4m+5) →⁺ (0,0,0,7m+9)
theorem trans_1 (m : ℕ) : ⟨0, 0, 0, 4*m+5⟩ [fm]⊢⁺ ⟨0, 0, 0, 7*m+9⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, (4*m+4)+1⟩ = some ⟨0, 0, 1, 4*m+4⟩; unfold fm; rfl
  apply stepStar_trans (d_to_c_gen _ _)
  rw [show 1 + (4*m+4) = (4*m+3) + 2 from by ring]
  apply stepStar_trans (stepPlus_stepStar (setup _))
  rw [show 4*m+3 = 1 + 2*(2*m+1) from by ring]
  apply stepStar_trans (consume_chain (2*m+1) 0 1 2)
  rw [show 0 + (2*m+1) = 2*m+1 from by ring, show 2 + 3*(2*m+1) = 6*m+5 from by ring]
  step fm
  rw [show 2*m+1+1 = (2*m+1)+1 from by ring]
  apply stepStar_trans (rule2_chain (2*m+1) 1 (6*m+6))
  rw [show 1+2*(2*m+1+1) = 1+4*(m+1) from by ring,
      show 6*m+6+(2*m+1)+1 = (7*m+7)+(m+1) from by ring]
  apply stepStar_trans (rule3_chain (m+1) 1 (7*m+7))
  rw [show 7*m+7 = (7*m+6)+1 from by ring]
  exact stepPlus_stepStar (close_1 _)

-- (0,0,0,4m+6) →⁺ (0,0,0,7m+10)
theorem trans_2 (m : ℕ) : ⟨0, 0, 0, 4*m+6⟩ [fm]⊢⁺ ⟨0, 0, 0, 7*m+10⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, (4*m+5)+1⟩ = some ⟨0, 0, 1, 4*m+5⟩; unfold fm; rfl
  apply stepStar_trans (d_to_c_gen _ _)
  rw [show 1 + (4*m+5) = (4*m+4) + 2 from by ring]
  apply stepStar_trans (stepPlus_stepStar (setup _))
  rw [show 4*m+4 = 0 + 2*(2*m+2) from by ring]
  apply stepStar_trans (consume_chain (2*m+2) 0 0 2)
  rw [show 0 + (2*m+2) = 2*m+2 from by ring, show 2 + 3*(2*m+2) = 6*m+8 from by ring]
  rw [show 2*m+2 = (2*m+1)+1 from by ring]
  apply stepStar_trans (rule2_chain (2*m+1) 2 (6*m+8))
  rw [show 2+2*(2*m+1+1) = 2+4*(m+1) from by ring,
      show 6*m+8+(2*m+1)+1 = (7*m+9)+(m+1) from by ring]
  apply stepStar_trans (rule3_chain (m+1) 2 (7*m+9))
  rw [show 7*m+9 = (7*m+8)+1 from by ring]
  exact stepPlus_stepStar (close_2 _)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2⟩)
  · execute fm 8
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d, q = ⟨0, 0, 0, d⟩ ∧ d ≥ 2)
  · intro c ⟨d, hq, hd⟩; subst hq
    rcases (show d = 2 ∨ (∃ m, d = 4*m+3) ∨ (∃ m, d = 4*m+4) ∨
                (∃ m, d = 4*m+5) ∨ (∃ m, d = 4*m+6) from by
            rcases Nat.eq_or_lt_of_le hd with h | h
            · left; omega
            · right
              set q := (d - 3) / 4
              set r := (d - 3) % 4
              have hmod : d - 3 = 4 * q + r := (Nat.div_add_mod (d - 3) 4).symm
              have hr : r < 4 := Nat.mod_lt _ (by omega)
              have hd3 : d = 4 * q + r + 3 := by omega
              interval_cases r
              · left; exact ⟨q, by omega⟩
              · right; left; exact ⟨q, by omega⟩
              · right; right; left; exact ⟨q, by omega⟩
              · right; right; right; exact ⟨q, by omega⟩) with
      rfl | ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩
    · exact ⟨⟨0, 0, 0, 3⟩, ⟨3, rfl, by omega⟩, by execute fm 12⟩
    · exact ⟨⟨0, 0, 0, 7*m+4⟩, ⟨7*m+4, rfl, by omega⟩, trans_3 m⟩
    · exact ⟨⟨0, 0, 0, 7*m+5⟩, ⟨7*m+5, rfl, by omega⟩, trans_0 m⟩
    · exact ⟨⟨0, 0, 0, 7*m+9⟩, ⟨7*m+9, rfl, by omega⟩, trans_1 m⟩
    · exact ⟨⟨0, 0, 0, 7*m+10⟩, ⟨7*m+10, rfl, by omega⟩, trans_2 m⟩
  · exact ⟨2, rfl, by omega⟩
