import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1131: [5/6, 44/35, 49/2, 3/11, 165/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  1
-1  0  0  2  0
 0  1  0  0 -1
 0  1  1 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1131

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c+1, d, e+1⟩
  | _ => none

private theorem e_to_b_gen : ∀ k b d, ⟨0, b, 0, d, k⟩ [fm]⊢* ⟨0, b + k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · step fm; apply stepStar_trans (ih (b + 1) d); ring_nf; finish

theorem e_to_b : ∀ k d, ⟨0, 0, 0, d, k⟩ [fm]⊢* ⟨0, k, 0, d, 0⟩ := by
  intro k d; have h := e_to_b_gen k 0 d; simpa using h

theorem r3_chain : ∀ k a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih a (d + 2) e); ring_nf; finish

theorem r2_chain : ∀ k a c d e, ⟨a, 0, c + k, d + k, e⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (a + 2) c d (e + 1)); ring_nf; finish

theorem inner_chain : ∀ k b c d e, ⟨0, b + 2 * k, c + 1, d + k, e⟩ [fm]⊢*
    ⟨0, b, c + 1 + k, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 1) d (e + 1)); ring_nf; finish

theorem partial_round (c d e : ℕ) :
    ⟨0, 1, c + 1, d + 1, e⟩ [fm]⊢* ⟨1, 0, c + 1, d, e + 1⟩ := by
  step fm; step fm; finish

theorem tail_deq (a e : ℕ) :
    ⟨a + 1, 0, 1, 0, e⟩ [fm]⊢* ⟨0, 0, 0, 2 * a + 5, e + 1⟩ := by
  step fm; step fm
  rw [show a + 2 = 0 + (a + 2) from by ring]
  apply stepStar_trans (r3_chain (a + 2) 0 1 (e + 1)); ring_nf; finish

private theorem qeq {a₁ b₁ c₁ d₁ e₁ a₂ b₂ c₂ d₂ e₂ : ℕ}
    (ha : a₁ = a₂) (hb : b₁ = b₂) (hc : c₁ = c₂) (hd : d₁ = d₂) (he : e₁ = e₂) :
    (⟨a₁, b₁, c₁, d₁, e₁⟩ : Q) = ⟨a₂, b₂, c₂, d₂, e₂⟩ := by
  subst ha; subst hb; subst hc; subst hd; subst he; rfl

theorem from_b_even_ge (m r : ℕ) : ⟨0, 2 * m, 0, 2 * m + 3 + r, 0⟩ [fm]⊢⁺
    ⟨0, 0, 0, 4 * m + r + 6, 2 * m + 3⟩ := by
  rw [show (2 * m + 3 + r : ℕ) = (2 * m + 2 + r) + 1 from by ring]
  step fm
  rw [show (2 * m + 1 : ℕ) = 1 + 2 * m from by ring,
      show (2 * m + 2 + r : ℕ) = (m + 2 + r) + m from by ring]
  apply stepStar_trans (inner_chain m 1 0 (m + 2 + r) 1)
  -- State: ⟨0, 1, 0+1+m, m+2+r, 1+m⟩ which normalizes to ⟨0, 1, 1+m, m+2+r, 1+m⟩
  have heq : (⟨(0:ℕ), 1, 0 + 1 + m, m + 2 + r, 1 + m⟩ : Q) =
      ⟨0, 1, m + 1, (m + 1 + r) + 1, 1 + m⟩ := qeq rfl rfl (by omega) (by omega) rfl
  rw [heq]
  apply stepStar_trans (partial_round m (m + 1 + r) (1 + m))
  have heq2 : (⟨(1:ℕ), 0, m + 1, m + 1 + r, 1 + m + 1⟩ : Q) =
      ⟨1, 0, 0 + (m + 1), r + (m + 1), 1 + m + 1⟩ := qeq rfl rfl (by omega) (by omega) rfl
  rw [heq2]
  apply stepStar_trans (r2_chain (m + 1) 1 0 r (1 + m + 1))
  have heq3 : (⟨1 + 2 * (m + 1), (0:ℕ), 0, r, 1 + m + 1 + (m + 1)⟩ : Q) =
      ⟨0 + (2 * m + 3), 0, 0, r, 2 * m + 3⟩ := qeq (by omega) rfl rfl rfl (by omega)
  rw [heq3]
  apply stepStar_trans (r3_chain (2 * m + 3) 0 r (2 * m + 3))
  have heq4 : (⟨(0:ℕ), 0, 0, r + 2 * (2 * m + 3), 2 * m + 3⟩ : Q) =
      ⟨0, 0, 0, 4 * m + r + 6, 2 * m + 3⟩ := qeq rfl rfl rfl (by omega) rfl
  rw [heq4]; finish

theorem from_b_even_eq (m : ℕ) : ⟨0, 2 * m, 0, 2 * m + 2, 0⟩ [fm]⊢⁺
    ⟨0, 0, 0, 4 * m + 5, 2 * m + 3⟩ := by
  rw [show (2 * m + 2 : ℕ) = (2 * m + 1) + 1 from by ring]
  step fm
  nth_rewrite 1 [show (2 * m + 1 : ℕ) = 1 + 2 * m from by ring]
  rw [show (2 * m + 1 : ℕ) = (m + 1) + m from by ring]
  apply stepStar_trans (inner_chain m 1 0 (m + 1) 1)
  -- State: ⟨0, 1, 0+1+m, m+1, 1+m⟩ normalized to ⟨0, 1, 1+m, m+1, 1+m⟩
  have heq : (⟨(0:ℕ), 1, 0 + 1 + m, m + 1, 1 + m⟩ : Q) =
      ⟨0, 1, m + 1, m + 1, 1 + m⟩ := qeq rfl rfl (by omega) rfl rfl
  rw [heq]
  apply stepStar_trans (partial_round m m (1 + m))
  -- State: ⟨1, 0, m+1, m, 1+m+1⟩
  have heq2 : (⟨(1:ℕ), 0, m + 1, m, 1 + m + 1⟩ : Q) =
      ⟨1, 0, 1 + m, 0 + m, 1 + m + 1⟩ := qeq rfl rfl (by omega) (by omega) rfl
  rw [heq2]
  apply stepStar_trans (r2_chain m 1 1 0 (1 + m + 1))
  -- State: ⟨1+2*m, 0, 1, 0, 1+m+1+m⟩
  have heq3 : (⟨1 + 2 * m, (0:ℕ), 1, 0, 1 + m + 1 + m⟩ : Q) =
      ⟨(2 * m) + 1, 0, 1, 0, 1 + m + 1 + m⟩ := qeq (by omega) rfl rfl rfl rfl
  rw [heq3]
  apply stepStar_trans (tail_deq (2 * m) (1 + m + 1 + m))
  have heq4 : (⟨(0:ℕ), 0, 0, 2 * (2 * m) + 5, 1 + m + 1 + m + 1⟩ : Q) =
      ⟨0, 0, 0, 4 * m + 5, 2 * m + 3⟩ := qeq rfl rfl rfl (by omega) (by omega)
  rw [heq4]; finish

theorem from_b_odd_ge (m r : ℕ) : ⟨0, 2 * m + 1, 0, 2 * m + 4 + r, 0⟩ [fm]⊢⁺
    ⟨0, 0, 0, 4 * m + r + 8, 2 * m + 4⟩ := by
  rw [show (2 * m + 4 + r : ℕ) = (2 * m + 3 + r) + 1 from by ring]
  step fm
  rw [show (2 * m + 1 + 1 : ℕ) = 0 + 2 * (m + 1) from by ring,
      show (2 * m + 3 + r : ℕ) = (m + 2 + r) + (m + 1) from by ring]
  apply stepStar_trans (inner_chain (m + 1) 0 0 (m + 2 + r) 1)
  -- State: ⟨0, 0, 0+1+(m+1), m+2+r, 1+(m+1)⟩ normalized to ⟨0, 0, 2+m, m+2+r, 2+m⟩
  have heq : (⟨(0:ℕ), 0, 0 + 1 + (m + 1), m + 2 + r, 1 + (m + 1)⟩ : Q) =
      ⟨0, 0, 0 + (m + 2), r + (m + 2), 0 + (m + 2)⟩ := qeq rfl rfl (by omega) (by omega) (by omega)
  rw [heq]
  apply stepStar_trans (r2_chain (m + 2) 0 0 r (0 + (m + 2)))
  have heq2 : (⟨0 + 2 * (m + 2), (0:ℕ), 0, r, 0 + (m + 2) + (m + 2)⟩ : Q) =
      ⟨0 + (2 * m + 4), 0, 0, r, 2 * m + 4⟩ := qeq (by omega) rfl rfl rfl (by omega)
  rw [heq2]
  apply stepStar_trans (r3_chain (2 * m + 4) 0 r (2 * m + 4))
  have heq3 : (⟨(0:ℕ), 0, 0, r + 2 * (2 * m + 4), 2 * m + 4⟩ : Q) =
      ⟨0, 0, 0, 4 * m + r + 8, 2 * m + 4⟩ := qeq rfl rfl rfl (by omega) rfl
  rw [heq3]; finish

theorem from_b_odd_eq (m : ℕ) : ⟨0, 2 * m + 1, 0, 2 * m + 3, 0⟩ [fm]⊢⁺
    ⟨0, 0, 0, 4 * m + 7, 2 * m + 4⟩ := by
  rw [show (2 * m + 3 : ℕ) = (2 * m + 2) + 1 from by ring]
  step fm
  nth_rewrite 1 [show (2 * m + 1 + 1 : ℕ) = 0 + 2 * (m + 1) from by ring]
  rw [show (2 * m + 1 + 1 : ℕ) = (m + 1) + (m + 1) from by ring]
  apply stepStar_trans (inner_chain (m + 1) 0 0 (m + 1) 1)
  -- State: ⟨0, 0, 0+1+(m+1), m+1, 1+(m+1)⟩ normalized to ⟨0, 0, 2+m, m+1, 2+m⟩
  have heq : (⟨(0:ℕ), 0, 0 + 1 + (m + 1), m + 1, 1 + (m + 1)⟩ : Q) =
      ⟨0, 0, 1 + (m + 1), 0 + (m + 1), 1 + (m + 1)⟩ := qeq rfl rfl rfl (by omega) rfl
  rw [heq]
  apply stepStar_trans (r2_chain (m + 1) 0 1 0 (1 + (m + 1)))
  have heq2 : (⟨0 + 2 * (m + 1), (0:ℕ), 1, 0, 1 + (m + 1) + (m + 1)⟩ : Q) =
      ⟨(2 * m + 1) + 1, 0, 1, 0, 2 * m + 3⟩ := qeq (by omega) rfl rfl rfl (by omega)
  rw [heq2]
  apply stepStar_trans (tail_deq (2 * m + 1) (2 * m + 3))
  have heq3 : (⟨(0:ℕ), 0, 0, 2 * (2 * m + 1) + 5, 2 * m + 3 + 1⟩ : Q) =
      ⟨0, 0, 0, 4 * m + 7, 2 * m + 4⟩ := qeq rfl rfl rfl (by omega) (by omega)
  rw [heq3]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ D E, q = ⟨0, 0, 0, D, E⟩ ∧ D ≥ E + 2)
  · intro c ⟨D, E, hq, hD⟩; subst hq
    rcases Nat.even_or_odd E with ⟨m, hm⟩ | ⟨m, hm⟩
    · rw [show m + m = 2 * m from by ring] at hm; subst hm
      rcases (show D = 2 * m + 2 ∨ D ≥ 2 * m + 3 from by omega) with rfl | hDge
      · refine ⟨⟨0, 0, 0, 4 * m + 5, 2 * m + 3⟩,
          ⟨4 * m + 5, 2 * m + 3, rfl, by omega⟩, ?_⟩
        apply stepStar_stepPlus_stepPlus (e_to_b (2 * m) (2 * m + 2))
        exact from_b_even_eq m
      · obtain ⟨r, rfl⟩ : ∃ r, D = 2 * m + 3 + r := ⟨D - (2 * m + 3), by omega⟩
        refine ⟨⟨0, 0, 0, 4 * m + r + 6, 2 * m + 3⟩,
          ⟨4 * m + r + 6, 2 * m + 3, rfl, by omega⟩, ?_⟩
        apply stepStar_stepPlus_stepPlus (e_to_b (2 * m) (2 * m + 3 + r))
        exact from_b_even_ge m r
    · subst hm
      rcases (show D = 2 * m + 3 ∨ D ≥ 2 * m + 4 from by omega) with rfl | hDge
      · refine ⟨⟨0, 0, 0, 4 * m + 7, 2 * m + 4⟩,
          ⟨4 * m + 7, 2 * m + 4, rfl, by omega⟩, ?_⟩
        apply stepStar_stepPlus_stepPlus (e_to_b (2 * m + 1) (2 * m + 3))
        exact from_b_odd_eq m
      · obtain ⟨r, rfl⟩ : ∃ r, D = 2 * m + 4 + r := ⟨D - (2 * m + 4), by omega⟩
        refine ⟨⟨0, 0, 0, 4 * m + r + 8, 2 * m + 4⟩,
          ⟨4 * m + r + 8, 2 * m + 4, rfl, by omega⟩, ?_⟩
        apply stepStar_stepPlus_stepPlus (e_to_b (2 * m + 1) (2 * m + 4 + r))
        exact from_b_odd_ge m r
  · exact ⟨2, 0, rfl, by omega⟩

end Sz22_2003_unofficial_1131
