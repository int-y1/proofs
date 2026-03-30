import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz22_2003_unofficial #1100: [5/6, 392/55, 77/2, 3/7, 5/3]

Vector representation:
```
-1 -1  1  0  0
 3  0 -1  2 -1
-1  0  0  1  1
 0  1  0 -1  0
 0 -1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1100

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+3, b, c, d+2, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

private theorem stepStar_of_eq {fm : Q → Option Q} (h : c₁ = c₂) :
    c₁ [fm]⊢* c₂ := by subst h; exact ⟨0, rfl⟩

theorem r3_drain : ∀ k d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d + 1) (e + 1))
    ring_nf; finish

theorem r4_drain : ∀ k b e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) e)
    ring_nf; finish

theorem r2_drain : ∀ k a c d, ⟨a, 0, c + k, d, k⟩ [fm]⊢* ⟨a + 3 * k, 0, c, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 3) c (d + 2))
    ring_nf; finish

theorem r3r2_tail : ∀ c a d, ⟨a + 1, 0, c, d, 0⟩ [fm]⊢* ⟨a + 2 * c + 1, 0, 0, d + 3 * c, 0⟩ := by
  intro c; induction' c with c ih <;> intro a d
  · exists 0
  · step fm; step fm
    rw [show a + 3 = (a + 2) + 1 from by ring]
    apply stepStar_trans (ih (a + 2) (d + 3))
    ring_nf; finish

theorem combo : ∀ e b c d, b ≤ 3 * (e + 1) → c + b ≥ e + 1 →
    ⟨3, b, c, d, e + 1⟩ [fm]⊢* ⟨3 * (e + 1) - b + 3, 0, c + b - (e + 1), d + 2 * (e + 1), 0⟩ := by
  intro e; induction' e with e ih <;> intro b c d hb hcb
  · interval_cases b
    · rw [show c = (c - 1) + 1 from by omega]; step fm
      apply stepStar_of_eq; show (⟨_, _, _, _, _⟩ : ℕ × ℕ × ℕ × ℕ × ℕ) = ⟨_, _, _, _, _⟩
      ext <;> simp
    · rw [show (1 : ℕ) = 0 + 1 from by ring]; step fm
      rw [show c + 1 = (c + 1 - 1) + 1 from by omega]; step fm
      apply stepStar_of_eq; show (⟨_, _, _, _, _⟩ : ℕ × ℕ × ℕ × ℕ × ℕ) = ⟨_, _, _, _, _⟩
      ext <;> simp
    · rw [show (2 : ℕ) = 1 + 1 from by ring]; step fm
      rw [show (1 : ℕ) = 0 + 1 from by ring]; step fm
      rw [show c + 2 = (c + 2 - 1) + 1 from by omega]; step fm
      apply stepStar_of_eq; show (⟨_, _, _, _, _⟩ : ℕ × ℕ × ℕ × ℕ × ℕ) = ⟨_, _, _, _, _⟩
      ext <;> simp
    · rw [show (3 : ℕ) = 2 + 1 from by ring]; step fm
      rw [show (2 : ℕ) = 1 + 1 from by ring]; step fm
      rw [show (1 : ℕ) = 0 + 1 from by ring]; step fm
      rw [show c + 3 = (c + 3 - 1) + 1 from by omega]; step fm
      apply stepStar_of_eq; show (⟨_, _, _, _, _⟩ : ℕ × ℕ × ℕ × ℕ × ℕ) = ⟨_, _, _, _, _⟩
      ext <;> simp
  · by_cases hb3 : b ≥ 3
    · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 3 := ⟨b - 3, by omega⟩
      rw [show (e + 1 + 1 : ℕ) = (e + 1) + 1 from by ring]
      step fm; step fm; step fm; step fm
      apply stepStar_trans (ih b' (c + 2) (d + 2) (by omega) (by omega))
      apply stepStar_of_eq; show (⟨_, _, _, _, _⟩ : ℕ × ℕ × ℕ × ℕ × ℕ) = ⟨_, _, _, _, _⟩
      ext <;> simp <;> omega
    · push_neg at hb3
      interval_cases b
      · rw [show c = (c - (e + 2)) + (e + 2) from by omega,
            show (e + 1 + 1 : ℕ) = e + 2 from by ring]
        apply stepStar_trans (r2_drain (e + 2) 3 (c - (e + 2)) d)
        apply stepStar_of_eq; show (⟨_, _, _, _, _⟩ : ℕ × ℕ × ℕ × ℕ × ℕ) = ⟨_, _, _, _, _⟩
        ext <;> simp; omega
      · rw [show (1 : ℕ) = 0 + 1 from by ring]; step fm
        rw [show c + 1 = (c + 1 - (e + 2)) + (e + 2) from by omega,
            show (e + 1 + 1 : ℕ) = e + 2 from by ring]
        apply stepStar_trans (r2_drain (e + 2) 2 (c + 1 - (e + 2)) d)
        apply stepStar_of_eq; show (⟨_, _, _, _, _⟩ : ℕ × ℕ × ℕ × ℕ × ℕ) = ⟨_, _, _, _, _⟩
        ext <;> simp; omega
      · rw [show (2 : ℕ) = 1 + 1 from by ring]; step fm
        rw [show (1 : ℕ) = 0 + 1 from by ring]; step fm
        rw [show c + 2 = (c + 2 - (e + 2)) + (e + 2) from by omega,
            show (e + 1 + 1 : ℕ) = e + 2 from by ring]
        apply stepStar_trans (r2_drain (e + 2) 1 (c + 2 - (e + 2)) d)
        apply stepStar_of_eq; show (⟨_, _, _, _, _⟩ : ℕ × ℕ × ℕ × ℕ × ℕ) = ⟨_, _, _, _, _⟩
        ext <;> simp; omega

theorem main_trans (a d : ℕ) (hd : d ≤ 2 * a + 1) :
    ⟨a + 2, 0, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨2 * a + d + 6, 0, 0, 3 * d + 2 * a + 7, 0⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨(a + 1) + 1, 0, 0, d + 1, 0⟩ = some ⟨a + 1, 0, 0, d + 2, 1⟩; simp [fm]
  rw [show (a + 1 : ℕ) = 0 + (a + 1) from by ring]
  apply stepStar_trans (r3_drain (a + 1) (d + 2) 1)
  rw [show d + 2 + (a + 1) = 0 + (d + a + 3) from by ring,
      show 1 + (a + 1) = a + 2 from by ring]
  apply stepStar_trans (r4_drain (d + a + 3) 0 (a + 2))
  rw [show 0 + (d + a + 3) = (d + a + 2) + 1 from by ring]
  step fm
  rw [show (a + 2 : ℕ) = (a + 1) + 1 from by ring]
  step fm
  apply stepStar_trans (combo a (d + a + 2) 0 2 (by omega) (by omega))
  rw [show 3 * (a + 1) - (d + a + 2) + 3 = (2 * a + 3 - d) + 1 from by omega,
      show 0 + (d + a + 2) - (a + 1) = d + 1 from by omega,
      show 2 + 2 * (a + 1) = 2 * a + 4 from by ring]
  apply stepStar_trans (r3r2_tail (d + 1) (2 * a + 3 - d) (2 * a + 4))
  apply stepStar_of_eq; show (⟨_, _, _, _, _⟩ : ℕ × ℕ × ℕ × ℕ × ℕ) = ⟨_, _, _, _, _⟩
  ext <;> simp <;> omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 2, 0⟩) (by execute fm 4)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a + 2, 0, 0, d + 1, 0⟩ ∧ d ≤ 2 * a + 1)
  · intro c ⟨a, d, hq, hd⟩; subst hq
    refine ⟨⟨2 * a + d + 6, 0, 0, 3 * d + 2 * a + 7, 0⟩, ?_, main_trans a d hd⟩
    exact ⟨2 * a + d + 4, 3 * d + 2 * a + 6, rfl, by omega⟩
  · exact ⟨1, 1, rfl, by omega⟩

end Sz22_2003_unofficial_1100
