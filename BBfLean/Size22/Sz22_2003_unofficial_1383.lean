import BBfLean.FM

/-!
# sz22_2003_unofficial #1383: [63/10, 5/33, 4/3, 121/7, 15/2]

Vector representation:
```
-1  2 -1  1  0
 0 -1  1  0 -1
 2 -1  0  0  0
 0  0  0 -1  2
-1  1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1383

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

theorem r2r1_chain : ∀ k, ∀ a b d,
    ⟨a + k, b + 1, 0, d, k⟩ [fm]⊢* ⟨a, b + k + 1, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by omega,
        show (k + 1 : ℕ) = k + 1 from rfl]
    step fm; step fm
    rw [show b + (k + 1) + 1 = b + 1 + k + 1 from by omega,
        show d + (k + 1) = d + 1 + k from by omega]
    exact ih a (b + 1) (d + 1)

theorem r3_chain : ∀ k, ∀ a d,
    ⟨a, k, 0, d, 0⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    rw [show a + 2 * (k + 1) = a + 2 + 2 * k from by omega]
    exact ih (a + 2) d

theorem r4_chain : ∀ k, ∀ a e,
    ⟨a, 0, 0, k, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    rw [show e + 2 * (k + 1) = e + 2 + 2 * k from by omega]
    exact ih a (e + 2)

theorem main_trans (K e : ℕ) :
    ⟨(e + 1) + (K + 2), 0, 0, 0, e + 1⟩ [fm]⊢⁺
    ⟨(2 * e + 4) + ((K + 2) + 2), 0, 0, 0, 2 * e + 4⟩ := by
  rw [show (e + 1) + (K + 2) = (e + K + 2) + 1 from by omega]
  step fm
  rw [show e + K + 2 = (e + K + 1) + 1 from by omega,
      show (1 : ℕ) = 0 + 1 from by omega]
  step fm
  rw [show e + K + 1 = K + (e + 1) from by omega,
      show (3 : ℕ) = 2 + 1 from rfl]
  apply stepStar_trans (r2r1_chain (e + 1) K 2 1)
  rw [show 2 + (e + 1) + 1 = e + 4 from by omega,
      show 1 + (e + 1) = e + 2 from by omega]
  apply stepStar_trans (r3_chain (e + 4) K (e + 2))
  rw [show K + 2 * (e + 4) = K + 2 * e + 8 from by omega]
  apply stepStar_trans (r4_chain (e + 2) (K + 2 * e + 8) 0)
  rw [show 0 + 2 * (e + 2) = 2 * e + 4 from by omega,
      show K + 2 * e + 8 = (2 * e + 4) + ((K + 2) + 2) from by omega]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 0, 2⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨K, e⟩ ↦ ⟨(e + 1) + (K + 2), 0, 0, 0, e + 1⟩) ⟨1, 1⟩
  intro ⟨K, e⟩
  exact ⟨⟨K + 2, 2 * e + 3⟩, main_trans K e⟩

end Sz22_2003_unofficial_1383
