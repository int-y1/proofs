import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1984: [99/35, 4/5, 25/6, 7/11, 55/2]

Vector representation:
```
 0  2 -1 -1  1
 2  0 -1  0  0
-1 -1  2  0  0
 0  0  0  1 -1
-1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1984

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

theorem e_to_d : ∀ k, ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih generalizing d
  · exists 0
  · rw [show d + (k + 1) = (d + 1) + k from by ring]
    step fm
    exact ih (d := d + 1)

theorem r3r2r2 : ∀ k, ⟨a + 1, k, 0, 0, e⟩ [fm]⊢* ⟨a + 3 * k + 1, 0, 0, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a
  · exists 0
  · step fm; step fm; step fm
    rw [show a + 3 + 1 = (a + 3) + 1 from by ring,
        show a + 3 * (k + 1) + 1 = (a + 3) + 3 * k + 1 from by ring]
    exact ih (a := a + 3)

theorem drain_even : ∀ k, ∀ a b e, ⟨a + k, b + 1, 0, 2 * k, e⟩ [fm]⊢* ⟨a, b + 3 * k + 1, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih
  · intro a b e; exists 0
  · intro a b e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show 2 * (k + 1) = 2 * k + 1 + 1 from by ring]
    step fm; step fm; step fm
    -- Goal: (a+k, b+2+2, 0, 2*k, e+1+1) ⊢* (a, b+3*(k+1)+1, 0, 0, e+(2*k+1+1))
    -- Need to massage to ih form: (a+k, (b+3)+1, 0, 2*k, (e+2)) ⊢* (a, (b+3)+3*k+1, 0, 0, (e+2)+2*k)
    rw [show b + 2 + 2 = (b + 3) + 1 from by ring,
        show e + 1 + 1 = e + 2 from by ring,
        show b + 3 * (k + 1) + 1 = (b + 3) + 3 * k + 1 from by ring,
        show e + (2 * k + 1 + 1) = (e + 2) + 2 * k from by omega]
    exact ih a (b + 3) (e + 2)

theorem drain_odd : ∀ k, ∀ a b e, ⟨a + k + 1, b + 1, 0, 2 * k + 1, e⟩ [fm]⊢* ⟨a + 2, b + 3 * k + 2, 0, 0, e + 2 * k + 1⟩ := by
  intro k; induction' k with k ih
  · intro a b e
    step fm; step fm; step fm; finish
  · intro a b e
    rw [show a + (k + 1) + 1 = (a + k + 1) + 1 from by ring,
        show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 from by ring]
    step fm; step fm; step fm
    -- Goal: (a+k+1, b+2+2, 0, 2*k+1, e+1+1) ⊢* (a+2, b+3*(k+1)+2, 0, 0, e+2*(k+1)+1)
    rw [show b + 2 + 2 = (b + 3) + 1 from by ring,
        show e + 1 + 1 = e + 2 from by ring,
        show b + 3 * (k + 1) + 2 = (b + 3) + 3 * k + 2 from by ring,
        show e + 2 * (k + 1) + 1 = (e + 2) + 2 * k + 1 from by ring]
    exact ih a (b + 3) (e + 2)

theorem trans_odd : ⟨n + k + 2, 0, 0, 2 * k + 1, 0⟩ [fm]⊢⁺ ⟨n + 9 * k + 7, 0, 0, 2 * k + 2, 0⟩ := by
  step fm; step fm
  rw [show n + k + 1 = (n + 1) + k from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (drain_even k (n + 1) 1 2)
  rw [show 1 + 3 * k + 1 = 3 * k + 2 from by ring,
      show n + 1 = n + 1 from rfl]
  apply stepStar_trans (r3r2r2 (3 * k + 2) (a := n) (e := 2 + 2 * k))
  rw [show n + 3 * (3 * k + 2) + 1 = n + 9 * k + 7 from by ring,
      show 2 + 2 * k = 2 * k + 2 from by ring]
  apply stepStar_trans (e_to_d (2 * k + 2) (a := n + 9 * k + 7) (d := 0))
  ring_nf; finish

theorem trans_even : ⟨m + k + 2, 0, 0, 2 * (k + 1), 0⟩ [fm]⊢⁺ ⟨m + 9 * k + 11, 0, 0, 2 * k + 3, 0⟩ := by
  step fm; step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show m + k + 1 = m + k + 1 from rfl]
  apply stepStar_trans (drain_odd k m 1 2)
  rw [show m + 2 = (m + 1) + 1 from by ring,
      show 1 + 3 * k + 2 = 3 * k + 3 from by ring]
  apply stepStar_trans (r3r2r2 (3 * k + 3) (a := m + 1) (e := 2 + 2 * k + 1))
  rw [show (m + 1) + 3 * (3 * k + 3) + 1 = m + 9 * k + 11 from by ring,
      show 2 + 2 * k + 1 = 2 * k + 3 from by ring]
  apply stepStar_trans (e_to_d (2 * k + 3) (a := m + 9 * k + 11) (d := 0))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 3)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d + 1, 0⟩ ∧ a ≥ d + 2)
  · intro c ⟨a, d, hq, ha⟩; subst hq
    rcases Nat.even_or_odd (d + 1) with ⟨K, hK⟩ | ⟨K, hK⟩
    · obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
      have hd1 : d + 1 = 2 * (k + 1) := by omega
      rw [hd1]
      obtain ⟨m, rfl⟩ : ∃ m, a = m + k + 2 := ⟨a - k - 2, by omega⟩
      refine ⟨⟨m + 9 * k + 11, 0, 0, 2 * k + 3, 0⟩,
        ⟨m + 9 * k + 11, 2 * k + 2, ?_, ?_⟩, trans_even⟩
      · ring_nf
      · omega
    · have hd1 : d + 1 = 2 * K + 1 := by omega
      rw [hd1]
      obtain ⟨n, rfl⟩ : ∃ n, a = n + K + 2 := ⟨a - K - 2, by omega⟩
      refine ⟨⟨n + 9 * K + 7, 0, 0, 2 * K + 2, 0⟩,
        ⟨n + 9 * K + 7, 2 * K + 1, ?_, ?_⟩, trans_odd⟩
      · ring_nf
      · omega
  · exact ⟨2, 0, rfl, by omega⟩
