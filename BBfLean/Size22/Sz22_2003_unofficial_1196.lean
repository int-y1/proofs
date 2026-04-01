import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1196: [5/6, 49/3, 1089/35, 2/11, 15/2]

Vector representation:
```
-1 -1  1  0  0
 0 -1  0  2  0
 0  2 -1 -1  2
 1  0  0  0 -1
-1  1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1196

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- R4 chain: move e to a
theorem e_to_a : ∀ k, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a + k, 0, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 1))
    ring_nf; finish

-- R3+R2+R2 chain: drain c when a=0
theorem r322_chain : ∀ k, ⟨0, 0, c + k, d + 1, e⟩ [fm]⊢* ⟨0, 0, c, d + 1 + 3 * k, e + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c := c) (d := d + 3) (e := e + 2))
    ring_nf; finish

-- Drain: from (0, 0, c, d+1, e) to (e + 2*c, 0, 0, d + 1 + 3*c, 0)
theorem drain : ⟨0, 0, c, d + 1, e⟩ [fm]⊢* ⟨e + 2 * c, 0, 0, d + 1 + 3 * c, 0⟩ := by
  rw [show (c : ℕ) = 0 + c from by ring]
  apply stepStar_trans (r322_chain c (c := 0) (d := d) (e := e))
  simp only [Nat.zero_add]
  rw [show e + 2 * c = 0 + (e + 2 * c) from by ring,
      show (0 : ℕ) = 0 from rfl]
  apply stepStar_trans (e_to_a (e + 2 * c) (a := 0) (d := d + 1 + 3 * c) (e := 0))
  simp only [Nat.zero_add]; finish

-- Combined: (a, 0, c+1, d+1, e) ->* (e+2c+2+2a, 0, 0, d+3c+4+a, 0) when d+1 >= a
theorem combined : ∀ a, ∀ c d e, d + 1 ≥ a →
    ⟨a, 0, c + 1, d + 1, e⟩ [fm]⊢* ⟨e + 2 * c + 2 + 2 * a, 0, 0, d + 3 * c + 4 + a, 0⟩ := by
  intro a; induction' a using Nat.strongRecOn with a ih; intro c d e hd
  rcases a with _ | _ | a
  · -- a = 0
    apply stepStar_trans (drain (c := c + 1) (d := d) (e := e))
    ring_nf; finish
  · -- a = 1
    step fm  -- R3: (1, 2, c, d, e+2)
    step fm  -- R1: (0, 1, c+1, d, e+2)
    step fm  -- R2: (0, 0, c+1, d+2, e+2)
    rw [show d + 2 = (d + 1) + 1 from by ring]
    apply stepStar_trans (drain (c := c + 1) (d := d + 1) (e := e + 2))
    ring_nf; finish
  · -- a + 2
    step fm  -- R3: (a+2, 2, c, d, e+2)
    step fm  -- R1: (a+1, 1, c+1, d, e+2)
    step fm  -- R1: (a, 0, c+2, d, e+2)
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    rw [show c + 2 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih a (by omega) (c + 1) d' (e + 2) (by omega))
    ring_nf; finish

-- Main transition: need d+1 >= a for combined
theorem main_trans (hd : d + 1 ≥ a) : ⟨a + 2, 0, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨2 * a + 4, 0, 0, d + a + 7, 0⟩ := by
  step fm  -- R5: (a+1, 1, 1, d+1, 0)
  step fm  -- R1: (a, 0, 2, d+1, 0)
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (combined a 1 d 0 hd)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 5, 0⟩)
  · execute fm 7
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a + 2, 0, 0, d + 1, 0⟩ ∧ d + 1 ≥ a ∧ d ≥ a + 4)
  · intro c ⟨a, d, hq, hd, hda⟩; subst hq
    refine ⟨⟨2 * a + 4, 0, 0, d + a + 7, 0⟩,
      ⟨2 * a + 2, d + a + 6, rfl, by omega, by omega⟩,
      main_trans hd⟩
  · exact ⟨0, 4, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1196
