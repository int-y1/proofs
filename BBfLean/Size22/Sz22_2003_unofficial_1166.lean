import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1166: [5/6, 44/35, 91/2, 3/11, 75/13]

Vector representation:
```
-1 -1  1  0  0  0
 2  0 -1 -1  1  0
-1  0  0  1  0  1
 0  1  0  0 -1  0
 0  1  2  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1166

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+2, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c+2, d, e, f⟩
  | _ => none

theorem r3_drain : ∀ k d f, ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d + k, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro d f
  · exists 0
  · rw [Nat.add_succ a k]; step fm
    apply stepStar_trans (ih (d + 1) (f + 1)); ring_nf; finish

theorem r4_drain : ∀ k b, ⟨0, b, 0, d, e + k, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b
  · exists 0
  · rw [Nat.add_succ e k]; step fm
    apply stepStar_trans (ih (b + 1)); ring_nf; finish

theorem r211_chain : ∀ k b c d e, ⟨0, b + 2 * k, c + 1, d + k, e, f⟩ [fm]⊢*
    ⟨0, b, c + 1 + k, d, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = b + 2 * k + 1 + 1 from by ring, Nat.add_succ d k]
    step fm; step fm; step fm
    rw [show c + 1 + 1 = (c + 1) + 1 from rfl]
    apply stepStar_trans (ih b (c + 1) d (e + 1)); ring_nf; finish

theorem r2_chain : ∀ k a c d e, ⟨a, 0, c + k, d + k, e, f⟩ [fm]⊢*
    ⟨a + 2 * k, 0, c, d, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [Nat.add_succ c k, Nat.add_succ d k]; step fm
    apply stepStar_trans (ih (a + 2) c d (e + 1)); ring_nf; finish

theorem r3r2_spiral : ∀ k a e f, ⟨a + 1, 0, k + 1, 0, e, f⟩ [fm]⊢*
    ⟨a + k + 2, 0, 0, 0, e + k + 1, f + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a e f
  · step fm; step fm; finish
  · rw [Nat.add_succ k 0]; step fm; step fm
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (e + 1) (f + 1)); ring_nf; finish

theorem r3_drain_plus : ∀ k d f, ⟨a + k + 1, 0, 0, d, e, f⟩ [fm]⊢⁺
    ⟨a, 0, 0, d + k + 1, e, f + k + 1⟩ := by
  intro k d f
  rw [Nat.add_succ (a + k) 0]; step fm
  apply stepStar_trans (r3_drain k (d + 1) (f + 1)); ring_nf; finish

-- Even transition
theorem main_even (m : ℕ) :
    ⟨4 * m + 3, 0, 0, 0, 6 * m + 3, (2 * m + 1) * (3 * m + 2)⟩ [fm]⊢⁺
    ⟨4 * m + 5, 0, 0, 0, 6 * m + 6, (m + 1) * (6 * m + 7)⟩ := by
  -- Phase 1: R3 drain
  rw [show (4 * m + 3 : ℕ) = 0 + (4 * m + 2) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus
    (r3_drain_plus (4 * m + 2) 0 ((2 * m + 1) * (3 * m + 2)) (a := 0) (e := 6 * m + 3))
  -- State: (0, 0, 0, 4m+3, 6m+3, (2m+1)*(3m+2)+4m+3)
  -- Phase 2: R4 drain
  rw [show 0 + (4 * m + 2) + 1 = 4 * m + 3 from by ring,
      show (2 * m + 1) * (3 * m + 2) + (4 * m + 2) + 1 =
        (2 * m + 1) * (3 * m + 2) + (4 * m + 3) from by ring,
      show (6 * m + 3 : ℕ) = 0 + (6 * m + 3) from by ring]
  apply stepStar_trans (r4_drain (6 * m + 3) 0 (d := 4 * m + 3) (e := 0)
    (f := (2 * m + 1) * (3 * m + 2) + (4 * m + 3)))
  -- State: (0, 6m+3, 0, 4m+3, 0, f)
  show ⟨0, 0 + (6 * m + 3), 0, 4 * m + 3, 0,
    (2 * m + 1) * (3 * m + 2) + (4 * m + 3)⟩ [fm]⊢* _
  rw [show (0 + (6 * m + 3) : ℕ) = 6 * m + 3 from by ring]
  -- Phase 3: R5 step
  rw [show (2 * m + 1) * (3 * m + 2) + (4 * m + 3) =
    ((2 * m + 1) * (3 * m + 2) + (4 * m + 2)) + 1 from by ring]
  step fm
  -- State: (0, 6m+4, 2, 4m+3, 0, f')
  show ⟨0, 6 * m + 3 + 1, 1 + 1, 4 * m + 3, 0,
    (2 * m + 1) * (3 * m + 2) + (4 * m + 2)⟩ [fm]⊢* _
  -- Phase 4: R211 chain (3m+2 rounds)
  rw [show 6 * m + 3 + 1 = 0 + 2 * (3 * m + 2) from by ring,
      show (4 * m + 3 : ℕ) = (m + 1) + (3 * m + 2) from by ring]
  apply stepStar_trans (r211_chain (3 * m + 2) 0 1 (m + 1) 0
    (f := (2 * m + 1) * (3 * m + 2) + (4 * m + 2)))
  -- State: (0, 0, 3m+4, m+1, 3m+2, f)
  -- Phase 5: R2 chain (m+1 R2s)
  rw [show 1 + 1 + (3 * m + 2) = (2 * m + 3) + (m + 1) from by ring,
      show (0 + (3 * m + 2) : ℕ) = 3 * m + 2 from by ring]
  nth_rw 2 [show (m + 1 : ℕ) = 0 + (m + 1) from by ring]
  apply stepStar_trans (r2_chain (m + 1) 0 (2 * m + 3) 0 (3 * m + 2)
    (f := (2 * m + 1) * (3 * m + 2) + (4 * m + 2)))
  -- State: (2m+2, 0, 2m+3, 0, 4m+3, f)
  show ⟨0 + 2 * (m + 1), 0, 2 * m + 3, 0, 3 * m + 2 + (m + 1),
    (2 * m + 1) * (3 * m + 2) + (4 * m + 2)⟩ [fm]⊢* _
  -- Phase 6: R3/R2 spiral
  rw [show 0 + 2 * (m + 1) = (2 * m + 1) + 1 from by ring,
      show (2 * m + 3 : ℕ) = (2 * m + 2) + 1 from by ring,
      show 3 * m + 2 + (m + 1) = 4 * m + 3 from by ring]
  apply stepStar_trans (r3r2_spiral (2 * m + 2) (2 * m + 1) (4 * m + 3)
    ((2 * m + 1) * (3 * m + 2) + (4 * m + 2)))
  show ⟨(2 * m + 1) + (2 * m + 2) + 2, 0, 0, 0, (4 * m + 3) + (2 * m + 2) + 1,
    (2 * m + 1) * (3 * m + 2) + (4 * m + 2) + (2 * m + 2) + 1⟩ [fm]⊢* _
  rw [show (2 * m + 1) + (2 * m + 2) + 2 = 4 * m + 5 from by ring,
      show (4 * m + 3) + (2 * m + 2) + 1 = 6 * m + 6 from by ring,
      show (2 * m + 1) * (3 * m + 2) + (4 * m + 2) + (2 * m + 2) + 1 =
        (m + 1) * (6 * m + 7) from by ring]
  finish

-- Odd transition helper with expanded target f
private theorem main_odd_aux (m : ℕ) :
    ⟨4 * m + 5, 0, 0, 0, 6 * m + 6, (m + 1) * (6 * m + 7)⟩ [fm]⊢⁺
    ⟨4 * m + 7, 0, 0, 0, 6 * m + 9, 6 * m * m + 19 * m + 15⟩ := by
  -- Phase 1: R3 drain
  rw [show (4 * m + 5 : ℕ) = 0 + (4 * m + 4) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus
    (r3_drain_plus (4 * m + 4) 0 ((m + 1) * (6 * m + 7)) (a := 0) (e := 6 * m + 6))
  -- Phase 2: R4 drain
  rw [show 0 + (4 * m + 4) + 1 = 4 * m + 5 from by ring,
      show (m + 1) * (6 * m + 7) + (4 * m + 4) + 1 =
        (m + 1) * (6 * m + 7) + (4 * m + 5) from by ring,
      show (6 * m + 6 : ℕ) = 0 + (6 * m + 6) from by ring]
  apply stepStar_trans (r4_drain (6 * m + 6) 0 (d := 4 * m + 5) (e := 0)
    (f := (m + 1) * (6 * m + 7) + (4 * m + 5)))
  show ⟨0, 0 + (6 * m + 6), 0, 4 * m + 5, 0,
    (m + 1) * (6 * m + 7) + (4 * m + 5)⟩ [fm]⊢* _
  rw [show (0 + (6 * m + 6) : ℕ) = 6 * m + 6 from by ring]
  -- Phase 3: R5 step
  rw [show (m + 1) * (6 * m + 7) + (4 * m + 5) =
    ((m + 1) * (6 * m + 7) + (4 * m + 4)) + 1 from by ring]
  step fm
  show ⟨0, 6 * m + 6 + 1, 1 + 1, 4 * m + 5, 0,
    (m + 1) * (6 * m + 7) + (4 * m + 4)⟩ [fm]⊢* _
  -- Phase 4: R211 chain (3m+3 rounds)
  rw [show (m + 1) * (6 * m + 7) + (4 * m + 4) =
    6 * m * m + 17 * m + 11 from by ring]
  nth_rw 1 [show 6 * m + 6 + 1 = 1 + 2 * (3 * m + 3) from by ring]
  nth_rw 1 [show (4 * m + 5 : ℕ) = (m + 2) + (3 * m + 3) from by ring]
  apply stepStar_trans (r211_chain (3 * m + 3) 1 1 (m + 2) 0
    (f := 6 * m * m + 17 * m + 11))
  show ⟨0, 1, 1 + 1 + (3 * m + 3), m + 2, 0 + (3 * m + 3),
    6 * m * m + 17 * m + 11⟩ [fm]⊢* _
  -- Phase 5a: R2+R1
  rw [show 1 + 1 + (3 * m + 3) = (3 * m + 4) + 1 from by ring,
      show (m + 2 : ℕ) = (m + 1) + 1 from by ring,
      show 0 + (3 * m + 3) = 3 * m + 3 from by ring]
  step fm; step fm
  show ⟨1, 0, (3 * m + 4) + 1, m + 1, 3 * m + 3 + 1,
    6 * m * m + 17 * m + 11⟩ [fm]⊢* _
  -- Phase 5b: R2 chain (m+1 R2s)
  rw [show (3 * m + 4) + 1 = (2 * m + 4) + (m + 1) from by ring,
      show 3 * m + 3 + 1 = 3 * m + 4 from by ring]
  nth_rw 2 [show (m + 1 : ℕ) = 0 + (m + 1) from by ring]
  apply stepStar_trans (r2_chain (m + 1) 1 (2 * m + 4) 0 (3 * m + 4)
    (f := 6 * m * m + 17 * m + 11))
  -- Phase 6: R3/R2 spiral
  rw [show 1 + 2 * (m + 1) = (2 * m + 2) + 1 from by ring,
      show (2 * m + 4 : ℕ) = (2 * m + 3) + 1 from by ring,
      show 3 * m + 4 + (m + 1) = 4 * m + 5 from by ring]
  apply stepStar_trans (r3r2_spiral (2 * m + 3) (2 * m + 2) (4 * m + 5)
    (6 * m * m + 17 * m + 11))
  rw [show (2 * m + 2) + (2 * m + 3) + 2 = 4 * m + 7 from by ring,
      show (4 * m + 5) + (2 * m + 3) + 1 = 6 * m + 9 from by ring,
      show 6 * m * m + 17 * m + 11 + (2 * m + 3) + 1 =
        6 * m * m + 19 * m + 15 from by ring]
  finish

-- Odd transition
theorem main_odd (m : ℕ) :
    ⟨4 * m + 5, 0, 0, 0, 6 * m + 6, (m + 1) * (6 * m + 7)⟩ [fm]⊢⁺
    ⟨4 * m + 7, 0, 0, 0, 6 * m + 9, (2 * m + 3) * (3 * m + 5)⟩ := by
  have h := main_odd_aux m
  rw [show (6 * m * m + 19 * m + 15 : ℕ) = (2 * m + 3) * (3 * m + 5) from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 3, 2⟩)
  · execute fm 8
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun m ↦ ⟨4 * m + 3, 0, 0, 0, 6 * m + 3, (2 * m + 1) * (3 * m + 2)⟩) 0
  intro m
  exists m + 1
  exact stepPlus_trans (main_even m) (main_odd m)

end Sz22_2003_unofficial_1166
