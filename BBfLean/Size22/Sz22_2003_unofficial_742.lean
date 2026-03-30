import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #742: [35/6, 4/55, 1573/2, 3/7, 35/13]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  0
-1  0  0  0  2  1
 0  1  0 -1  0  0
 0  0  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_742

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+2, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | _ => none

theorem r3_drain : ∀ k, ∀ a d e f, ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 2) (f + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ b d e f, ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e f)
    ring_nf; finish

theorem r2_drain : ∀ k, ∀ a d e f, ⟨a, 0, k, d, e + k, f⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) d e f)
    ring_nf; finish

theorem interleaved : ∀ b, ∀ C D E F,
    ⟨(0 : ℕ), b, C + 1, D, E + (C + 1 + b), F⟩ [fm]⊢* ⟨2 * C + b + 2, 0, 0, D + b, E, F⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih
  rcases b with _ | _ | b
  · intro C D E F
    rw [show C + 1 + 0 = C + 1 from by ring,
        show 2 * C + 0 + 2 = 0 + 2 * (C + 1) from by ring,
        show D + 0 = D from by ring]
    exact r2_drain (C + 1) 0 D E F
  · intro C D E F
    rw [show E + (C + 1 + 1) = (E + (C + 1)) + 1 from by ring]
    step fm; step fm
    rw [show 2 * C + 1 + 2 = 1 + 2 * (C + 1) from by ring]
    exact r2_drain (C + 1) 1 (D + 1) E F
  · intro C D E F
    rw [show E + (C + 1 + (b + 2)) = (E + (C + 1 + (b + 1))) + 1 from by ring]
    step fm; step fm; step fm
    rw [show C + 1 + (b + 1) = (C + 1) + 1 + b from by ring,
        show D + 1 + 1 = (D + 2 : ℕ) from by ring]
    apply stepStar_trans (ih b (by omega) (C + 1) (D + 2) E F)
    rw [show 2 * (C + 1) + b + 2 = 2 * C + (b + 2) + 2 from by ring,
        show D + 2 + b = D + (b + 2) from by ring]
    finish

theorem phase1 (n f : ℕ) :
    ⟨n + 1, 0, 0, n, f + n, f⟩ [fm]⊢⁺ ⟨0, 0, 0, n, f + 3 * n + 2, f + n + 1⟩ := by
  apply stepStar_stepPlus
  · rw [show n + 1 = 0 + (n + 1) from by ring,
        show f + 3 * n + 2 = f + n + 2 * (n + 1) from by ring,
        show f + n + 1 = f + (n + 1) from by ring]
    exact r3_drain (n + 1) 0 n (f + n) f
  · intro h; injection h with h; omega

theorem phase234 (n f : ℕ) :
    ⟨0, 0, 0, n, f + 3 * n + 2, f + n + 1⟩ [fm]⊢* ⟨n + 2, 0, 0, n + 1, f + 2 * n + 1, f + n⟩ := by
  rw [show (n : ℕ) = 0 + n from by omega,
      show f + 3 * (0 + n) + 2 = f + 3 * n + 2 from by ring,
      show f + (0 + n) + 1 = f + n + 1 from by ring]
  apply stepStar_trans (r4_chain n 0 0 (f + 3 * n + 2) (f + n + 1))
  rw [show 0 + n = n from by ring,
      show f + n + 1 = (f + n) + 1 from by ring]
  step fm -- R5
  rw [show f + 3 * n + 2 = (f + 2 * n + 1) + (0 + 1 + n) from by ring]
  apply stepStar_trans (interleaved n 0 1 (f + 2 * n + 1) (f + n))
  rw [show 2 * 0 + n + 2 = n + 2 from by ring,
      show 1 + n = n + 1 from by ring]
  finish

theorem main_trans (n f : ℕ) :
    ⟨n + 1, 0, 0, n, f + n, f⟩ [fm]⊢⁺ ⟨n + 2, 0, 0, n + 1, f + 2 * n + 1, f + n⟩ :=
  stepPlus_stepStar_stepPlus (phase1 n f) (phase234 n f)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 1, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨p.1 + 1, 0, 0, p.1, p.2 + p.1, p.2⟩) ⟨1, 0⟩
  intro ⟨n, f⟩
  refine ⟨⟨n + 1, f + n⟩, ?_⟩
  show (n + 1, 0, 0, n, f + n, f) [fm]⊢⁺
    ((n + 1) + 1, 0, 0, n + 1, (f + n) + (n + 1), f + n)
  have key := main_trans n f
  rw [show (n + 1) + 1 = n + 2 from by ring,
      show (f + n) + (n + 1) = f + 2 * n + 1 from by ring]
  exact key

end Sz22_2003_unofficial_742
