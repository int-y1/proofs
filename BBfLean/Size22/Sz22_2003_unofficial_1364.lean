import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1364: [63/10, 4/33, 847/2, 5/7, 2/11]

Vector representation:
```
-1  2 -1  1  0
 2 -1  0  0 -1
-1  0  0  1  2
 0  0  1 -1  0
 1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1364

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

theorem r3_drain : ∀ k, ∀ d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + k, e + 2 * k⟩ := by
  intro k; induction' k with k ih
  · intro d e; exists 0
  · intro d e; step fm
    apply stepStar_trans (ih (d + 1) (e + 2)); ring_nf; finish

theorem r4_drain : ∀ k, ∀ c e, ⟨0, 0, c, k, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro c e; exists 0
  · intro c e; rw [Nat.add_succ]; step fm
    apply stepStar_trans (ih (c + 1) e); ring_nf; finish

theorem r2_drain : ∀ k, ∀ a b d, ⟨a, b + k, 0, d, k⟩ [fm]⊢* ⟨a + 2 * k, b, 0, d, 0⟩ := by
  intro k; induction' k with k ih
  · intro a b d; exists 0
  · intro a b d
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) b d); ring_nf; finish

theorem r1r1r2_chain : ∀ k, ∀ b d e,
    ⟨2, b, 2 * k, d, e + k⟩ [fm]⊢* ⟨2, b + 3 * k, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih
  · intro b d e; exists 0
  · intro b d e
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (b + 3) (d + 2) e); ring_nf; finish

theorem r3r2r2_chain : ∀ k, ∀ a d,
    ⟨a + 1, 2 * k, 0, d, 0⟩ [fm]⊢* ⟨a + 3 * k + 1, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih
  · intro a d; exists 0
  · intro a d
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 3) (d + 1)); ring_nf; finish

theorem phase3_even (a K d : ℕ) :
    ⟨a + 1, 2 * K, 0, d, 0⟩ [fm]⊢* ⟨0, 0, d + a + 4 * K + 1, 0, 2 * a + 6 * K + 2⟩ := by
  apply stepStar_trans (r3r2r2_chain K a d)
  apply stepStar_trans (r3_drain (a + 3 * K + 1) (d + K) 0)
  apply stepStar_trans (r4_drain (d + K + (a + 3 * K + 1)) 0 (0 + 2 * (a + 3 * K + 1)))
  ring_nf; finish

theorem phase3_odd : ∀ K, ∀ a d,
    ⟨a + 1, 2 * K + 1, 0, d, 0⟩ [fm]⊢* ⟨0, 0, d + a + 4 * K + 3, 0, 2 * a + 6 * K + 5⟩ := by
  intro K; induction' K with K ih
  · intro a d
    step fm; step fm; step fm
    apply stepStar_trans (r3_drain (a + 1) (d + 2) 3)
    apply stepStar_trans (r4_drain (d + 2 + (a + 1)) 0 (3 + 2 * (a + 1)))
    ring_nf; finish
  · intro a d
    rw [show 2 * (K + 1) + 1 = 2 * K + 3 from by ring]
    step fm; step fm; step fm
    rw [show a + 4 = (a + 3) + 1 from by ring]
    apply stepStar_trans (ih (a + 3) (d + 1))
    ring_nf; finish

theorem main_trans_even (m j : ℕ) (hj : j ≤ m) :
    ⟨0, 0, 2 * m + 1, 0, 2 * m + 2 * j + 2⟩ [fm]⊢⁺
    ⟨0, 0, 8 * m + 5, 0, 10 * m + 2 * j + 7⟩ := by
  step fm; step fm; step fm
  rw [show 2 * m + 2 * j = (m + 2 * j) + m from by ring]
  apply stepStar_trans (r1r1r2_chain m 1 1 (m + 2 * j))
  rw [show 1 + 3 * m = (2 * m + 1 - 2 * j) + (m + 2 * j) from by omega,
      show 1 + 2 * m = 2 * m + 1 from by ring]
  apply stepStar_trans (r2_drain (m + 2 * j) 2 (2 * m + 1 - 2 * j) (2 * m + 1))
  rw [show 2 + 2 * (m + 2 * j) = (2 * m + 4 * j + 1) + 1 from by ring,
      show 2 * m + 1 - 2 * j = 2 * (m - j) + 1 from by omega]
  apply stepStar_trans (phase3_odd (m - j) (2 * m + 4 * j + 1) (2 * m + 1))
  rw [show 2 * m + 1 + (2 * m + 4 * j + 1) + 4 * (m - j) + 3 = 8 * m + 5 from by omega,
      show 2 * (2 * m + 4 * j + 1) + 6 * (m - j) + 5 = 10 * m + 2 * j + 7 from by omega]
  finish

theorem main_trans_odd (m j : ℕ) (hj : j ≤ m) :
    ⟨0, 0, 2 * m + 1, 0, 2 * m + 2 * j + 3⟩ [fm]⊢⁺
    ⟨0, 0, 8 * m + 5, 0, 10 * m + 2 * j + 8⟩ := by
  step fm; step fm; step fm
  rw [show 2 * m + 2 * j + 1 = (m + 2 * j + 1) + m from by ring]
  apply stepStar_trans (r1r1r2_chain m 1 1 (m + 2 * j + 1))
  rw [show 1 + 3 * m = (2 * m - 2 * j) + (m + 2 * j + 1) from by omega,
      show 1 + 2 * m = 2 * m + 1 from by ring]
  apply stepStar_trans (r2_drain (m + 2 * j + 1) 2 (2 * m - 2 * j) (2 * m + 1))
  rw [show 2 + 2 * (m + 2 * j + 1) = (2 * m + 4 * j + 3) + 1 from by ring,
      show 2 * m - 2 * j = 2 * (m - j) from by omega]
  apply stepStar_trans (phase3_even (2 * m + 4 * j + 3) (m - j) (2 * m + 1))
  rw [show 2 * m + 1 + (2 * m + 4 * j + 3) + 4 * (m - j) + 1 = 8 * m + 5 from by omega,
      show 2 * (2 * m + 4 * j + 3) + 6 * (m - j) + 2 = 10 * m + 2 * j + 8 from by omega]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 21, 0, 28⟩)
  · execute fm 68
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ m r, q = ⟨0, 0, 2 * m + 1, 0, 2 * m + r + 2⟩ ∧ r ≤ 2 * m + 1)
  · intro q ⟨m, r, hq, hr⟩
    subst hq
    rcases Nat.even_or_odd r with ⟨j, hj⟩ | ⟨j, hj⟩
    · subst hj
      refine ⟨⟨0, 0, 8 * m + 5, 0, 10 * m + 2 * j + 7⟩,
        ⟨4 * m + 2, 2 * m + 2 * j + 1, ?_, ?_⟩, ?_⟩
      · ring_nf
      · omega
      · rw [show j + j = 2 * j from by ring]
        exact main_trans_even m j (by omega)
    · subst hj
      refine ⟨⟨0, 0, 8 * m + 5, 0, 10 * m + 2 * j + 8⟩,
        ⟨4 * m + 2, 2 * m + 2 * j + 2, ?_, ?_⟩, ?_⟩
      · ring_nf
      · omega
      · rw [show 2 * m + (2 * j + 1) + 2 = 2 * m + 2 * j + 3 from by ring]
        exact main_trans_odd m j (by omega)
  · exact ⟨10, 6, by ring_nf, by omega⟩

end Sz22_2003_unofficial_1364
