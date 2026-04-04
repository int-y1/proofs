import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1831: [9/10, 7/2, 44/21, 5/11, 66/7]

Vector representation:
```
-1  2 -1  0  0
-1  0  0  1  0
 2 -1  0 -1  1
 0  0  1  0 -1
 1  1  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1831

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b+1, c, d, e+1⟩
  | _ => none

theorem r4_chain : ∀ k, ⟨(0 : ℕ), 0, 0, d, e + k⟩ [fm]⊢* ⟨0, 0, k, d, e⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · rw [show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih (e := e + 1))
    step fm; finish

theorem drain : ∀ k, ⟨(0 : ℕ), b + k, 0, d + 1, e⟩ [fm]⊢* ⟨0, b, 0, d + k + 1, e + k⟩ := by
  intro k; induction' k with k ih generalizing b d e
  · exists 0
  · rw [show b + (k + 1) = b + k + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (d := d + 1) (e := e + 1))
    ring_nf; finish

theorem interleaved : ∀ k, ⟨(0 : ℕ), b + 1, c + 2 * k + 1, d + k + 1, E⟩ [fm]⊢*
    ⟨0, b + 3 * k + 1, c + 1, d + 1, E + k⟩ := by
  intro k; induction' k with k ih generalizing b c d E
  · exists 0
  · rw [show c + 2 * (k + 1) + 1 = (c + 2) + 2 * k + 1 from by ring,
        show d + (k + 1) + 1 = (d + 1) + k + 1 from by ring]
    apply stepStar_trans (ih (b := b) (c := c + 2) (d := d + 1) (E := E))
    rw [show b + 3 * k + 1 = (b + 3 * k) + 1 from by ring,
        show c + 2 + 1 = (c + 1) + 1 + 1 from by ring,
        show d + 1 + 1 = (d + 1) + 1 from by ring]
    step fm; step fm; step fm
    ring_nf; finish

theorem ev0_trans : ⟨(0 : ℕ), 0, 0, F + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, 0, F + 2, 2⟩ := by
  execute fm 5

theorem main_trans : ∀ ev, ⟨(0 : ℕ), 0, 0, ev + F + 2, 2 * ev + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, 3 * ev + F + 5, 4 * ev + 6⟩ := by
  intro ev
  -- Phase 1: R4 chain
  rw [show (2 * ev + 2 : ℕ) = 0 + (2 * ev + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (2 * ev + 2) (d := ev + F + 2) (e := 0))
  -- Now at (0, 0, 2*ev+2, ev+F+2, 0), goal is ⊢⁺
  -- Phase 2: R5 + R1
  rw [show ev + F + 2 = (ev + F + 1) + 1 from by ring,
      show (2 * ev + 2 : ℕ) = (2 * ev + 1) + 1 from by ring]
  step fm; step fm
  -- Now at (0, 3, 2*ev+1, ev+F+1, 1), goal is ⊢*
  -- Phase 3: Interleaved chain
  rw [show (3 : ℕ) = 2 + 1 from by ring,
      show (2 * ev + 1 : ℕ) = 0 + 2 * ev + 1 from by ring,
      show ev + F + 1 = F + ev + 1 from by ring]
  apply stepStar_trans (interleaved ev (b := 2) (c := 0) (d := F) (E := 1))
  -- Now at (0, 2+3*ev+1, 0+1, F+1, 1+ev)
  -- Phase 4: Partial round R3+R1+R2
  rw [show 2 + 3 * ev + 1 = (3 * ev + 2) + 1 from by ring,
      show 1 + ev = ev + 1 from by ring]
  step fm; step fm; step fm
  -- Now at (0, 3*ev+4, 0, F+1, ev+1+1)
  -- Phase 5: Drain
  rw [show ev + 1 + 1 = ev + 2 from by ring,
      show (3 * ev + 4 : ℕ) = 0 + (3 * ev + 4) from by ring,
      show F + 1 = F + 0 + 1 from by ring]
  apply stepStar_trans (drain (3 * ev + 4) (b := 0) (d := F + 0) (e := ev + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0 + 0 + 1, 2 * 0⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨ev, F⟩ ↦ ⟨0, 0, 0, ev + F + 1, 2 * ev⟩) ⟨0, 0⟩
  intro ⟨ev, F⟩
  rcases ev with _ | ev
  · refine ⟨⟨1, F⟩, ?_⟩
    show ⟨(0 : ℕ), 0, 0, 0 + F + 1, 2 * 0⟩ [fm]⊢⁺ ⟨0, 0, 0, 1 + F + 1, 2 * 1⟩
    rw [show 0 + F + 1 = F + 1 from by ring,
        show (2 * 0 : ℕ) = 0 from by ring,
        show 1 + F + 1 = F + 2 from by ring,
        show (2 * 1 : ℕ) = 2 from by ring]
    exact ev0_trans
  · refine ⟨⟨2 * ev + 3, ev + F + 1⟩, ?_⟩
    show ⟨(0 : ℕ), 0, 0, (ev + 1) + F + 1, 2 * (ev + 1)⟩ [fm]⊢⁺
      ⟨0, 0, 0, (2 * ev + 3) + (ev + F + 1) + 1, 2 * (2 * ev + 3)⟩
    rw [show (ev + 1) + F + 1 = ev + F + 2 from by ring,
        show 2 * (ev + 1) = 2 * ev + 2 from by ring,
        show (2 * ev + 3) + (ev + F + 1) + 1 = 3 * ev + F + 5 from by ring,
        show 2 * (2 * ev + 3) = 4 * ev + 6 from by ring]
    exact main_trans ev
