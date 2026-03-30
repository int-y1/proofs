import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #681: [35/6, 4/165, 77/2, 3/7, 4/11]

Vector representation:
```
-1 -1  1  1  0
 2 -1 -1  0 -1
-1  0  0  1  1
 0  1  0 -1  0
 2  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_681

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b+1, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | _ => none

theorem d_to_b : ∀ K B D, ⟨(0:ℕ), B, 0, D + K, E⟩ [fm]⊢* ⟨0, B + K, 0, D, E⟩ := by
  intro K; induction' K with K ih <;> intro B D
  · exists 0
  · rw [show D + (K + 1) = (D + K) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (B + 1) D)
    ring_nf; finish

theorem tail_phase : ∀ C D E, ⟨(2:ℕ), 0, C, D, E⟩ [fm]⊢* ⟨0, 0, 0, C + D + 2, C + E + 2⟩ := by
  intro C; induction' C with C ih <;> intro D E
  · step fm; step fm; ring_nf; finish
  · step fm; step fm; step fm; step fm
    apply stepStar_trans (ih (D + 1) (E + 1))
    ring_nf; finish

theorem phase3 : ∀ B, ∀ C D E, B ≤ 2 * E + 1 →
    ⟨(2:ℕ), B, C, D, E⟩ [fm]⊢* ⟨0, 0, 0, B + C + D + 2, C + E + 2⟩ := by
  intro B; induction' B using Nat.strongRecOn with B ih
  intro C D E hB
  rcases B with _ | B
  · -- B = 0
    apply stepStar_trans (tail_phase C D E)
    ring_nf; finish
  · rcases B with _ | B
    · -- B = 1
      step fm; step fm; step fm; step fm
      apply stepStar_trans (tail_phase C (D + 1) E)
      ring_nf; finish
    · rcases B with _ | B
      · -- B = 2
        obtain ⟨E', rfl⟩ : ∃ E', E = E' + 1 := ⟨E - 1, by omega⟩
        step fm; step fm; step fm; step fm
        apply stepStar_trans (tail_phase (C + 1) (D + 1) E')
        ring_nf; finish
      · -- B = B + 3
        obtain ⟨E', rfl⟩ : ∃ E', E = E' + 1 := ⟨E - 1, by omega⟩
        step fm; step fm; step fm
        apply stepStar_trans (ih B (by omega) (C + 1) (D + 2) E' (by omega))
        ring_nf; finish

theorem d_to_b_all : ∀ D, ⟨(0:ℕ), 0, 0, D, E⟩ [fm]⊢* ⟨0, D, 0, 0, E⟩ := by
  intro D
  have h := d_to_b D 0 0 (E := E)
  simp at h
  exact h

theorem main_trans : ⟨(0:ℕ), 0, 0, 2 * n + 1, n + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * (n + 1) + 1, (n + 1) + 1⟩ := by
  apply stepStar_stepPlus_stepPlus (d_to_b_all (2 * n + 1))
  step fm
  apply stepStar_trans (phase3 (2 * n + 1) 0 0 n (by omega))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 2⟩)
  · execute fm 9
  · apply progress_nonhalt_simple (fm := fm) (A := ℕ)
      (fun n ↦ ⟨0, 0, 0, 2 * (n + 1) + 1, (n + 1) + 1⟩) 0
    intro n
    exact ⟨n + 1, main_trans⟩
