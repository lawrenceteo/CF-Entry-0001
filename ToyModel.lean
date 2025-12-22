import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic

/-!
# ToyModel.lean
Entry 0001: Cognitive Formalism (CF) Toy Model
Lean 4.27.0-rc1 + Mathlib master
-/

/-- Public Semantic Subspace (So) is modeled as the x-axis in ℝ². -/
def So : Set (ℝ × ℝ) := { v | v.2 = 0 }

/-- Private Subspace (Sd) is modeled as the y-axis in ℝ². -/
def Sd : Set (ℝ × ℝ) := { v | v.1 = 0 }

/-- An update U is admissible if it maps So into So and is norm-bounded. -/
def Admissible (U : ℝ × ℝ → ℝ × ℝ) : Prop :=
  ∀ x ∈ So, U x ∈ So ∧ ‖U x‖ ≤ (1 + 0.1) * ‖x‖

/-- A PLA update leaks into Sd or grows beyond tolerance. -/
def PLA (U : ℝ × ℝ → ℝ × ℝ) : Prop :=
  ∃ x ∈ So, (U x ∈ Sd) ∨ (‖U x‖ > (1 + 0.1) * ‖x‖)

/-- Theorem A: PLA updates violate CISI admissibility. -/
theorem PLA_violates_CISI (U : ℝ × ℝ → ℝ × ℝ) :
    PLA U → ¬ Admissible U := by sorry

/-- SHP pruning functional: project any vector back onto So. -/
def H (v : ℝ × ℝ) : ℝ × ℝ := (v.1, 0)

/-- Theorem B: SHP pruning correctness. -/
theorem SHP_pruning_correctness (U : ℝ × ℝ → ℝ × ℝ) (x : ℝ × ℝ) (hx : x ∈ So) :
    H (U x) ∈ So ∧ ‖H (U x) - U x‖ = ‖(0, (U x).2)‖ := by sorry
