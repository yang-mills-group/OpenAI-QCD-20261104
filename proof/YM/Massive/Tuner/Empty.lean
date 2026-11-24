import YM.QCD.Finch.Cool

/-!
# Deterministic reference action is normalized at the identity
-/

set_option autoImplicit false
noncomputable section
namespace YM.Massive.Pressure
open Lattice RG Wilson Precision QCD QCD.Lat Finset
open scoped BigOperators Topology Matrix.Norms.Frobenius
variable {n : Side} {k : ℕ} {G : Gauge}

lemma spin_one (s : Signed) : pull s 0 (1:Config G n)=1:=by
  funext i; unfold pull Step.read; split <;> simp

lemma slot_flat (s : Slot) (i : Site n) : s.atSite (1:Config G n) i = 0:=by
  unfold Slot.atSite Slot.eval
  apply norm_le_zero_iff.mp; rw [Gauge.norm_adjoint]; apply (G.curvature_norm _).trans
  have he : faceValue (expandAt i (1:Config G n)) (s.offset,s.plaq)=1:=by simp [faceValue, travel,Lattice.square, expandAt]
  rw [he,G.chord_one]

lemma bare_flat [NeZero k] (s : Atom G k) (i : Site n) : s.unmasked (1:Config G n) i = 0:=by
  classical
  simp [Atom.unmasked, Atom.poly, slot_flat, NeZero.ne k]

lemma loop_flat [NeZero k] (s : ℕ → Atom G k) (b : BudgetPoint) (i : Site n) : PathData.atomSeries s b (1:Config G n) i=0:=by
  classical
  unfold PathData.atomSeries
  have h (j : ℕ) : (s j).placed b (1:Config G n) i=0 :=by
    unfold Atom.placed
    by_cases hu : Healthy b.threshold ((s j).footprint i) (1:Config G n)
    · rw [masked_eq _ _ _ _ hu]; exact bare_flat ..
    exact masked_ne _ _ _ _ hu
  simp_rw [h,tsum_zero]

lemma channels_one (F : PathData G) (t : Clip) (p : BudgetPoint) (β : ℝ) : F.inChannels t p β (1:Config G n)=0:=by
  classical
  unfold PathData.inChannels PathData.principal
  simp_rw [spin_one]; have hh (f : Face (Per n)) : F.baseTerm t p 1 f=0:=by
    unfold PathData.baseTerm; rw [WilsonStartup.face_one, G.chord_one]; simp [PathData.clipped, PathData.ell, PathData.ellTerms, slot_flat, p.threshold_pos.le]
  simp only [hh, sum_const_zero, loop_flat, add_zero,mul_zero]

lemma uncut_flat [NeZero k] (F : ℕ→ Atom G k) : Extra.Iteration.action F (1: Config G n)=0:=by
  unfold Extra.Iteration.action
  simp_rw [spin_one]
  simp [Patch.average, uncut,bare_flat]

lemma scent_one (W : ℕ→Atom su 2) (F : PathData su) (t : Clip) (p : BudgetPoint) (N : ℕ) (β : ℝ) :
    Finch.scent W p F t β 0 N (1:Grid n)=0:=by simp [Finch.scent, Reggae.pulse,uncut_flat,channels_one]
end YM.Massive.Pressure
#print axioms YM.Massive.Pressure.scent_one
