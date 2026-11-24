import YM.Bwana.View
import YM.Avena.Wink
import YM.Massive.Ribbon.Graft
/-! Orientation preserves weights up to horizon constant. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Display Papyrus
variable {c : Side} {d : ℕ}
namespace Sieve
set_option maxHeartbeats 1200000
open Stative Plans Plans.Stamp
variable (a:Axis) (x:Pol d)
local notation "A" => Pairs (SpinMode d)
abbrev wakeA (d:ℕ)(a:Axis) : SpinPol d→ₛₗ[starRingEnd ℂ] SpinPol d:= ((changeVars (Matrix.fromBlocks 0 (flipTable a (-(gamma a).transpose)) (flipTable a (-gamma a)) 0)).toLinearMap.comp dagger)
abbrev coal(J:Labels.Jet su):= Labels.changedJet (fun _=> Labels.Taylor.turn (Signed.reflect a)⁻¹) J
local notation "WA"=> wakeA d a
lemma readA (J:Labels.Jet su): ready d J (UV.adj a x)=WA (ready d (coal a J) x):=by
      induction x using TensorProduct.induction_on with
      | zero=> simp
      | tmul x y=> unfold UV.adj; rw [TensorProduct.map_tmul,ready_t,ready_t,map_smulₛₗ]; change Labels.read J (Labels.rotated _ (conjGPol x)) • (WA y) = _; apply congr_arg (fun z:ℂ=> z • WA y); unfold Labels.rotated; rw [Labels.eval_changed,UV.conj_values]; rfl
      | add x y h h'=> simp_rw [map_add,h,h']
lemma wakeKE (t:ℝ)(x:SpinPol d): WA (Kites.engine t A x)= Kites.engine t A (WA x):=by
      rw [← write x]; simp only [map_sum,map_smul,map_smulₛₗ]; refine sum_congr rfl (fun i _=>?_); apply congr_arg; rw[Kites.nominate _ t i.card (homogeneous _),map_smulₛₗ, Kites.nominate (WA (mono i)) _ i.card (show WA (mono i)∈ layer _ i.card from exterior_layer _ (dagger_degree (homogeneous i)))]; simp -- inference
lemma adjust (u v:ℝ) : UV.adj a (Sieve.widths u v x)=Sieve.widths u v (UV.adj a x):=by
     have hp(u v:ℝ)(x:Pol d)(J): ready d J (Sieve.widths u v x)= Kites.engine v A (ready d (u • J) x):=by rw[← one_scene,← one_scene,Sieve.countingG]
     apply distinct; intro J; rw [readA,hp,hp,readA, show coal a (u • J)=u • coal a J from funext fun i=>map_smul (Labels.Taylor.turn (Signed.reflect a)⁻¹) u (J i)]; exact wakeKE ..
variable (d:ℕ)(F:RawSym)
lemma movesAD (u v:ℝ)(x: Label d): dimming u v d (F.adj d a x)= F.adj d a (dimming u v d x):=by
     apply Subtype.ext; change Sieve.widths u v (F.adj d a x).val = _; rw [F.adjActs,F.adjActs]; exact (adjust ..).symm
-- norm bound via treating as semi. α∀
lemma boothD :∃ C:ℝ,1 ≤ C∧∀ (a:Axis)(u v:ℝ)(x:Label d),‖dimming u v d (F.adj d a x)‖ ≤ C* ‖dimming u v d x‖:=by
      let B:= Module.finBasis ℂ (Label d); let I:= Fin (Module.finrank ℂ (Label d)); let X (i:I): Label d→L[ℂ]ℂ:= (B.coord i).toContinuousLinearMap; let VT (a:Axis):=∑ i:I, ‖X i‖* ‖F.adj d a (B i)‖; have h(a:Axis)(x:Label d): ‖F.adj d a x‖ ≤ VT a*‖x‖:=by
           conv_lhs => rw [show x= ∑ i:I, X i x • B i from (B.sum_repr x).symm,map_sum]
           apply (norm_sum_le ..).trans; unfold VT; rw[sum_mul]; refine Finset.sum_le_sum fun i _=>?_ ; rw [map_smulₛₗ,norm_smul,show ‖starRingEnd ℂ (X i x)‖ = ‖X i x‖ from norm_star _]; exact (mul_le_mul_of_nonneg_right ((X i).le_opNorm x) (norm_nonneg _)).trans_eq (by ring)
      obtain ⟨V,hV⟩:= (Set.finite_range VT).bddAbove; refine ⟨max 1 V,le_max_left ..,fun a u v x=>?_⟩; rw [movesAD]; exact (h a _).trans (mul_le_mul_of_nonneg_right ((hV ⟨a,rfl⟩).trans (le_max_right ..)) (norm_nonneg _))
open Stative Plans Plans.Stamp
lemma bill_su :∃ C:ℝ,1≤ C∧∀ (t:List Axis),t.length≤8→∀ (u v:ℝ)(x:Label d), wealth (Massive.Patria.Hub.spine F x t).val u v ≤ C*‖dimming u v d x‖:=by
       obtain ⟨M,hM,H⟩:= boothD d F; have h(l:List Axis)(u v:ℝ)(x:Label d): ‖dimming u v d (Massive.Patria.Hub.spine F x l)‖ ≤ M^l.length*‖dimming u v d x‖:=by
           induction l with
           | nil=>simp [Massive.Patria.Hub.spine]
           | cons a l ih=>rw[Massive.Patria.Hub.spine]; exact (H ..).trans ((mul_le_mul_of_nonneg_left ih (zero_le_one.trans hM)).trans_eq (by simp only [List.length_cons,pow_succ']; ring))
       obtain ⟨b,k,hb,hk,hp⟩:=Plans.Stamp.Stair.Cabin.wNorm d
       refine ⟨k*M^8, one_le_mul_of_one_le_of_one_le hk (one_le_pow₀ hM),fun t ht u v x=>?_⟩; exact (hp u v _).2.trans ((mul_le_mul_of_nonneg_left ((h ..).trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hM ht) (norm_nonneg _))) (zero_le_one.trans hk)).trans_eq (by ring))
end Sieve
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Sieve.bill_su
