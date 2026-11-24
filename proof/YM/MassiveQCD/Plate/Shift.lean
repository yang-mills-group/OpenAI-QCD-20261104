import YM.MassiveQCD.Plate.Roof
/-! # Wear orientation of real transmission postage (may be fed through non-real test radii)
 Control actually-projected spins in physical or counted units. Intended for K-merge coherence
 and projection locations without fake spins. Every calibration in these lemmas
 relative to declared normalization.s
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Plate
open QCD QCD.Grass QCD.Cove QCD.Creek QCD.Lat Lattice Finset RG Wilson Ribbon Function Loom Fleet
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff Classical Matrix Kronecker
variable {c:Side}{N:ℕ}{I D E J:Type}[Fintype I][Fintype D]
variable {a b:ℝ}
local notation "K"=> Keys c N
local notation "R"=> Spine I
local notation "X"=> K⊕Spine I
local notation "Y"=> D⊕Spine I
local notation "M"=> ample N I
variable (I) (t:ℝ)
open Patron Sway OrbitG Villa Stitch Apron Kites Cupola
noncomputable def turn (t:ℝ): Patio (D⊕Spine I)→ₐ[ℂ]Patio (D⊕Spine I):=by
   let F:= (Kites.engine t D); let w:= F.toLinearMap.toContinuousLinearMap
   let p:= carry (Spine I) w; have hp (x: Alg D): w (grade x)= grade (w x):=(exterior_parity _ _).symm
   let R₁:= (roomA (D⊕Spine I)).toSubmodule; let q:= (p.toLinearMap.comp (light _).toLinearMap).codRestrict R₁ (fun i=> evenCarry (Spine I) w hp i.val (bright i)); refine AlgHom.ofLinearMap q (Subtype.ext ?_) (fun i j=> Subtype.ext (ledger_alg F hp i.val j.val)); change carry _ w 1=1; rw [← map_one (fiber (A:=D) (Spine I)),← quiet,speaks, show w 1=1 from map_one F]
lemma turned (x: Patio (D⊕Spine I))(v:Finset (Spine I)): pluck D v (turn I t x)=engine t D (pluck D v x):= wing (Spine I) _ _ _
variable {I}
lemma cloak (s:Finset I)(x: Patio Y)(q:I→Bool)(h:Polite q s x): Polite q s (turn I t x):= politeStep (engine t D).toLinearMap.toContinuousLinearMap h rfl
lemma freight (x: Patio Y)(q:I→Bool)(h:ValidPieces D q Finset.univ x):ValidPieces D q Finset.univ (turn I t x):=by rw [h.wholeV,map_sum]; exact ValidPieces.cost _ _ (fun i _=> ValidPieces.role _ (cloak t i _ q (choseTuft ..)) (subset_univ i))
lemma freeTurn (x: Patio X) : vacR R K (turn I t x) = wearK c N t (vacR R K x):=by
    apply Subtype.ext; change resetM _ K _= engine t K (resetM R K _); rw [revive,revive]; exact turned I t x _
lemma freeT (x:Patio X)(V: Frame c): turn I t (parcelColor N V I x)= parcelColor N V I (turn I t x) := by
    apply pluckVisible; intro j; rw [turned,partColor,partColor,turned]; exact (Kites.pitcher (Lat.rotates N V) _ t).symm
-- TINE maps over tape cost & class
variable (N)(p:I→Site c) (t φ θ:ℝ) (q:I→Bool)
noncomputable def changeBill : EvenA c (ample N I) →ₐ[ℂ] EvenA c (ample N I) := ((banknote N p θ).comp (turn I t)).comp (withdraw N p φ)
local notation "pay"=> changeBill N p t φ θ -- order reset actual binders t earlier defined section! check sig
lemma changeLife (φ' t' :ℝ)(x: EvenA c (ample N I))(h:0<θ): withdraw N p θ (changeBill N p t' φ' θ x)= turn I t' (withdraw N p φ' x):= home N p θ h _
-- notation.Vault
lemma changeValid (h:0<θ)(x: EvenA c (ample N I))(hp:Well N p φ q x): Well N p θ q (pay x):=by have he:=changeLife N p θ φ t x h; refine ⟨congr_arg (banknote N p θ) he,?_⟩; rw [he]; exact freight t _ q hp.applies
lemma changeColor (x: EvenA c (ample N I))(z: Lat.Frame c)(hp:Well N p φ q x)(h:0<φ): pay (sways (Lat.rotates (ample N I) z) x)= sways (Lat.rotates (ample N I) z) (pay x) :=by
   let y:= withdraw N p φ x; let V:= parcelColor N z I
   have hx: withdraw N p φ (sways (Lat.rotates M z) x)= V y:=by
      refine Eq.trans ?_ (home N p φ h (V y)); exact congr_arg (withdraw N p φ) ((congr_arg _ hp.spark.symm).trans (all_color N p φ q z y hp.applies).symm)
   unfold changeBill; simp only [AlgHom.comp_apply]; rw [hx]; exact (congr_arg (banknote N p θ) (freeT t y z)).trans (all_color N p θ q z _ (freight t y q hp.applies))
-- uses same interior marker projector, even before material.C. 
lemma hopeful (x:Alg K)(S:Support c)(h:x∈region (limits S)): Kites.engine t (Keys c N) x∈region (limits S):=by
    refine effects (engine _ _) ?_ x h; intro i hi; unfold engine; rw [change_atom]; apply Subalgebra.sum_mem; intro j _; by_cases ht:j=i; · subst j; exact Subalgebra.smul_mem _ (marked _ _ hi) _
    rw [Matrix.diagonal_apply_ne _ (Ne.symm ht),zero_smul]; exact Subalgebra.zero_mem _
lemma change_L (x: EvenA c (ample N I))(S:Support c)(hp:Gated S x):Gated S (pay x):=by
   let y:= withdraw N p φ x; change pen N p θ (light _ (turn I t y))∈_; rw [← Ribbon.rewriteR (Keys c N) (light _ (turn I t y)),map_sum]; apply Subalgebra.sum_mem; intro i _; change pen N p θ (stake _ i (pluck (Keys c N) i (turn I t y)))∈_; rw [turned]; by_cases he: i⊆limitQ p S
   · exact entitled N p θ S i _ (hopeful N t _ _ (pennied N p φ i x S hp)) fun i hx=> (mem_filter.mp (he hx)).2
   rw [show pluck _ i y=0 from confined N p φ i x S hp he,map_zero,map_zero,map_zero]; exact Subalgebra.zero_mem _
include q in -- retained.Envelope.Eq
lemma changeCoin (x: EvenA c (ample N I))(hp:Well N p φ q x)(ht:0 < t)(hz:0<θ)(hw:t*θ ≤ φ) : ‖token c (ample N I) θ (pay x)‖ ≤ ‖token c (ample N I) φ x‖:=by
   have hh := (mul_pos ht hz).trans_le hw; let y:= withdraw N p φ x
   have hf : banknote N p φ y=x:= hp.spark; change ‖token c (ample N I) θ (banknote N p θ (turn I t y))‖ ≤_; rw [Loom.pulse,Loom.pulse,withdrawCost N p θ hz]; nth_rw 1 [← hf] -- only RHS x? folded y and x hidden. edit
   rw [withdrawCost N p φ hh]; refine sum_le_sum fun i _=>?_ ; rw [turned]; let v:=pluck _ i y; change ‖Kites.engine θ K (engine t K v)‖≤‖engine φ K v‖; rw [Kites.makes]; have hX:0<θ*t:=mul_pos hz ht
   rw [Grass.norm_def,Grass.norm_def]; apply sum_le_sum; intro j _; rw [fundW,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hX.le,fundW,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hh.le,mul_comm θ]; gcongr
end YM.MassiveQCD.Plate
#print axioms YM.MassiveQCD.Plate.changeCoin
