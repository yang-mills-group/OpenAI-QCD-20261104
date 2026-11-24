import YM.Rebus.Hurts
import YM.Play.Cause
import YM.Cape.Peace
/-! # Common ownership W. Awakening exact by Brief. Calculus upcoming. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Rebus
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Cape Play Play.Chamber QCD.Bera QCD.Anomaly Hypnos Hypnos.Fruit Rot
open Play.Camp
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{J K':Patch}{P:Teller su}{β x C μ W:ℝ}
variable {O:BudgetPoint}{ι κ I Z E D:Type}[Fintype I]
variable {N i j n k m l r t M B Q:ℕ}
section
-- forecast salary sF,ε etc.
variable {δ q₀ κ₀ σ η u v r r' t d a a' z w w' s C μ:ℝ}
variable (L':Flight i j)(x:f.val=c.val*L'.L.val){P₀: Run.St f}
variable (G:Jets.Sun L' c f x η r z a a' m P₀)
local notation "Ry"=> sliceL L' x
local notation "X0"=> Dh f N I
local notation "X1"=> Dh c N I
variable (p:I→Site f) (Z:Finset I)
local notation "D0"=> shock Z (spineP p N (majorT l*Q))
local notation "M"=> kpit L' x N B I
-- cheaper stencil metrics on ENTIRE root rail
structure Spins (N B:ℕ)(s :ℝ) :Prop where
    meter i: (∑ j:Keys c N,‖wheelsF N L' x i j‖) ≤ s
    issue i j: ‖spider N L' x i j‖ ≤ s
    pos : 1 ≤ s
variable (ht: Spins L' x N B s)
local notation "Ω"=>sfan L' x N B I
open Matrix
lemma bills_br {Y Y':Type}[Fintype Y][Fintype Y'] (M₀: Matrix Y Y' ℂ) (A:Finset (Y⊕I)) [DecidableEq I] (h:1 ≤ s) (hp:∀ i,∑ j,‖M₀ i j‖ ≤ s): Anomaly.bills (breezeP I M₀) A s:=by
   rintro (i|j) hi
   · rw [Fintype.sum_sum_type]; simpa only [breezeP, fromBlocks_apply₁₂,Matrix.zero_apply,norm_zero, Finset.sum_const_zero,add_zero,fromBlocks_apply₁₁] using hp i
   rw [Fintype.sum_sum_type]; simpa [breezeP,one_apply,apply_ite (fun x:ℂ=>‖x‖)] using h -- expr notation fix
lemma bills_cut {Y Y':Type}[Fintype Y][Fintype Y'] (M₀ M₁:Matrix Y Y' ℂ)(A:Finset (Y⊕I)) [DecidableEq I] (hs:0≤ s)(h:∀ i,Sum.inl i∈A → ∑ j,‖M₀ i j-M₁ i j‖≤ s): Anomaly.bills (breezeP I M₀-breezeP I M₁) A s:=by
    rintro (i|i) hi<;> rw [Fintype.sum_sum_type]
    · simpa only [Matrix.sub_apply,breezeP,fromBlocks_apply₁₂,fromBlocks_apply₁₁,Matrix.zero_apply,sub_zero,norm_zero,Finset.sum_const_zero,add_zero] using h i hi
    simpa only [Matrix.sub_apply,breezeP,fromBlocks_apply₂₂,fromBlocks_apply₂₁,sub_self,norm_zero,Finset.sum_const_zero,add_zero] using hs
lemma stamp_norm {A :Type} (P:Matrix A A ℂ) (Y:Finset (Pairs A⊕I)) (he: ∀ i: A,Sum.inl (Sum.inl i)∈ Y→∀ j, ‖P i j‖≤ s)(hs:0≤ s): ∀ i∈Y,∀ j,‖breezeX I (stamping P) i j‖ ≤ s:=by
   rintro ((a|a)|a) hi ((b|b)|b) <;> first| exact he _ hi _| exact (by change ‖(0:ℂ)‖ ≤ _; rw [norm_zero]; exact hs)
lemma stamps_diff {A: Type} (P Q:Matrix A A ℂ) (Y: Finset (Pairs A⊕I))(he:∀ i:A,Sum.inl (Sum.inl i)∈Y → ∀ j,‖P i j-Q i j‖≤ s)(hs:0≤ s):∀ i∈Y,∀ j,‖breezeX I (stamping P) i j-breezeX I (stamping Q) i j‖ ≤ s :=by
   rintro ((a|a)|a) hi ((b|b)|b) <;> first| exact he _ hi _| exact (by change ‖(0:ℂ)-0‖ ≤ _; rw [sub_zero,norm_zero]; exact hs)
include ht
lemma sailing (A:Finset X0): Anomaly.bills M A s ∧ (∀ i∈A,∀ j∈A,‖Ω i j‖ ≤ s):=by
    have hs:=zero_le_one.trans ht.pos
    have hz (i j:Modes f N): ‖shore L' x N B i j‖ ≤ s:=by unfold Rot.shore; rw [of_apply]; split; exact ht.issue ..; rw [norm_zero]; exact hs
    refine ⟨bills_br (Rot.shear L' x N B) A ht.pos (?_),fun i hi j _=> stamp_norm (Rot.shore L' x N B) A (fun i _=> hz i) hs i hi j⟩; intro i; apply le_trans _ (ht.meter i); apply sum_le_sum; intro j _; unfold Rot.shear; rw [of_apply]; split; exact le_rfl; rw [norm_zero]; exact norm_nonneg _
omit ht
open Spice
structure Skiff (b₀:ℕ)(w w' :ℝ) : Prop where
    issues U V:∀ (i j: Modes f N), Spice.BeamRaw (halo b₀ {i.1.1}) U 1 V → V ≤ w→ ‖spore G b₀ U i j-shore L' x N b₀ i j‖ ≤ w'
    pulses U V:∀ (i:Keys f N)(j:Keys c N), Spice.BeamRaw (halo b₀ {locationP i}) U 1 V→ V ≤ w→ ‖(G.equip N b₀).shortP U i j-shear L' x N b₀ i j‖ ≤ w'
-- build eventually near runtime.N. propagate cost Skylight
variable (U:Grid f)
set_option quotPrecheck false
local notation "Vx"=>spore G B U
local notation "Tx"=> (G.equip N B).shortP U
local notation "Mf"=> breezeP (Spine I) ((G.equip N B).shortP U)
local notation "Vf"=> breezeX (Spine I) (stamping (spore G B U (F:=N)))
-- Auras
lemma rhoE (i: Keys f N) : let L:= limits (F:=N) (halo (B+1) {(Ry).parent (locationP i)})
                       ∀ j∉ L,(G.equip N B).shortP U i j=0∧shear L' x N B i j=0:=by
    intro K j hj; have hv: (Ry).embed (locationP j)∉halo B {locationP i}:=by
        intro h; have hf:= rowL Ry h; rw [Ratio.embed_parent] at hf; exact hj (mem_filter.mpr ⟨mem_univ _,halo_spec.mpr ⟨_,mem_singleton_self _,hf⟩⟩)
    exact ⟨by_contra (fun hi=>hv ((G.equip N B).sleeps i j U hi)), if_neg hv⟩
-- card rate
noncomputable def stockN (N B:ℕ):ℝ:= 2*((B+1+B+1+1:ℕ)^4)*Fintype.card Lat.Fiber*N
lemma earlier (b:ℕ)(N:ℕ)(i: Site c): (((limits (F:=N) (halo (b+1) ({i}:Support c))).card:ℝ)) ≤ stockN N b:=by
    rw [limits_card]; unfold stockN; push_cast
    have ht: (halo (b+1) ({i}:Support c)).card ≤ (b+1+b+1+1)^4:=by simpa [Nat.add_assoc] using (Corona.halo_size {i} (b+1)) -- order
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _); apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _); push_cast at *; gcongr; exact_mod_cast ht
variable (htK: Skiff (N:=N) L' x G B w w') (hw: 0 ≤ w')
variable (X: Finset (Dh f N I)) (hh:∀ i:Keys f N, Sum.inl i∈X→Spice.BeamRaw (halo B {locationP i}) U 1 w)
include htK hh hw
lemma minceP : Anomaly.bills (Mf-M) X (stockN N B*w') ∧ (∀ i∈X,∀ j∈X,‖Vf i j-Ω i j‖ ≤ w'):=by
    have hv (i j: Modes f N)(hi:Sum.inl (Sum.inl i)∈ X) : ‖spore G B U i j - Rot.shore L' x N B i j‖ ≤ w':=by
         have hh:= hh (.inl i) hi; exact htK.issues U w i j hh le_rfl
    have he:= stamps_diff (spore G B U) (Rot.shore L' x N B) X (fun i hi j=>hv i j hi) hw
    refine ⟨bills_cut (Tx) (Rot.shear L' x N B) X (mul_nonneg (show 0 ≤ stockN N B from by unfold stockN; positivity) hw) (?_),fun i hi j _=> he i hi j⟩
    intro i hi; let K:= limits (F:=N) (halo (B+1) {(Ry).parent (locationP i)})
    let f j := ‖(G.equip N B).shortP U i j-Rot.shear L' x N B i j‖
    have hz(j)(hj:j∉K): f j=0:=by obtain ⟨he,h⟩:=rhoE L' x G U i j hj; unfold f; rw [he,h,sub_zero,norm_zero]
    change ∑ j,f j≤ _; rw [← sum_subset (s₁:=K) (f:=f) (subset_univ K) (fun i _=> hz i)]
    calc _ ≤ ∑ _j∈K,w':=sum_le_sum (fun j hj=> htK.pulses U w i j (hh i hi) le_rfl)
         _ ≤ _:= by rw [Finset.sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (earlier ..) hw
omit htK hh hw in
private lemma billsIn {A B:Type}[Fintype A][Fintype B](M₁ M₂:Matrix A B ℂ) (Y Z: Matrix A A ℂ) (X:Finset A) (hu:Anomaly.bills (M₁-M₂) X t ∧ (∀ i∈X,∀ j∈X,‖Y i j-Z i j‖≤ w'))(hz: Anomaly.bills M₂ X s ∧ ∀ i∈X,∀ j∈X,‖Z i j‖≤ s): Anomaly.bills M₁ X (s+t)∧∀ i∈ X,∀ j∈ X,‖Y i j‖ ≤ s+w':=by
    constructor
    · intro i hi; have hp:=hu.1 i hi; apply le_trans _ (add_le_add (hz.1 i hi) hp); rw [← sum_add_distrib]; exact sum_le_sum fun j _ => by simpa only [sub_zero,Matrix.sub_apply,add_comm] using norm_sub_le_norm_sub_add_norm_sub (M₁ i j) (M₂ i j) 0
    intro i hi j hj; apply le_trans _ (add_le_add (hz.2 i hi j hj) (hu.2 i hi j hj)); simpa only [sub_zero,add_comm] using norm_sub_le_norm_sub_add_norm_sub (Y i j) (Z i j) 0
include ht
lemma lampsP : Anomaly.bills (Mf) X (s+stockN N B*w') ∧ ∀ i∈X,∀ j∈X,‖Vf i j‖ ≤ s+w':= billsIn _ _ _ _ X (minceP L' x G U htK hw X hh) (sailing L' x ht X)
-- budgetW
end
end YM.MassiveQCD.Rebus
#print axioms YM.MassiveQCD.Rebus.lampsP
