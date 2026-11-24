import YM.Lobo.Camel
set_option maxHeartbeats 780000
set_option autoImplicit false
noncomputable section
namespace YM.Lobo
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV TensorProduct Heron Tawny Tawny.Cast Tawny.Cast.Perla Tawny.Cast.Carnal Tawny.Cast.Drill Tawny.Cast.Zinc
open Perla.Fore Dream Dream.Clove
open Massive.Oriole UV.Free
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius Kronecker
open StressFlux (pair curl0)
open Finset
variable (G: EuPin)(f:Flavor 6)(i j k:Axis)
lemma pebV (htY:i≠j): projection (med f i j (gamma k)) ≠ 0:=by
     intro he; obtain ⟨p,hp,ht⟩:= freedom; obtain ⟨y,hy⟩:=findR k p ht; let c:= Gpick
     obtain ⟨Q,hQ⟩:= BrickM.rootY (StressFlux.leg0 i j c); let X:Maxwell.TaylorTower su:=Pi.single 0 Q; have hP : lexY X 0= StressFlux.leg0 i j c:=(congr_arg Maxwell.gaugeJet (show X 0=Q from Pi.single_eq_same ..)).trans hQ
     have h:= (auditor f axis jPick iPick p y hp X _ ((Qeq _).1 he)).1
     change vitality f axis jPick iPick p y hp X 10 (youthL f i j (gamma k))=0 at h; rw [mixedY, if_pos rfl, hP,StressFlux.curl0_leg] at h
     apply mul_ne_zero findSlot.choose_spec.choose_spec hy; have ht:StressFlux.curl0 i j (StressFlux.leg0 i j c)=c:=by rw [StressFlux.curl0_leg]; simp [basis_eq,htY,Ne.symm htY]
     rw [← StressFlux.curl0_leg, ht] at h; exact h -- h shadow
lemma ripeN : projection (med f 0 1 (gamma 1) + med f 0 2 (gamma 2)) ≠0:=by
     intro he; obtain ⟨p,hp,ht⟩:= freedom; obtain ⟨y,hy⟩:=findR 1 p ht; let c:= Gpick
     obtain ⟨Q,hQ⟩:=BrickM.rootY (StressFlux.leg0 0 1 c); let X:Maxwell.TaylorTower su:=Pi.single 0 Q; have hP : lexY X 0= StressFlux.leg0 0 1 c:=(congr_arg Maxwell.gaugeJet (show X 0= Q from Pi.single_eq_same ..)).trans hQ
     have h:= (auditor f axis jPick iPick p y hp X _ ((Qeq _).1 he)).1; rw [Submodule.coe_add,map_add] at h; change vitality f axis _ _ p y hp X 10 (youthL f 0 1 (gamma 1)) + vitality f axis _ _ p y hp X 10 (youthL f 0 2 (gamma 2))=0 at h; simp only [mixedY,hP, StressFlux.curl0_leg] at h
     have hv:=mul_ne_zero findSlot.choose_spec.choose_spec hy; simp +decide [basis_eq, show BendR.ore (0:su.Color)=0 from map_zero _] at h -- avoid simpl
     exact hv (mul_eq_zero.mpr h)
lemma gritI (x:Tri): lieu (edgeK x) ≠ lieu (backK x):= fun h=>threeL x (Fin.castSucc_inj.mp h.symm)
lemma raysM (x:Tri) : Free.projection (pulseT f false x k)≠0:= pebV f _ _ k (gritI _)
local notation "Σ" => pulseT f false
lemma act_star : let z:= starV f; projection (z.val 0)= projection ((pulseT f false 2 1)-(pulseT f false 1 2)) +projection (pulseT f true 0 timeAxis) :=by
   intro z; rw [show z.val 0= _ from TableT.star_val ..,Fin.sum_univ_four]; -- careful wrong viz. starV = ∑j med 0 j gamma_j. M2 = 0,1; M1=2,0.
   have hv (a b:Axis):med f a a (gamma b)=0:=by apply smul_right_injective (Label 10) (two_ne_zero (α:=ℂ)); change (2:ℂ) • _=(2:ℂ) • (0:Label 10); rw [smul_zero, two_smul]; nth_rw 1[bear f a a]; exact neg_add_cancel (med f a a (gamma b))
   rw[hv,zero_add,bear f 0 2,map_add]; exact congr_arg₂ (·+·) (congr_arg projection (show pulseT f false 2 1+ -(pulseT f false 1 2)= _ from (sub_eq_add_neg (pulseT f false 2 1) (pulseT f false 1 2)).symm)) rfl
lemma rock : projection ((pulseT f false 2 1)-(pulseT f false 1 2)) ≠0:=by
      change projection (med f 0 1 (gamma 1) - med f 2 0 (gamma 2)) ≠0; rw[bear f 2 0,show med f 0 1 (gamma 1)- - med f 0 2 (gamma 2) = _ from (sub_neg_eq_add (med f 0 1 (gamma 1)) (med f 0 2 (gamma 2)))]; exact ripeN f
lemma rotor (w:Bool)(x:Tri): pulseT f w x k∈ Qa 10:= (coalP ..).1 -- check
-- lemma crunchT(i j:Tri): (disk i 0 i j)=if i=j then 1 else 0:=by unfold disk Thr; simp [Matrix.one_apply,lieu]
end YM.Lobo
#print axioms YM.Lobo.rock
#print axioms YM.Lobo.raysM
#print axioms YM.Lobo.act_star
#print axioms YM.Lobo.rotor
