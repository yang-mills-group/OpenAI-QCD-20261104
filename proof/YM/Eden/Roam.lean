import YM.Eden.Wizard
/-! # shift covariance of rolls and vertex at one.S raw rows. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Eden
open Function Lattice Laurent Bloch Metric RG Filter Arise Arise.Range
open Finset YM.Bank Precision Matrix
open scoped Topology BigOperators Matrix Matrix.Norms.Frobenius Classical Kronecker
open QCD QCD.Lat QCD.Free QCD.Flume QCD.Bank Next.Free
open QCD.Creek QCD.Anomaly QCD.Cove QCD.Kit QCD.Bloom QCD.Pine QCD.Grass
open Massive Massive.UV Patria Patria.Exposure Revolve TorusPCAC.Geometry TorusPCAC.Geometry.AxisB
open Lining Ferry Cylinder Elm Elm.SparK Elm.SparK.Arbor
variable {c f:Side}{N k m:ℕ}{I J:Type}[Fintype I][Fintype J]
variable (W:Walk)(p:Multi k)(x y: Cover) (U: Grid c)
local notation "PU"=> pull 1 (wrap c y) U
lemma motion_fade (i:Site c): fadeF x (PU) W i * (heat y i • 1)= fadeF (x+y) U W (i+wrap c y):=by
     let z:=wrap c y; have hp :landsE c (x+y) W=landsE c x W+z:=by unfold landsE capEdge; rw [← add_assoc,map_add]; -- reduce
     unfold fadeF; rw [hp]; split; next hi=>
         rw [hi,if_pos rfl,haloW, show expandAt (wrap c x) (PU)=expandAt (wrap c (x+y)) U from (by rw [pull_one]; funext i; simp only [expandAt,Lattice.translate,map_add,add_assoc]), Matrix.mul_smul, mul_one,smul_smul,show capEdge (x+y) W=capEdge x W+y from (add_assoc ..).symm, show heat y (landsE c x W)*ap c _ =_ from ((heated y (capEdge x W)).symm)] -- at `Xᵀ`; parse
         rfl
     next hi=> rw [if_neg (fun h=> hi (add_right_cancel h)), Matrix.zero_mul]
lemma travels (i:Site c): bladeU x PU p i* (heat y i • 1) = bladeU (x+y) U p (i+wrap c y):=by unfold bladeU hears; simp only [Finsupp.linearCombination_apply,Finsupp.sum,Matrix.sum_mul,Matrix.smul_mul]; apply sum_congr rfl; intro w _; rw[motion_fade]
lemma BannerP: BannerV c y=spar (fun i:Site c=> i+wrap c y) (fun i=> heat y i • 1):=by ext i j; by_cases he:i.2=j.2 <;> by_cases hx:i.1.1+wrap c y=j.1.1 <;> simp [BannerV,Lining.spar_intro,Matrix.blockDiagonal_apply,hues, copies, rides,he,hx,shiftE,Signed.actEquiv,Signed.act_one,wave_one] -- inspect
lemma roam : mood k x PU*slab (BannerV c y)=mood k (x+y) U:=by
     have ht: rollsU k x PU*BannerV c y=rollsU k (x+y) U:=by
         rw[BannerP]; let V:= Equiv.addRight (wrap c y); exact (Lining.spar_after V (fun i=> heat y i • 1) (bladeU x PU (k:=k))).trans (congr_arg nacre (funext fun i=>funext fun j=>by obtain ⟨j,rfl⟩:=V.surjective j; rw[V.symm_apply_apply]; exact travels ..))
     unfold mood slab; rw[fromBlocks_multiply]; simp only [Matrix.zero_mul,Matrix.mul_zero,add_zero,zero_add, ht,← mstar_mul]
lemma occ_p (v:Cover):ap c v=occ (0:Site c) v:=by simpa only [map_zero, ap_origin, one_mul,zero_add] using (Poised.Steed.rollAP c 0 v).symm
lemma foga (x:Cover)(w:Walk): travel (K:=su.El) 1 x w=1:=by induction w generalizing x with|nil=>rfl|cons i w h=> rw [Lattice.travel,h,mul_one]; unfold Step.read; split <;> simp
lemma dawnV (w:Walk)(i:Site c) : fadeF x (1:Grid c) w i= if i=wrap c (x+stop 0 w) then occ (0:Site c) (x+stop 0 w) • 1 else 0:=by
     unfold fadeF landsE capEdge; rw [add_comm _ x,occ_p]; split; next=>
        rw [haloW, show expandAt (wrap c x) (1:Grid c)=1 from rfl, foga, show colour 1=1 from su.mat_one, Lat.touch_one]
     next=> rfl
lemma lumens (i:Site c) : bladeU x (1:Grid c) p i = sound (fun j=> if i=wrap c (x+j) then occ (0:Site c) (x+j) • 1 else 0) (came (rider p)):=by rw[Arise.hearth]; unfold bladeU; exact congr_arg (fun f:Walk→Bundle=> hears f (rider p)) (funext fun w=>dawnV ..)
local notation "Z"=> mood k x (1:Grid c)
lemma pingR (a b: Fiber)(i:Site c): bladeU x (1:Grid c) p i a b= YM.Bloom.plume c x a (came (rider p)) () (i,b):=by
    rw [lumens,YM.Bloom.reefs]; unfold sound; simp only [Finsupp.linearCombination_apply,Finsupp.sum, Matrix.sum_apply]; apply sum_congr rfl; intro j _; rw [Matrix.smul_apply]; apply congr_arg; by_cases he:i=wrap c (x+j) <;> by_cases h:a=b <;> simp [he,h,Ne.symm,Matrix.one_apply, -map_add]
lemma pinned_zero (v:Sings k)(w:Keys c 6) : Z v w= tokenS c v x () w:=by
     unfold mood slab tokenS Buzz.paint; cases v <;> cases w <;> first| rfl| simp only [Bloom.chief,Sum.elim_inl,Sum.elim_inr, ↓reduceIte,Bloom.coreW,Bool.false_eq_true]
     next v w=> unfold rollsU Buzz.scrim Buzz.flaw; rw [fromBlocks_apply₁₁,imprints,pingR]; rfl
     next v w=>unfold rollsU Buzz.scrim Buzz.flaw; rw [fromBlocks_apply₂₂,mstar,imprints]; change star (if v.2=w.2 then (bladeU x (1:Grid c) v.1.1 w.1.1) _ _ else 0)= (if v.2=w.2 then _ else 0); rw [pingR]; split_ifs; exact (YM.Bloom.furls ..); exact star_zero _
end YM.QCD.Eden
#print axioms YM.QCD.Eden.roam
#print axioms YM.QCD.Eden.pinned_zero
