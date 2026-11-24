import YM.Clays.Rates
import YM.Oars.Reseats
set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 860000
namespace YM.MassiveQCD.Sample
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola
open Function Lattice Wilson Creek Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby Massive.PCAC
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
namespace Basal
variable {c:Side}{N:ℕ}{I D:Type}[Fintype I]{a C t b w x v θ m:ℝ}
variable (o:I→Site c)(p:I→Lat.Fields c N→L[ℂ]Lat.Fields c N)(H:∀ i,Veins (o i) (p i) C) (s:List I)(d:I→ℂ)
local notation "P"=> Patio (Keys c N⊕Spine I)
local notation "M"=> ample N I
local notation "T"=> traceI I
local notation "Λ"=> Keys c N
local notation "Yp"=> actE o p H d s
variable (F: Patron.Rail c (ample N I) D)
-- same addresses.X
local notation "f⁰"=> withdraw N o t
local notation "ft⁰"=> banknote N o t
noncomputable def flock (t:ℝ)(s: List I) : Patron.Rail c (ample N I) D:=⟨F.addr,fun i U=> banknote N o t (actE o p H d s (withdraw N o t (F.warp i U)))⟩
local notation "F⁺" j:arg=> flock o p H d F t j
variable {U:BudgetPoint}
variable (h: Wage.Tip N o (traceI I) F U t b x) (ht:0<t)
-- actual payload gate and cap for all.s.Geometry.At Frame. Wake for all even poles given.These types mainly abstracted.Spectrum.
include H ht
lemma warp_one (x:EvenA c M)(Y:Support c)(i:I)(h: Gated Y x)(hw:Well N o t (traceI I) x) : Gated Y (ft⁰ ((H i).incline (d i) i (f⁰ x))) :=by
      let z:=f⁰ x; let M' :=(H i).incline (d i) i; let V:= (H i).dies (d i) i; rw [Veins.inclined,map_add, show ft⁰ _=x from hw.spark]; unfold Gated; rw [map_add]; refine Subalgebra.add_mem _ h ?_; by_cases he:o i∈Y; swap; · have hf: V z=0:=(H i).diesOff (d i) i z (fun k=>Cupola.pennied N o t k x Y h) he; rw [hf,map_zero,map_zero]; exact Subalgebra.zero_mem _
      change light _ (ft⁰ (V z))∈_; have hz:ValidPieces Λ T univ z:=hw.applies; rw [hz.wholeV,map_sum,map_sum,map_sum]; refine Subalgebra.sum_mem _ fun j _=> ?_; let f:= Cupola.pick Λ T j z
      have hx(K:Finset (Spine I)):pluck Λ K f=if K=burst T j then pluck Λ (burst T j) z else 0:=by unfold f Cupola.pick; rw [many]; split; rw [show K=_ from by assumption]; rfl -- if both branches
      by_cases ht:j.image o⊆Y; swap
      · have hq : pluck Λ (burst T j) z=0:=Cupola.confined N o t (burst T j) x Y h (fun hu=> ht ((held_pins o Y j T).1 hu))
        have hf:f=0:=by apply pluckVisible; intro k; rw [hx,hq,map_zero,ite_self]
        change light _ (ft⁰ (V f))∈ _; rw [hf,map_zero,map_zero,map_zero]; exact Subalgebra.zero_mem _
      have hr : clad (limits Y) f.val:=fun K=>by
          change pluck Λ K f∈_; rw [hx]; split; exact Cupola.pennied N o t _ x Y h; exact Subalgebra.zero_mem _
      let W:= {i}∪ j; have hm: Polite T W (V f):=(H i).diesPiece _ _ (choseTuft ..); have hW:W.image o ⊆ Y:=by unfold W; rw [image_union,image_singleton]; exact union_subset (singleton_subset_iff.mpr he) ht
      rw [bank_spent, show light _ (V f)=_ from hm.exact.symm]; exact Ribbon.entitled N o t Y (burst T W) _ (((H i).diesClad (d i) i f Y hr) _) fun j hj=>hW (mem_image_of_mem _ (located (traceI I) W _ hj)) -- order.loc arg
include h
lemma earnsK (Y:List I)(i:D)(V:Grid c): Well N o t T ((F⁺ Y).warp i V)∧ Gated (F.addr i).place ((F⁺ Y).warp i V) :=by
     let z:=f⁰ (F.warp i V); have hZ:ValidPieces Λ T univ z:=(h.fits ..).applies
     constructor; · have hp:=validp o p H d Y z hZ; let X:= actE o p H d Y z; have hQ:f⁰ ((F⁺ Y).warp i V)= X:=Cupola.home N o t ht _; exact ⟨congr_arg _ hQ,hQ.symm ▸ hp⟩
     induction Y with
     | nil=>change Gated _ (ft⁰ (f⁰ _)); rw [(show ft⁰ _= _ from (h.fits i V).spark)]; exact h.tilt.uses.role ..
     | cons j s ih=>
         have hp:=validp o p H d s z hZ; let X:=actE o p H d s z; have hQ:f⁰ ((F⁺ s).warp i V)= X:=Cupola.home N o t ht _; change Gated _ (ft⁰ ((H j).incline _ j X)); rw [← hQ]; exact warp_one o p H d ht _ _ j ih ⟨congr_arg _ hQ,hQ.symm ▸ hp⟩ -- arg t position
lemma grooms (g:Lat.Frame c)(i:D)(V:Grid c):sways (Lat.rotates M g) ((F⁺ s).warp i (Lattice.gauge g V))=(F⁺ s).warp i V:=by
    let f:= f⁰ (F.warp i (Lattice.gauge g V)); let z:= f⁰ (F.warp i V); have hl:ft⁰ f=(F.warp i (Lattice.gauge g V)) := (h.fits ..).spark; have hz: ValidPieces Λ T univ f:=(h.fits ..).applies; let g':= parcelColor N g I; have ht: z=g' f:=Eq.trans (congr_arg (withdraw N o t) (show F.warp i V= ft⁰ (g' f) by rw [show ft⁰ (g' f)=_ from all_color N o t T g f hz,hl]; exact (Subtype.ext (h.tilt.pigment i V g)).symm)) (Cupola.home N o t ht _)
    change _= ft⁰ (Yp z); rw [ht]; exact (all_color N o t T g _ (validp o p H d s f hz)).symm.trans (congr_arg _ (toneE o p H d s g f).symm)
variable (ha:0≤a)(hC:0≤C)(hs: s.Nodup) (Fi:ℕ)(hr:Fires o Fi)(hg:∀ i:I,‖d i‖≤a)(hx:0 ≤ x)
include hs hC ha hr hg hx
lemma receivesK (hA: C*a*((U.B+U.B+1)^4 :ℕ)*Fi ≤ b-w): Wage.Tip N o T (F⁺ s) U t w x:=by
     let f:= F⁺ s; let Z:= (ft⁰).comp ((Yp).comp f⁰); have hp:=h.tilt.uses; refine ⟨⟨⟨fun i A B hx hg=> congr_arg Z (hp.uses i A B hx hg),fun i=> Z.toLinearMap.toContinuousLinearMap.measurable.comp (hp.reads i),fun i j=>(earnsK o p H d F h ht s i j).2,fun i U h=>hp.buys i U (fun e=>h ((congr_arg Z e).trans (map_zero _)))⟩,fun i V g=>congr_arg Subtype.val (grooms o p H s d F h ht g i V),?_⟩,fun i j=>(earnsK o p H d F h ht s i j).1⟩ -- order check
     obtain ⟨g,hg',hgV⟩:=h.tilt.sold.cost; let R i:= Real.exp ((b-w)*coverNumber U.B (F.addr i).place); have hn (i:D):0≤ g i:=(norm_nonneg _).trans (hgV i 1); refine ⟨fun i=> R i*g i,?_,fun i V=> ?_⟩
     · intro xx; convert hg' xx using 1; funext i; let S:= (F.addr i).place; change (if xx∈S then (_:ℝ)*(R i*g i)*Real.exp (w*coverNumber U.B S) else 0)=(if xx∈S then _ else 0); split; next ht=> simp only [taxed]; let L:ℝ:= coverNumber U.B S; change x^(oriD F i).card * (Real.exp ((b-w)*L)*g i)*Real.exp (w*L)= x^(oriD F i).card*g i*Real.exp (b*L); rw [show b * L=(b-w)*L+w*L from by ring,Real.exp_add]; ring -- `_` meta
       rfl
     let z:=F.warp i V; let v:=f⁰ z; have he: ‖token c M t z‖=Stitch.Tablet.credits t v:=Eq.trans (congr_arg (fun x=> ‖token _ _ t x‖) (h.fits i V).spark.symm) (from_full o ht v); let Y:=(F.addr i).place; exact (from_full o ht (actE o p H d s v)).trans_le ((credibility o p H d ht hg ha hC s hs (hy:=fun j=> Cupola.pennied N o t j z Y (hp.role ..)) U.B Fi hr hA).trans (mul_le_mul_of_nonneg_left (he.symm.trans_le (hgV i V)) (Real.exp_pos _).le)) -- lt tactics arg binder
omit hs hr hC ha hg hx
lemma rests: faultK N o t (F⁺ s)=faultK N o t F:=by
    let hC'(u v:Patron.Rail c N D)(hp:u.addr=v.addr)(hh:u.warp=v.warp):u=v:=by cases u; cases v; congr
    refine hC' _ _ rfl ?_; funext i V; let Z:= f⁰ (F.warp i V); have hf:f⁰ ((F⁺ s).warp i V)=actE o p H d s Z:=Cupola.home N o t ht _; change vacR (Spine I) _ _= vacR (Spine I) _ _; rw [hf]; exact Subtype.ext ((revive ..).trans ((waived o p H d s Z (show ValidPieces Λ T _ Z from (h.fits i V).applies)).trans (revive ..).symm))
lemma trunkR (hb:1≤ t)(hu:1≤ x)(hw:0 ≤b)(i:Grid c): heartK (F⁺ s) U.threshold i= (ft⁰) (Yp (f⁰ (heartK F U.threshold i))):=by
     let z:= (ft⁰).comp ((Yp).comp f⁰); refine ((z.toLinearMap.toContinuousLinearMap.hasSum (profits F i hb hu h.tilt.sold hw U.threshold).hasSum).congr_fun ?_).tsum_eq; intro u
     unfold Ruby.tK; change _=z _; split; next h0=> rw [if_pos (show separated (blocked (Ruby.home F)) u ∧ RG.flags U.threshold i=u.biUnion (oriD F) from h0),map_prod]; rfl
     next h0=>rw [if_neg (show ¬(separated (blocked (Ruby.home F)) u ∧ RG.flags U.threshold i=u.biUnion (oriD F)) from h0),map_zero]
end Basal
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.Basal.receivesK
#print axioms YM.MassiveQCD.Sample.Basal.trunkR
