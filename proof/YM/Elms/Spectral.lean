import YM.Elms.Luminous
/-! # Writes lists with definite tariffs and records the frozen pivot.
Books independent of placements after passing to sufficiently wide periods.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass Poised Poised.Display Poised.Sieve Poised.Plans MeasureTheory Filter Finset
open scoped Matrix Matrix.Norms.Frobenius InnerProductSpace Topology BigOperators TensorProduct Pointwise Classical ContDiff Stamp Kronecker
open Papyrus.Purl Papyrus LoomC
variable {d:ℕ}
namespace SparK
open Push.Mark YM.Source YM.Source.Drops RG RP
namespace Arbor
open Lining Lining.Temper Poised.Carte.Hem Permit
variable {n:Side}(U:Grid n)(P : Regulator n 6)
variable (o:Cover)(w v:Walk)(e:Point)(a:Axis)
namespace PrismD
variable (H: SourceRead.TaperHol)(K:Hol su)
open QCD.Kites Beacon
lemma Survey.unit (d:ℕ) : Survey H 1 0 0 (setas d 1):=by
   let x:=(1: Pol d); refine ⟨birth0, setas d x, ⟨0,fun n o _ J=> linearTime x _ _ ?_⟩,?_⟩
   · change SourceRead.Agrees (Beacon.moment H o J (fun _ : Grid n=>1)) (SourceRead.desired (1:Pol d) J)
     rw [← funext (observe J (1:Pol d)),show (1:Pol d)= (1:GPol)⊗ₜ[ℂ](1:SpinPol d) from rfl]
     have he(i): observation d J i ((1:GPol) ⊗ₜ[ℂ] (1:SpinPol d))=1:=by unfold observation; simp only [LinearMap.comp_apply,ready_t, AlgHom.toLinearMap_apply,map_one,one_smul]
     simp_rw [he,funext (f:=Beacon.moment H o J (fun _ : Grid n=>1)) (g:=fun _=> (1:SpinPol d)) (fun i=> map_one (adapter ..))]; exact ⟨contDiffAt_const,contDiffAt_const,fun _ _=>rfl⟩
   have hz(t:ℝ): prism t 1 d (setas d x)= setas d 1:=by
      let p:PowerPair d:= (0,∅); have hc: x=gen p:=by unfold x gen; simp only [p,mono_empty]; rfl
      rw [hc,spent]; simp only [life,p,Finsupp.support_zero,sum_empty,pow_zero,one_smul, ← hc]; rfl
   simp_rw [pow_zero,Complex.ofReal_one,inv_one,hz,one_smul]; exact tendsto_const_nhds
noncomputable abbrev issue (p:Bough):Drape:= Sum.elim (fun v:Slot× su.ColorIndex=>tendency v.1 v.2) (fun v:Barge=>burnish v.wal v.q (v.i,v.u)) p
abbrev luminos (p:Bough): ℕ:= Sum.elim (fun _=>1) (fun _=>0) p
abbrev tallyS (p:Bough): ℕ:= Sum.elim (fun _=>0) (fun _=>1) p

lemma issued (v:Bough)(h: Peg K (d/2)): Survey H (issue v) (luminos v) (tallyS v) (setas d (climber K d v)):=by cases v with |inl i=> exact growsSlot H K i.1 i.2 h|inr j=>exact growsBeams j.wal H K j.q (j.i,j.u) d
noncomputable def leaflet (l:List Bough):Drape:= (l.map issue).prod
abbrev gaugeI(l:List Bough):ℕ:=(l.map luminos).sum
abbrev fermI(l:List Bough):ℕ:=(l.map tallyS).sum
lemma leaves (l: List Bough)(h:Peg K (d/2)): Survey H (leaflet l) (gaugeI l) (fermI l) (setas d (canopy K d l)):=by
    induction l with
    | nil=>exact Survey.unit H d
    | cons a l ih=> rw [canopy_more, ←fold_taps]; simp only [leaflet,List.map_cons,List.prod_cons,gaugeI,fermI,List.sum_cons]; exact (issued H K a h).mul ih

noncomputable abbrev flashF (e:Point)(i:su.ColorIndex):Drape:=fun n o=> purely n o e (ico i)
noncomputable abbrev flashK (e:Point)(A:su.Color):Drape:=fun n o=>quest n o e A
lemma flashCoins(i:su.ColorIndex) : flashF e i = ∑ p:PlaqAxes, Push.Mark.hereTerm (fun s=>tendency s i) e.w e.e.2 p:=by
   funext n o; refine ContinuousMap.ext (fun U=>?_); simp only [Finset.sum_apply,ContinuousMap.sum_apply]; let V:=expandAt (wrap n o) U; let E:= EuclideanSpace.basisFun su.ColorIndex ℝ; change (inner ℝ (E i) (force V e.w e.e):ℂ) • (1: Lat.Fields n 6)=_; rw [show (inner ℝ _ _ :ℝ)=_ from (E.repr_apply_apply ..).symm]; change flashed (G:=su) e i V • _= _; rw [Push.Mark.fsum, Finset.sum_apply, sum_smul]; refine Finset.sum_congr rfl (fun p _=>?_); unfold hereTerm; split
   next _=> rw [Pi.sub_apply,sub_smul]; rfl
   next _=> split
            next _=> simp only [Pi.sub_apply,sub_smul,Pi.neg_apply, neg_smul]; rfl
            next _=> rw [Pi.zero_apply,zero_smul]; rfl
lemma flashing (i:su.ColorIndex) (h:Peg K (d/2)): Survey H (flashF e i) 1 0 (setas d (glitter K e i d)):=by
    rw [flashCoins,glitter,Push.Mark.psum]; obtain ⟨F,hF⟩:=coarseL (d:=d); rw [← hF]; simp_rw [map_sum]; refine Survey.total _ _ _ _ _ _ _ (fun i' _=>?_); unfold Push.Mark.hereTerm; split
    next _=> rw [map_sub,map_sub,hF]; exact (growsSlot H K _ i h).sub (growsSlot H K _ i h) -- hp
    next _=> split
             next _=> rw [map_neg,map_sub,map_neg,map_sub,hF]; exact ((growsSlot H K _ i h).sub (growsSlot H K _ i h)).neg
             next _=> rw [map_zero,map_zero]; exact Survey.dry ..
noncomputable def fuseD(v w:Walk)(p:ΔM): Drape:=∑ i:Dike,∑ j:Dike,p i j • (burnish w false j * burnish v true i)
noncomputable def exposeD(n:Side)(o:Cover)(U:Grid n): Drape→ₗ[ℂ]Lat.Fields n 6:=(ContinuousMap.evalCLM ℂ U).toLinearMap.comp ((LinearMap.proj (R:=ℂ) (φ:=fun _ :Cover=> Insertion n 6) o).comp (LinearMap.proj (R:=ℂ) (φ:=fun n:Side=> Cover→Insertion n 6) n))
lemma pointwiseE (x:Drape) : x n o U= exposeD n o U x:=rfl
lemma put_bus (u x:Walk)(M:ΔM): exposeD n o U (fuseD u x M) = bill o u x M U:=by
   unfold fuseD bill; simp only [map_sum]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl (fun j _=>?_)
   rw [map_smul,←pointwiseE]; simp only [Pi.mul_apply,ContinuousMap.mul_apply]; congr 2
lemma quakeE (A:su.Color) : exposeD n o U (flashK e A) = dualSp o e.w e.e.2 A U:=by rw [← pointwiseE]; change quest n o e A U=_; apply Eq.refl
lemma postY (A:su.Color): flashK e A= -fuseD e.w (e.w++[posDir e.e.2]) (RP.down 6 e.e.2 (cob A))-fuseD (e.w++[posDir e.e.2]) e.w (RP.up 6 e.e.2 (cob A)):=by
   apply equal; intro n o U; rw [map_sub,map_neg,put_bus,put_bus,quakeE]; rfl
 where
   equal {X Y:Drape}(h:∀ n o U, exposeD n o U X=exposeD n o U Y): X=Y:=funext fun i=> funext fun o=> ContinuousMap.ext (fun U=> (pointwiseE ..).trans ((h i o U).trans (pointwiseE ..).symm))
lemma promised (A:su.Color): Draft (flashK e A) 0 2:=by
   rw [postY]; have h(x y:Drape)(he: Draft x 0 2)(hv: Draft y 0 2):Draft (-x-y) 0 2:=by rw [sub_eq_add_neg]; simpa using Draft.joins (he.scale (-1)) (hv.scale (-1))
   refine h _ _ (Draft.sums _ _ (fun i _=> Draft.sums _ _ (fun j _=> ((brew _ _ _).mulX (brew _ _ _)).scale _))) (Draft.sums _ _ (fun i _=> Draft.sums _ _ (fun j _=> ((brew _ _ _).mulX (brew _ _ _)).scale _)))
variable (i:Dike)(q:Bool)
def endZ (a:Axis):Drape:= burnish w q i - ((∑ j:Dike,revM q (mL (Lat.lo a)) i j • burnish (adWalk q w a) q j)+∑ j:Dike, revM q (mL (hi a)) i j • burnish (adWalk (!q) w a) q j)
lemma endY : endZ w i q a n o U= unwind n q o w U i a:=by unfold endZ unwind; simp only [Pi.add_apply,Pi.sub_apply,ContinuousMap.add_apply,ContinuousMap.sub_apply, Finset.sum_apply,ContinuousMap.sum_apply]; rfl
noncomputable def tipC (w:Walk)(q:Bool)(i:Dike)(d:ℕ):Covec d:= twig q i.1 i.2 (vector (stop 0 w))
lemma rip (w:Walk)(j:Dike)(q:Bool)(s:Bool) : tipC (adWalk s w a) q j d= twig q j.1 j.2 (vector (stop 0 w+ Pulses.bySign s a)):=by cases s <;> simp [tipC,adWalk,Pulses.bySign,stop_append,Lattice.stop]
noncomputable def oreZ (d:ℕ):Covec d:= tipC w q i d - ((∑ j:Dike,revM q (mL (Lat.lo a)) i j • tipC (adWalk q w a) q j d) + ∑ j:Dike, revM q (mL (hi a)) i j • tipC (adWalk (!q) w a) q j d)
lemma mL_loc (x:Spike)(j:Dike): revM q (mL x) i j=if i.2=j.2 ∧ i.1.2=j.1.2 then Pulses.flipD q x i.1.1 j.1.1 else 0:=by
   cases q <;> by_cases H:i.2=j.2 <;> by_cases h:i.1.2=j.1.2 <;> simp [revM, mL, Pulses.flipD, Matrix.blockDiagonal_apply,copies, *,Ne.symm, Lat.wave,Matrix.one_apply] -- ,*
lemma driveD {X:Type*}[AddCommGroup X][Module ℂ X](x:Spike)(f:Dike→ X): ∑ j:Dike,revM q (mL x) i j • f j= ∑ j:Pinor,Pulses.flipD q x i.1.1 j • f ((j,i.1.2),i.2):=by simp_rw [mL_loc,ite_smul,zero_smul,Fintype.sum_prod_type]; simp [ite_and] -- ite nested
lemma ore_eco : ∑ a:Axis, oreZ w a i q d = Pulses.bent q i.1.1 i.1.2 i.2 (stop (0:Cover) w):=by
    unfold Pulses.bent; refine Finset.sum_congr rfl (fun a _=>?_); let x(j:Pinor):Dike:= ((j,i.1.2), i.2); let f(j:Dike):= tipC w q j d; unfold oreZ; rw [driveD,driveD]; simp_rw [rip];
    have he: stop (0:Cover) w+ Pulses.bySign (!q) a= stop 0 w - Pulses.bySign q a:=by cases q <;> simp [Pulses.bySign,sub_eq_add_neg]
    rw [he]; let V:=Pulses.flipD q (Lat.lo a); let W:=Pulses.flipD q (hi a); have hz: ∑ j, (V i.1.1 j • f (x j)+ W i.1.1 j • f (x j))=f i:=by
        simp_rw [← add_smul, show ∀ j,V i.1.1 j+ W i.1.1 j= _ from fun j=> (add_comm _ _).trans (Pulses.signdB q a _ j)]; simp only [Matrix.one_apply,ite_smul,one_smul,zero_smul,sum_ite_eq,mem_univ,if_true]; rfl
    simp_rw [Finset.sum_add_distrib] at hz; simp only [smul_sub,sum_add_distrib,sum_sub_distrib]; rw [show tipC w q i d = _ from hz.symm]; unfold V W x f tipC; abel
noncomputable def brake : Drape := ∑ a:Axis,endZ w i q a
lemma endPulse (M:Regulator n 6) : solar M q o w i= ((M.m i.2:ℂ)) • cane n q o w i + brake w i q n o:=by simp_rw [brake,Finset.sum_apply]; unfold solar; apply congr_arg₂ _ rfl; apply Finset.sum_congr rfl; intro a _; apply ContinuousMap.ext; intro U; rw [endY]; simp only [ContinuousMap.sub_apply,ContinuousMap.add_apply,ContinuousMap.sum_apply]; rfl
include K
lemma motor (d:ℕ) : Survey H (brake w i q) 0 1 (setas d (flora (Grass.line (Pulses.bent q i.1.1 i.1.2 i.2 (stop (0:Cover) w))))) :=by
   obtain ⟨F,hF⟩:=floraL (d:=d); rw [← ore_eco w i q,← hF]; simp_rw [map_sum]; refine Survey.total H _ _ _ _ _ _ (fun a _=>?_); unfold oreZ endZ; simp only [map_sub,map_add,map_smul,map_sum]; rw [hF]
   apply Survey.sub (growsBeams w H K _ _ _); apply Survey.add (Survey.total _ _ _ _ _ _ _ (fun j _=>(growsBeams _ _ K _ _ _).scale _)) (Survey.total _ _ _ _ _ _ _ (fun j _=>(growsBeams _ _ K _ _ _).scale _)) -- unification
end PrismD
end Arbor
end SparK
end YM.Massive.Elm
#print axioms YM.Massive.Elm.SparK.Arbor.PrismD.flashing
#print axioms YM.Massive.Elm.SparK.Arbor.PrismD.motor
