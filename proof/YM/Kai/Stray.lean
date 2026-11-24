import YM.Kai.Eights
/-! families vector covariance at arbitrary launch. exact and translatable. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.PCAC.Oren
open Function Filter MeasureTheory Set QCD QCD.Lat QCD.Grass Lattice Wilson UV RG QCD.Grass.Ward
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator Classical TensorProduct Kronecker
open Poised Poised.Beacon Poised.Plans Finset Module Poised.Stative Massive.Patria Patria.Exposure Depth Intag
open Entr Entr.Meridian Stew Cylinder
open QCD.Tide Revolve Onsite Tawny Tawny.Cast
variable {S:Scheme}{R c:Side}{d n i l j:ℕ}(A:Run S n R 6)(hA:A.Actual)(q:Averaging)
-- relay versions
local notation "Mμ" u:arg=> S.side R u
local notation "V0"=> Insertion (S.side R i) 6
variable (F G:Cover→Insertion (S.side R i) 6)(W:Insertion (S.side R i) 6)(T:Signed)
local notation "ν"=> fun x=> report A x q l 0 -- hygiene
private lemma the_wire (W W': V0)(Φ:∀ c:Side,Density c 6→Density c 6)(hstep:∀ (m:ℕ)(x:Insertion (S.side R (m+1)) 6),Φ (S.side R m) (A.block m x)= A.block m (Φ (S.side R (m+1)) x))(he:Φ (Mμ i) W=⇑W')(h:l ≤ i): Φ (Mμ l) (relay A l W)= ⇑(relay A l W'):=by
    induction h using Nat.decreasingInduction with
    | self=> unfold relay; rw[S.entrance] -- inspect
             exact he
    | of_succ i h ih=> rw [stepped A W h,stepped A W' h,hstep, ih]
private lemma plume (t:Grid (Mμ i)→ Grid (Mμ i))(H:Lat.Fields (Mμ i) 6 →ₐ[ℂ] Lat.Fields (Mμ i) 6)(h:∀ x p,H (F x (t p))=G (T.act x) p)(hi:l ≤ i)(U:Grid (Mμ i)) : H (visitor S i l q 0 F (t U))=visitor S i l (Averaging.permute T q) 0 G U:=by
     let L: V0→ₗ[ℝ] Lat.Fields (Mμ i) 6:=(H.toLinearMap.comp (ContinuousMap.evalCLM ℂ (t U)).toLinearMap).restrictScalars ℝ; unfold visitor; rw[smul_zero]; exact permeate q T L F G U (fun x=>h x U) (odd_to hi)
lemma trail1(p:EuPin)(hp:p.Lifts T)(h:∀ b:Cover,Action.pin p T ⇑(F b)= ⇑(G (T.act b))) (hv:l ≤ i): Action.pin p T (report A F q l 0)=⇑(report A G (Averaging.permute T q) l 0):=by
    apply the_wire A _ _ (fun _=>Action.pin p T) (fun x y=> by unfold Run.block; rw[step_brute,step_brute]; exact Exposure.pin_travel (stitch S R x) _ T p hp (S.admissible _) _ _ (ContinuousMap.continuous _)) _ hv
    exact funext fun x=> plume q F G T (pull T 0) (Lining.Temper.shipP _ T p) (fun x y=> congr_fun (h x) y) hv x
lemma trailC (h:∀ b:Cover, Action.charge ⇑(F b)= ⇑(F b)) (hv:l ≤ i): Action.charge (report A F q l 0)= ⇑(report A F q l 0):=by
     apply the_wire A _ _ (fun _=>Action.charge) (fun x y=>by unfold Run.block; rw[step_brute,step_brute]; exact Exposure.charge_shift (stitch S R x) _ (S.admissible _) _ _ (ContinuousMap.continuous _)) _ hv; funext x
     have ht:=plume q F F 1 (fun y=> conjugate∘y) (Lining.Temper.eveN _) (fun p i=>by rw [Signed.act_one]; exact congr_fun (h p) i) hv x; rw [permit_one] at ht; exact ht
lemma trailF (u:FlavorTorus)(h:∀ b:Cover, Action.flavor u ⇑(F b)= ⇑(F b))(hv:l ≤ i): Action.flavor u (report A F q l 0)= ⇑(report A F q l 0):=by
     apply the_wire A _ _ (fun _=> Action.flavor u) (fun x y=>by unfold Run.block; rw[step_brute,step_brute]; exact Exposure.flavor_shift (stitch S R x) _ (S.admissible _) _ _ (ContinuousMap.continuous _) u) _ hv; funext x
     have ht:=plume q F F 1 id (Lining.Temper.stroll _ u) (fun p i=>by rw [Signed.act_one]; exact congr_fun (h p) i) hv x; rw[permit_one] at ht; exact ht
lemma trailP (h:∀ b:Cover, Action.parity ⇑(F b)=⇑(F b))(hv:l ≤ i): Action.parity (report A F q l 0)= ⇑(report A F q l 0):=by
     apply the_wire A _ _ (fun _=>Action.parity) (fun x y=>by unfold Run.block; rw [step_brute,step_brute]; exact Eq.symm (TorusPCAC.Finite.block_grade (stitch S R x) (S.admissible _) _ (ContinuousMap.continuous _) _ _)) _ hv; funext x
     have ht:=plume q F F 1 id QCD.Grass.grade (fun p i=>by rw [Signed.act_one]; exact congr_fun (h p) i) hv x; rw[permit_one] at ht; exact ht
lemma trackScale (z:ℂ): report A (z • F) q l 0=z • report A F q l 0:=by
     unfold report; rw[show visitor S i l q 0 (z • F)=z • visitor S i l q 0 F from ?_,show ∀ x:V0, relay A l (z • x)= z • relay A l x from fun x=>map_smul (relay (T:=i) A l) z x] -- inspect
     unfold visitor; rw [Patria.Rolls.roles,Patria.Rolls.roles]; exact (Patria.Rolls.rollLinear (k:=1) (M:=ratioTo S i l) (l:=Rolls.menu q) F _ ((z • LinearMap.id (R:=ℂ) (M:=V0)).restrictScalars ℝ)).symm
-- where.T
structure Roars (F:Axis → Cover → Insertion (S.side R i) 6) :Prop where
      color(a b): Action.charge ⇑(F a b)= ⇑(F a b)
      charm(a b u): Action.flavor u ⇑(F a b)= ⇑(F a b)
      still(a b):Action.parity ⇑(F a b)= ⇑(F a b)
      pin(a b s)(v:EuPin): v.Lifts s→Action.pin v s ⇑(F a b)= (↑(signT s a):ℂ) • ⇑(F (s.perm a) (s.act b))
local notation "Vx"=> Axis
open Tide
include hA
lemma unleash (F':Axis → Cover → Insertion (S.side R i) 6)(x:Axis→Label d)(Θ:SourceRead.TaperHol)(X:Bore d)(s:RawSym)(Q:Market S R d)(hR:Rubric s X)(hW:Wager A Θ X Q l)(h:Roars F')(ht:l ≤ i)(hX:∀ j,Tally Θ 0 (x j) (A.density l) (report A (F' j) (Rolls.shelV j) l 0)): x∈ RawVec d:=by
     let L(b):= report A (F' b) (Rolls.shelV b) l 0
     let M' := A.density l; have hv:= pier A hA hW.siteM
     refine ⟨fun i=>⟨?_,fun u=>?_⟩,fun i=>?_,fun p v hh a=>?_,fun _=>(one_smul ..).symm⟩
     · rw [←s.parityActs]; have hp:=Canvas.hingeP Θ (L i) (s.parity _ (x i)) (fun u=>⇑(X (Mμ l) 0 u)) (hX i) hW.reading (by rw[hv]; exact (arrives A l hW.siteM).2.2.2.2) (hR.parity _ _ _); rw[show Action.parity (L i)= ⇑(L i) from trailP A _ _ (h.still _) ht] at hp; rw [Canvas.consensus _ _ _ hp _ (hX _)]
     · rw [←s.flavorActs]; have hp:= Canvas.arrows Θ u (L i) (s.flavor _ u (x i)) (fun u=>⇑(X (Mμ l) 0 u)) (hX i) hW.reading (by rw[hv]; exact (arrives A l hW.siteM).2.2.1 _) (hR.flavor _ _ _ _); rw[show Action.flavor u (L i)= ⇑(L i) from trailF A _ _ u (fun b=>h.charm _ b u) ht] at hp; rw [Canvas.consensus _ _ _ hp _ (hX _)]
     · rw [←s.chargeActs]; have hp:= Canvas.swingC Θ (L i) hW.living (s.charge _ (x i)) (fun u=>⇑(X (Mμ l) 0 u)) (hX i) hW.reading (by rw [hv]; exact (arrives A l hW.siteM).2.2.2.1) (hR.charge _ _ _); rw[show Action.charge (L i)= ⇑(L i) from trailC A _ _ (h.color _) ht] at hp; rw [Canvas.consensus _ _ _ hp _ (hX _)]
     rw [←s.pinActs]; have hp:= Canvas.hinge p Θ v (L a) hh hW.living (s.pin _ v (x a)) (fun u=>⇑(X (Mμ l) 0 u)) (hX a) hW.reading (by rw[hv]; exact (arrives A l hW.siteM).1 _ _ hh) (by have hk:=hR.pin (Mμ l) (x a) 0 p v hh; rw [Signed.act_zero] at hk; exact hk)
     let t:ℂ:= signT p a; have he' : Action.pin v p (L a)=t • ⇑(L (p.perm a)):=by have he:= trail1 A (Rolls.shelV a) _ (t • F' (p.perm a)) p v hh (fun b=>h.pin a b p v hh) ht; rw [show Averaging.permute p (Rolls.shelV a)=Rolls.shelV (p.perm a) from Rolls.pays_rotate _ _,trackScale A] at he; exact he
     rw [he'] at hp; rw [Canvas.consensus _ _ _ hp _ (Needle.quotaY _ _ _ _ _ _ (hX (p.perm a)))]; rfl
end YM.Massive.PCAC.Oren

#print axioms YM.Massive.PCAC.Oren.unleash
