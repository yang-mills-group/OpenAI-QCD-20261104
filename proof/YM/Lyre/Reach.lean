import YM.Lyre.Left
/-! # joint expectations with Borel probes both directions -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lyre
open Function Filter QCD.Lat QCD MeasureTheory Lattice Wilson QCD.Grass
open Push.GridApprox Tide Transfer
open RG Kit Kites NormedSpace
open scoped Topology ComplexOrder Matrix.Norms.L2Operator Classical
variable {A B C:Type*}[Fintype A][Fintype B][Fintype C]

open YM.Next.Free Wilson Flume
variable {i j F:ℕ} {c f:Side}
open Lattice
variable (P:Flight i j)(hf:f.val=c.val*P.L.val){β w:ℝ}{K:KernelChoices}
lemma mode_eq(Q:Matrix (Modes c F) (Modes f F) ℂ)(x:Lat.Fields f F)(y:Lat.Fields c F): ber (Modes c F) (y * sheath 1 Q x)= ber _ (Tide.furnace Q y*x):= left_shore Q x y
lemma shift_eq(Q:Matrix (Modes c F) (Modes f F) ℂ)(x:Lat.Fields f F)(y:Lat.Fields c F): ber (Modes c F) (sheath 1 Q x*y)= ber _ (x*Tide.furnace Q y):= right_shore Q x y
-- test instance at physical.B. both linear character orders exact.
set_option maxHeartbeats 650000 in
lemma starboard (u x: Grid c→Lat.Fields c F)(Y: Grid f→Lat.Fields c F)(h:P.patch.Branches K su)(hu:u=(P.visit K hf).push β Y)(hp:Stays x)(hY:Stays Y):
    (∫ V, ber _ (u V*x V) ∂prior su c) = ∫ U:Grid f, ber _ (Y U*brook (P.visit K hf) β x U) ∂prior su f:=by
     let A:= P.visit K hf; have hk:A.IsKernel β su:= A.isKernel h β; subst u
     let vq(U:Grid f)(V:Grid c):=A.density β U V; let X:= fun U V=>ber (Modes c F) ((vq U V • Y U)*x V)
     have hw: Integrable (uncurry X) ((prior su f).prod (prior su c)):=by
          have hz: Stays (fun U:Grid f×Grid c=> Y U.1*(A.density β U.1 U.2 • x U.2)):= (hY.travel measurable_fst).mult (delta (S:=A) h x hp β)
          let k:= (ber (Modes c F)).toContinuousLinearMap
          have ht : Stays (fun U:Grid f×Grid c=> k (Y U.1*(A.density β U.1 U.2 • x U.2))):=hz.flows k.continuous
          have H: uncurry X= fun U:Grid f×Grid c=> k (Y U.1*(A.density β U.1 U.2 • x U.2)):= funext fun i=> congr_arg (ber _) (by change (A.density β i.1 i.2 • _)*_= _; rw [mul_smul_comm, smul_mul_assoc]); rw [H]; exact ht.intg _
     have ht(V:Grid c): ber _ ((A.push β Y V)*x V)=∫ U:Grid f, X U V ∂prior su f:=by
          let Z:= ((ber _).comp (LinearMap.mulRight ℂ (x V))).toContinuousLinearMap
          exact (Z.integral_comp_comm (A.push_slice hk V Y (hY.intg _))).symm
     have he(U:Grid f): ber _ (Y U*brook A β x U)= ∫ V:Grid c,X U V ∂prior su c:=by
          let Z:= ((ber _).comp (LinearMap.mulLeft ℂ (Y U))).toContinuousLinearMap
          change Z (brook A β x U)= _; rw [brook,← Z.integral_comp_comm (deltaPay (β:=β) (S:=A) h x hp U)]; apply integral_congr_ae; apply ae_of_all; intro i; change ber (Modes c F) (Y U*(vq U i • x i))= ber _ ((vq U i • Y U)* x i); rw [mul_smul_comm,smul_mul_assoc]
     change (∫ V,ber _ ((A.push β Y V)*x V) ∂prior su _) = ∫ U,ber _ (Y U*(brook A β x U)) ∂prior su _; simp_rw [ht,he]; exact (integral_integral_swap hw).symm
set_option maxHeartbeats 650000 in
lemma portD (u x: Grid c→Lat.Fields c F)(Y: Grid f→Lat.Fields c F)(h:P.patch.Branches K su)(hu:u=(P.visit K hf).push β Y)(hp:Stays x)(hY:Stays Y):
    (∫ V, ber _ (x V*u V) ∂prior su c) = ∫ U:Grid f, ber _ (brook (P.visit K hf) β x U*Y U) ∂prior su f:=by
     let A:= P.visit K hf; have hk:A.IsKernel β su:= A.isKernel h β; subst u
     let vq(U:Grid f)(V:Grid c):=A.density β U V; let X:= fun U V=>ber (Modes c F) (x V*(vq U V • Y U))
     have hw: Integrable (uncurry X) ((prior su f).prod (prior su c)):=by
          have hz: Stays (fun U:Grid f×Grid c=> (A.density β U.1 U.2 • x U.2)*Y U.1):= (Tide.delta (S:=A) h x hp β).mult (hY.travel measurable_fst)
          let k:= (ber (Modes c F)).toContinuousLinearMap
          have ht : Stays (fun U:Grid f×Grid c=> k ((A.density β U.1 U.2 • x U.2)*Y U.1)):=hz.flows k.continuous
          have H: uncurry X= fun U:Grid f×Grid c=> k ((A.density β U.1 U.2 • x U.2)*Y U.1):= funext fun i=> congr_arg (ber _) (by change _*(A.density β i.1 i.2 • _)= _; rw [mul_smul_comm, smul_mul_assoc]); rw [H]; exact ht.intg _
     have ht(V:Grid c): ber _ (x V*(A.push β Y V))=∫ U:Grid f, X U V ∂prior su f:=by
          let Z:= ((ber _).comp (LinearMap.mulLeft ℂ (x V))).toContinuousLinearMap
          exact (Z.integral_comp_comm (A.push_slice hk V Y (hY.intg _))).symm
     have he(U:Grid f): ber _ (brook A β x U*Y U)= ∫ V:Grid c,X U V ∂prior su c:=by
          let Z:= ((ber _).comp (LinearMap.mulRight ℂ (Y U))).toContinuousLinearMap
          change Z (brook A β x U)= _; rw [brook,← Z.integral_comp_comm (deltaPay (β:=β) (S:=A) h x hp U)]; apply integral_congr_ae; apply ae_of_all; intro i; change ber (Modes c F) ((vq U i • x i)*Y U)= ber _ (x i*(vq U i • Y U)); rw [mul_smul_comm,smul_mul_assoc]
     change (∫ V,ber _ (x V*(A.push β Y V)) ∂prior su _) = ∫ U,ber _ (brook A β x U* Y U) ∂prior su _; simp_rw [ht,he]; exact (integral_integral_swap hw).symm
lemma sheathH [DecidableEq A][DecidableEq B](G:Grid f→Matrix A B ℂ)(h:Continuous G):Continuous (fun i:Grid f × Dirac B=> Kit.sheath 1 (G i.1) i.2):=by
    have hv:Continuous (fun i:Grid f × Dirac B=>(G i.1,i.2)):= (h.comp continuous_fst).prodMk continuous_snd
    change Continuous ((fun i: Matrix A B ℂ × Dirac B=> Kit.sheath 1 i.1 i.2)∘fun i: Grid f × Dirac B=>(G i.1,i.2))
    exact (Kit.sheath_cont (A:=B) (B:=A) (b:=1)).comp hv
lemma continuousH [DecidableEq A][DecidableEq B](G:Grid f→ Matrix A B ℂ) (h:Continuous G)(x:Grid f→Dirac B)(hp:Stays x): Stays (fun U=> Kit.sheath 1 (G U) (x U)):=resident (A:=Pairs B) (B:=Pairs A) (X:=Grid f) (fun i:Grid f× Dirac B=>Kit.sheath 1 (G i.1) i.2) x (sheathH G h) hp
lemma reimburse (x:Stud f F)(hx:Stays x): Stays (soften P hf x):=continuousH (f:=f) (fun U:Grid f=> Kit.choir F (Flume.tied P hf 0 U)) ((Kit.choir_cont _).comp (Pine.tied_cont P hf 0)) x hx
lemma won {x :Stud f F} (hP:P.patch.Branches K su)(hx:Stays x): Continuous (transfer P K hf β w x):=(rescale w (F:=F) (c:=c)).toLinearMap.continuous_of_finiteDimensional.comp
   (push_continuous P K hf β hP _ ((reimburse P hf x hx).intg _))
lemma repaint (x:Lat.Fields c F) (h: w≠ 0) : rescale w (patternC c F w⁻¹ x)=x:=by
    change engine w _ (engine w⁻¹ _ x)=x; rw [makes,mul_inv_cancel₀ h]; apply QCD.Stew.poster; intro s; rw [fundW]; simp
variable (h:P.patch.Branches K su)(hw:w≠0)(x:Stud c F)(Y: Stud f F)(hp: Stays x)(hY:Stays Y)
include h hw hp hY
lemma echo_left:
    joint (x * transfer P K hf β w Y)= growth c F w * joint (Tide.offer P K hf β (stampC x w⁻¹)*Y):=by
   let u:=stampC x w⁻¹; let g:=growth c F w
   let v:= soften P hf Y; let z:=(P.visit K hf).push β v
   have ht(V:Grid c): x V* transfer P K hf β w Y V=rescale w (u V*z V):=(congr_arg (·* transfer _ _ _ _ _ _ _) (repaint (x V) hw).symm).trans (map_mul _ _ _).symm
   unfold joint; simp_rw [Pi.mul_apply,ht,volumeScale, integral_const_mul];
   rw [show (∫ V:Grid c,ber (Modes c F) (u V*z V) ∂prior su c)= _ from portD P hf z u v h rfl (paysA x hp) (reimburse P hf Y hY)]
   congr 1; apply integral_congr_ae; apply ae_of_all; intro V; exact mode_eq _ _ _
lemma echo_right:
    joint (transfer P K hf β w Y * x)= growth c F w * joint (Y*Tide.offer P K hf β (stampC x w⁻¹)):=by
   let u:=stampC x w⁻¹; let g:=growth c F w
   let v:=soften P hf Y; let z:=(P.visit K hf).push β v
   have ht(V:Grid c): transfer P K hf β w Y V*x V=rescale w (z V*u V):=(congr_arg (transfer _ _ _ _ _ _ _*·) (repaint (x V) hw).symm).trans (map_mul _ _ _).symm
   unfold joint; simp_rw [Pi.mul_apply,ht,volumeScale, integral_const_mul];
   rw [show (∫ V:Grid c,ber (Modes c F) (z V*u V) ∂prior su c)= _ from starboard P hf z u v h rfl (paysA x hp) (reimburse P hf Y hY)]
   congr 1; apply integral_congr_ae; apply ae_of_all; intro V; exact shift_eq _ _ _
end YM.Massive.Lyre
#print axioms YM.Massive.Lyre.won
#print axioms YM.Massive.Lyre.echo_left
#print axioms YM.Massive.Lyre.echo_right
