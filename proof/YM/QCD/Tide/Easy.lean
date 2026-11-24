import YM.QCD.Tide.Milky
import YM.QCD.Vita.Ravine
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Tide
open Lattice Wilson Grass Lat NormedSpace Function MeasureTheory Filter RP Kit Finset RG Push.GridApprox Jets
open scoped BigOperators Matrix.Norms.L2Operator Matrix Topology ComplexOrder Classical
variable {n c f : Side}{F:ℕ}{β:ℝ} {R:Cells.Cut c} {K:KernelChoices}
open Flume YM.Next.Free Kites Acre Rails Rain Loom Fleet
variable {i j:ℕ} (P:Flight i i)(hf:f.val=c.val*P.L.val){t:ℝ}
-- finite observable system
noncomputable def fresh (Y:Pixel c F)(x:Stud c F):ℂ:= ∫ V,ber _ (Cove.light _ (Y V)*x V) ∂prior su c
set_option maxHeartbeats 650000 in
lemma rightD (u x: Grid c→Fields c F)(Y: Grid f→Fields c F)(h:P.patch.Branches K su)(hu:u=(P.visit K hf).push β Y)(hp:Stays x)(hY:Stays Y):
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
lemma chair (Y:Pixel f F)(x:Stud c F)(h:P.patch.Branches K su)(hp:Stays x)(hY:Continuous Y): (∫ V,ber _ (advance P K hf Y β V*x V) ∂prior su c)= fresh Y (offer P K hf β x):=by
     rw [rightD P hf _ _ (can P hf F Y) (K:=K) (β:=β) h rfl hp (stays (Rain.tenderL P hf Y hY))]; unfold fresh; exact integral_congr_ae (ae_of_all _ fun U=> Tide.ship _ _ _ (Cove.bright (Y U)))
-- rescaling
noncomputable abbrev patternC (c:Side)(F:ℕ)(t:ℝ):= engine t (Cove.Keys c F)
noncomputable def stampC (x:Stud c F)(t:ℝ):Stud c F:= fun V=> patternC c F t (x V)
lemma gainP (x:Fields c F): ber _ (patternC c F t x)= (gain t c F:ℂ)*ber _ x:=by
    unfold ber; simp only [LinearMap.smul_apply, patternC, fundW, smul_eq_mul,card_univ,Rain.gain,Cove.Keys,Complex.ofReal_pow]; ring
lemma paysA (x:Stud c F)(h:Stays x):Stays (stampC x t):= h.flows ((patternC c F t).toLinearMap.continuous_of_finiteDimensional)
lemma pov (X:Pixel f F)(Y:Pixel c F)(h:P.patch.Branches K su)(ht:0<t)(hz:Modern P K hf β t X Y)(x:Stud c F)(hp:Stays x)(hX:Continuous X):fresh Y x=fresh X (offer P K hf β (stampC x t⁻¹)):=by
    rw [← chair P hf _ _ h (paysA x hp) hX]; unfold fresh; apply integral_congr_ae; refine ae_of_all _ fun V=>?_ ; dsimp only; rw [hz]; let g:= gain t⁻¹ c F; let u:= patternC c F t⁻¹; have he : 0<g:=pow_pos (inv_pos.mpr ht) _
    let L:= Cove.light (Cove.Keys c F); change _=ber _ (((↑(g⁻¹):ℂ) • u (L (Y V)))*u (x V)); rw [smul_mul_assoc,← map_mul, map_smul, gainP,smul_eq_mul,← mul_assoc]; change _=((g⁻¹:ℝ)* (g:ℂ))*_; rw [Complex.ofReal_inv,inv_mul_cancel₀ (by exact_mod_cast he.ne'),one_mul]
end YM.QCD.Tide
