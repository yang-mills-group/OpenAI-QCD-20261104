import YM.QCD.Agate.Inner
import YM.QCD.Agate.Sink
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Agate
open Land Lattice Wilson Grass Lat NormedSpace Function MeasureTheory Filter RP Kit Finset RG Push.GridApprox
open scoped BigOperators Matrix.Norms.L2Operator Matrix Topology ComplexOrder Classical
variable {n c f G K: Side}{F:ℕ}{β:ℝ} {Y:StepData c f}
open Tide Flume YM.Next.Free
variable {D S:Lot} {p:Site c}
noncomputable def pins (h:Fits c D)(p:Site c):Court D↪Site c := ⟨fun i=>leap p i.val,by intro i j he; exact Subtype.ext (h i.2 j.2 (add_right_cancel he))⟩
noncomputable def capH (Y:StepData c f)(h:Fits c D)(p:Site c)(u:Court D→ Y.patch.FrameTag): Y.SitesChoice:= Function.extend (pins h p) u (fun _=> Classical.arbitrary _)
lemma cappie (h:Fits c D)(t:Court D→ Y.patch.FrameTag)(i:Court D): capH Y h p t (pins h p i) = t i := (pins h p).injective.extend_apply ..
noncomputable def pram (Y:StepData c f)(h:Fits c D)(p:Site c)(U:Grid f)(u:Court D→Y.patch.FrameTag)(β:ℝ)(P:Trace D→ℂ):= ∫ V:Trace D,(∏ i:Pipe D,(perLink Y β U (capH Y h p u) (strike p i) (V i):ℂ))*P V ∂Measure.pi (fun _=> su.probHaar)
noncomputable def united (Y:StepData c f)(β:ℝ)(h:Fits c D)(p:Site c)(P:Trace D→ℂ)(U:Grid f):= ∑ t:Court D→ Y.patch.FrameTag,(∏ i:Court D,(perSite Y U (pins h p i) (t i):ℂ))*pram Y h p U t β P
lemma cup (h:Fits c D)(P:Trace D→ℂ)(ht:Stays P)(U:Grid f)(hp:Y.patch.Branches Y.kernel su): Push.GridApprox.back Y β (P∘crest p) U= united Y β h p P U:=by
  let l:= pins h p; let E:Pipe D↪Edge (Site c):=⟨strike p,crested p h⟩
  let q (t:Y.SitesChoice)(e: Edge (Site c))(v:su.El):ℂ:= perLink Y β U t e v
  let F:= P∘ crest p; let B (t: Y.SitesChoice):= ∫ V,(∏ e,q t e (V e))* F V ∂prior su c
  have hz (t:Y.SitesChoice): B t= pram Y h p U (t∘⇑l) β P:=by
      have hh e: (∫ x, q t e x ∂su.probHaar)=1:= Eq.trans (integral_ofReal (𝕜:=ℂ) (f:= perLink Y β U t e)) (by rw [perLink_mass]; rfl)
      change (∫ u:(Edge (Site c)→su.El),(∏ e,q t e (u e))*P (u∘⇑E) ∂Measure.pi (fun _=> su.probHaar))= _
      rw [LocalCup.shelf E P (q t) hh]; unfold pram; apply integral_congr_ae; apply ae_of_all; intro i; dsimp only; apply congr_arg (· * P i); apply prod_congr rfl; intro e _
      have hv: Y.connector U (capH Y h p (t∘⇑l)) (E e)= Y.connector U t (E e):=by
           apply connector_dep Y hp _ _ _ (cappie h (t∘⇑l) (inlet e)) _ (fun _ _ _=>rfl) (fun _ _ _=>rfl); change capH Y h p (t∘⇑l) ((strike p e).1+ step (strike p e).2)= t ((strike p e).1+step (strike p e).2); rw [← drainH]; exact cappie h _ (drain e)
      unfold q perLink; change _=(↑(∑ r : Y.patch.Points,Y.patch.predictorMass _ (Y.connector U (capH Y h p (t∘⇑l)) (E e)) r*noiseLink Y β _ _):ℂ); rw [show E e= strike p e from rfl] at hv; simp_rw [show E e=strike p e from rfl, hv]
  let s (i : Site c)(r:Y.patch.FrameTag):ℂ:=perSite Y U i r; have he (i:Site c): ∑ r,s i r=1:=by unfold s perSite; rw [← Complex.ofReal_sum,Y.patch.frameMass_sum hp,Complex.ofReal_one]
  unfold Push.GridApprox.back; simp_rw [density_parts,Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_prod, Finset.sum_mul,mul_assoc]
  rw [integral_finsetSum];
  · simp_rw [integral_const_mul]; change (∑ t:Y.SitesChoice,(∏ x,s x (t x))*B t)=_; simp_rw [hz]; exact LocalCup.plated l (fun t=> pram Y h p U t β P) s he
  intro t _; refine Integrable.const_mul ?_ _; have ha: Envelope F:= ⟨(ht.travel ((crestC p).measurable)).mes,(ht.travel ((crestC p).measurable)).bounded⟩
  exact Envelope.integrableC ((Envelope.prodC _ (fun (e : Edge (Site c)) (V:Grid c)=> q t e (V e)) (fun e _=> (Envelope.compactC (Complex.continuous_ofReal.comp (perLink_cont Y β U t e))).comp_env (measurable_pi_apply _))).mulC ha) _ -- arg order?
end YM.QCD.Agate
