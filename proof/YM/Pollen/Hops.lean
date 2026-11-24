import YM.Pollen.Dough
import YM.QCD.Stew.Nexus
/-! # bond Woven cost at smooth representative. Mask loans subsequently. No expectation subtractions baked in -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N n z:ℕ} {v:Strut c}{k:Spike}{g:Site c→ℂ} {w r a u:ℝ}{p:BudgetPoint}{o:Site c}
open Revolve Flume Quarry AnalyticBridge.VerifiedReset Port Jets Jets.Sun
variable {B: Support c}
local notation "tem" p:arg=> halo 1 {p}
lemma stemR (o:Site c)(a:Step) : o∈tem o∧ o+a.vec ∈ tem o:=by
    refine ⟨halo_subset _ _ (mem_singleton_self _),halo_spec.mpr ⟨o,mem_singleton_self _,?_⟩⟩; rw [separation_comm, separation, add_comm,add_sub_cancel_right]; unfold Step.vec; split; rw [pdist_neg]; exact pdist_step _; exact pdist_step _
lemma treatT (A: Step)(o:Site c): ∃ e:Edge (Site c),e.1∈ tem o ∧ e.1+step e.2 ∈ tem o ∧∃ L:Mat→L[ℝ]Mat,(∀ i,‖L i‖≤‖i‖) ∧ ∀ V:Grid c,hitch 0 V A o=L (colourLink e V):=by
    have hp:=stemR o A; let v:=glint 0 o A
    have hh:‖v‖=1:=by change ‖seam _ _ _‖=_; rcases seam_cases (0:Site c) (A.used o).1 _ with h|h <;> rw [h]<;> simp -- convert
    let T: Mat→L[ℝ]Mat := ContinuousLinearMap.restrictScalars ℝ (v • ContinuousLinearMap.id ℂ Mat)
    have hM M: ‖T M‖=‖M‖:=by change ‖v • M‖= _; rw [norm_smul,hh,one_mul]
    cases A with | mk i b =>
      cases b
      · exact ⟨(o,i),hp.1,hp.2,T,fun i=>(hM i).le,fun _=>rfl⟩ -- motive hh depends W
      refine ⟨(o-step i,i),?_ , ?_,T.comp (starL' ℝ |>.toContinuousLinearMap),fun i=>?_,fun V=>?_⟩
      · change o-step i∈tem o; rw [sub_eq_add_neg]; exact hp.2
      · change o-step i+step i∈_; rw [sub_add_cancel]; exact hp.1
      · change ‖T (star i)‖ ≤ _; rw [hM,norm_star]
      change v • colour (_⁻¹) =v • star (colour _); rw [colour_inv];simp [Step.used]
open Massive.PCAC QCD.Grass.Ward Further.DenseMixedKernels
open scoped Kronecker
variable (o:Site c) (b:Step)(f:Flavor N) (U:Grid c)
local notation "μ"=> Modes c N
local notation "S"=> Sour μ
noncomputable def gateH (U: Grid c): Sour (Modes c N):= zone N o * (Kit.leg 0 U b ⊗ₖ Massive.PCAC.spot f f)
local notation "H"=> gateH o b f
local notation "R"=>spot f f
local notation "s*"=>silverW -- from Stitch import? Sut f does import whole via? check
lemma gateReading (i j:μ): H U i j= if i.1.1=o ∧ j.1.1=o+b.vec∧ i.2=f∧ j.2=f then touch (hitch 0 U b o) i.1.2 j.1.2 else 0:=by
     unfold gateH; rw [zleft]; split; next h=>
        rw [Matrix.kronecker_apply,leg_day,rr]; unfold spot; rw [h]; simp [eq_comm]; split_ifs <;> simp_all <;> grind
     next h=>rw [if_neg (fun hp=>h hp.1)]
lemma haloGate (q:Site c): LocalOn (tem o) H:=by
    obtain ⟨e,h1,h2,L,hM,hQ⟩:=treatT b o; intro X Z hV; ext i j; rw [gateReading,gateReading,hQ,hQ,show colourLink e X=colourLink e Z from congr_arg colour (hV _ h1 h2)]
lemma rungProj (U1:Frame c): H (Lattice.gauge U1 U)=Lat.rotates N U1 * H U *star (Lat.rotates N U1):=by
     let M:= siteRot U1; let l:=leg 0 U b; let s:=spot f f; let D:= Lat.rotates N U1; let V:=zone N o; have h:D= M ⊗ₖ 1:=Sway.choir_in ..
     unfold gateH; rw[gaugeLeg]; change V*_ = D*(V*_)*star D; rw [← mul_assoc D,show D*V=V*D from (commute_zone o U1).eq.symm,mul_assoc, mul_assoc,h,Lat.star_kr, ← Matrix.mul_kronecker_mul, mul_assoc V, ← Matrix.mul_kronecker_mul,star_one,one_mul,mul_one] -- commute reversed
lemma shaft (C:ℝ) (hn:0≤C) (he:∀ (e:Edge (Site c)),e.1 ∈ halo 1 {o}→ ∀ l : List (Directions su c), l.length ≤p.order →(∀ i∈l,p.dirBound o i)→∀ U:Grid c, ‖leftDerivs (colourLink e) l U‖ ≤ C) : Fetch o false H p (voucher N (‖TouchL‖*C)):=by
     obtain ⟨e,h1,h2,L,hM,hQ⟩:=treatT b o; let M: Bundle→L[ℝ]Bundle:= ContinuousLinearMap.id ℝ Bundle; let T:Mat→L[ℝ]Bundle:=(TouchL.restrictScalars ℝ).comp L; let X:= T ∘ colourLink e; have hT(u:Mat): ‖T u‖≤ ‖TouchL‖*‖u‖:=(TouchL.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hM _) (norm_nonneg TouchL)); have hp:0 ≤ ‖TouchL‖*C:=mul_nonneg (norm_nonneg TouchL) hn; apply pointFetch H (haloGate o b f o) _ _ _ _ hp
     · intro i j U he; rw [gateReading] at he; split at he; next h=> exact ⟨h.1,h.2.1.symm ▸ (stemR ..).2⟩
       exact False.elim (he rfl)
     · exact fun V k=>rungProj o b f V k
     · intro i j; simp_rw [gateReading]; split; swap; · exact continuous_const
       simp_rw [show ∀ U: Grid c, touch (hitch 0 U b o)=X U from fun V=>by rw [hQ]; rfl]; let g:Bundle→ℂ:= fun B=> B i.1.2 j.1.2; have he: Continuous g:=by unfold g; fun_prop
       exact he.comp (T.continuous.comp (colour_cont.comp (continuous_apply e)))
     intro i j z; simp_rw [gateReading]; split; swap; · exact ((show Pitch _ _ _ _ 0 (1:ℝ) from (by simpa using! Pitch.fixed (0:ℂ) zero_le_one))).mono hp zero_le_one le_rfl
     have h: Pitch (colourLink e) z (p.dirBound o) p.order C 1:=⟨link_chart e z p.order,fun l hl hL=>by rw [one_pow,mul_one]; exact he e h1 _ hl hL z⟩; let g:Bundle→L[ℝ]ℂ:=LinearMap.toContinuousLinearMap ({ toFun:=fun x=>x i.1.2 j.1.2,map_add':=fun i j=>rfl,map_smul':=fun i j=>rfl}:Bundle→ₗ[ℝ]ℂ)
     simp_rw [show ∀ U: Grid c,touch (hitch 0 U b o)=X U from fun V=>by rw [hQ]; rfl]; have hv:∀ x', ‖g x'‖ ≤ 1*‖x'‖:= fun x=> (show ‖x i.1.2 j.1.2‖≤ ‖x‖ from (Cost.north ..)).trans_eq (Eq.symm (one_mul _))
     have hf:=(h.linear T hT (norm_nonneg TouchL)).linear g hv zero_le_one; rw [one_mul] at hf; exact hf
end YM.QCD.Stew
#print axioms YM.QCD.Stew.shaft
