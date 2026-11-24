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
lemma seamz (A: Step)(o:Site c): ∃ e:Edge (Site c),e.1∈ stand o ∧ e.1+step e.2 ∈ stand o ∧∃ L:Mat→L[ℝ]Mat,(∀ i,‖L i‖≤‖i‖) ∧ ∀ V:Grid c,hitch 0 V A o=L (colourLink e V):=by
    have hp:=stem o o (o+A.vec) A rfl rfl; let v:=glint 0 o A
    have hh:‖v‖=1:=by change ‖seam _ _ _‖=_; rcases seam_cases (0:Site c) (A.used o).1 _ with h|h <;> rw [h]<;> simp -- convert
    let T: Mat→L[ℝ]Mat := ContinuousLinearMap.restrictScalars ℝ (v • ContinuousLinearMap.id ℂ Mat)
    have hM M: ‖T M‖=‖M‖:=by change ‖v • M‖= _; rw [norm_smul,hh,one_mul]
    cases A with | mk i b =>
      cases b
      · exact ⟨(o,i),hp.1,hp.2,T,fun i=>(hM i).le,fun _=>rfl⟩ -- motive hh depends W
      refine ⟨(o-step i,i),?_ , ?_,T.comp (starL' ℝ |>.toContinuousLinearMap),fun i=>?_,fun V=>?_⟩
      · change o-step i∈stand o; rw [sub_eq_add_neg]; exact hp.2
      · change o-step i+step i∈_; rw [sub_add_cancel]; exact hp.1
      · change ‖T (star i)‖ ≤ _; rw [hM,norm_star]
      change v • colour (_⁻¹) =v • star (colour _); rw [colour_inv];simp [Step.used]
abbrev stratum (C:ℝ)(n:ℕ)(o:Site c)(p:BudgetPoint):Prop:=∀ e:Edge (Site c),e.1 ∈ stand o → ∀ l : List (Directions su c), l.length ≤p.order →(∀ i∈l,p.dirBound o i)→∀ U:Grid c, ‖leftDerivs (colourLink e) l U‖ ≤ C
def goldW : Spike→L[ℂ]Bundle:= LinearMap.toContinuousLinearMap { toFun:=wave,map_add':=fun x y=> (wave_add ..).symm,map_smul':=fun i v=> (Matrix.smul_kronecker ..) }
def silverW : Mat→L[ℝ] Bundle:= ContinuousLinearMap.restrictScalars ℝ (LinearMap.toContinuousLinearMap { toFun:=touch,map_add':=fun x y=> (touch_add ..).symm,map_smul':=fun i v=> Matrix.kronecker_smul .. } : Mat→L[ℂ] Bundle)
def follow (A:Spike): Mat→L[ℝ]Bundle:= ContinuousLinearMap.comp (ContinuousLinearMap.restrictScalars ℝ (ContinuousLinearMap.mul ℂ Bundle (wave A))) silverW -- parens need
lemma vigor (i:Mat)(A:Spike): ‖follow A i‖ ≤ ‖goldW‖*‖silverW‖*‖A‖*‖i‖:=by
    change ‖wave _ * touch _‖≤ _; apply (norm_mul_le ..).trans; apply (mul_le_mul (goldW.le_opNorm A) (silverW.le_opNorm i) (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans; exact le_of_eq (by ring)
variable {C:ℝ} (hp:stratum C n o p) (hx:0<a)(he: 0≤C)
lemma leader (i j : Site c)(M:Mat→L[ℝ]Bundle)(e: Edge (Site c))(hi:i∈stand o)(hj:j∈stand o)(hw:e.1∈stand o)(hv:e.1+step e.2∈stand o)(w:ℝ)(h:∀ x,‖M x‖ ≤ w*‖x‖)(hn:0≤w)(N:ℕ)(hh:0<a)(hp:stratum C n o p)(ht:0≤C) : Woven o (stand o) p a (fun V : Grid c=> paleF N (block i j (M (colourLink e V)))) (9*a^2*fingers N^2*(w*C)) :=by
    let F: Bundle→L[ℝ] EvenA c N:= ContinuousLinearMap.restrictScalars ℝ ((nozzle c N).comp (blockL i j)); let A:=F.comp M; let u (V:Grid c):=colourLink e V; have hq V : Chart p.order (A ∘ u) V:= A.contDiff.contDiffAt.comp 0 (link_chart e V p.order)
    have hs : Continuous u:= (show Continuous u from colour_cont.comp (continuous_apply e)) -- name
    refine ⟨fun U V H=> congr_arg (fun k=> A (colour k)) (H e hw hv),fun _=> padBl i j _ hi hj,fun i _=>hq i,fun U hu l hl hp₀=> ?_,(A.continuous.comp hs).measurable,by positivity⟩ -- edit
    change Sen o a (leftDerivs (A ∘ u) l U) ≤ _; rw [Push.Local.left_linear A l (link_chart e U p.order) hl]; exact (budgetBl _ i j hi hj hh N).trans (mul_le_mul_of_nonneg_left ((h _).trans (mul_le_mul_of_nonneg_left (hp e hw _ hl hp₀ U) hn)) (by positivity))
include hp hx he
def foamer (C:ℝ)(F:ℕ):=9*fingers F^2*‖goldW‖*‖silverW‖*C
lemma hale (M:Spike)(i:Step)(N:ℕ):
    let f(U:Grid c):= localX o M*leg 0 U i
    Woven o (stand o) p a (fun V=> paleF N (f V)) (foamer C N* (a^2 *‖M‖)) ∧ Woven o (stand o) p a (fun V=>paleF N (star (f V))) (foamer C N*(a^2*‖M‖)) :=by
    intro f; let j:=o+i.vec; obtain ⟨e,h0,h1,L,hL,hK⟩:=seamz i o; let T:= (follow M).comp L
    have hM U:f U=block o j (T (colourLink e U)):=by unfold f; rw [couple,hK]; rfl
    let D:=‖goldW‖*‖silverW‖*‖M‖; have hP:0≤D:=by unfold D; positivity
    have ht u: ‖T u‖≤ D*‖u‖:=(vigor (L u) M).trans (mul_le_mul_of_nonneg_left (hL _) hP)
    obtain ⟨hy,hz⟩:=stem o o j i rfl rfl; simp_rw [hM,starBl]; rw [show foamer C N*(a^2*‖M‖)=9*a^2*fingers N^2*(D*C) by unfold foamer D; ring]; refine ⟨leader o j T e hy hz h0 h1 D ht hP N hx hp he,leader j o ((starL' ℝ).toContinuousLinearMap.comp T) e hz hy h0 h1 D ?_ hP N hx hp he⟩ -- need hFun fix
    intro v; change ‖star (T v)‖≤_; rw [norm_star]; exact ht v
end YM.QCD.Stew
