import YM.Fir.Camp
/-! Time-tagged genuine finite expenditures descend to REAL field quotient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Fir
open YM.Analysis YM.Fir YM.Fir.Mesh YM.Fir.NoteF Needle Needle.GaugeP Filter Set Function Metric TagF
open Lattice Cells QCD QCD.Lat Patria Patria.Depth Patria.Hub
open UV Poised Plans Plans.Stamp Intag.Vale
open scoped Topology ContDiff BigOperators Classical
variable {C:Sequence} {P:Calibration C} {G:∀ d,Cottage P d} {β e:ℝ}(hp:C.Path β e)(hr:Sway C.S) {n:ℕ} {φ:ℕ→ℕ}(hφ:Tendsto φ atTop atTop)
namespace Sash
variable (s:Sash G φ)
variable {Z:SpaceZ}(H:Ability P φ Z)(hz:DriftF G φ)
include H hφ hp hr hz
variable (d:ℕ)
omit hz in
lemma believe (V:(i:ℕ)→stalk C i)(Y:ℕ→ CellF d)(z:CellF d)(h:Tendsto (Y ∘ φ) atTop (𝓝 z))(hv:Brush (G _).E (G _).K V Y)(p:Fin n)(t:Fin n→TagF)(x:Points n)(hx:x∈conf n):Exposes C φ (fun i=>tube C (packTag P t) p V (φ i)) x (puts Z x t p d (s.R d z)):=by
    let q(i):= glass G d Y i; let p'(i):= ridgeF G d i (Y i); let U:=packTag P t
    have h1:= snow hp U V p G hφ x hx Y hv (fun k _=> ((G _).pointsP hp hr none (fun _=> (t k).2) ⟨_,norm_nonneg (t k).2,Eventually.of_forall fun _=> le_rfl⟩).1); have h2:Tendsto (p' ∘ φ) atTop (𝓝 (s.R d z)):=voiceL (s.pearls _) h; have ht:=orient H t p p' (s.R d z) h2 x hx; have H':= h1.add ht; rw [zero_add] at H'; exact H'.congr (fun i=> sub_add_cancel ..)
include s
lemma increment :∃ M:Label d→ₗ[ℂ] Label (d+1),∀ n (t:Fin n→TagF)(x:Points n), x∈conf n→∀ p (v:Label d), puts Z x t p _ v=puts Z x t p (d+1) (M v):=by
    choose a hA v hv using hz.views d
    let T (i):= s.R (d+1) (v i); let B:=lid d; let M:= B.constr ℂ T; refine ⟨M,fun n t x hx p u=>?_⟩
    suffices Hx: puts Z x t p d=(puts Z x t p _).comp M from DFunLike.congr_fun Hx u
    refine B.ext fun i=> ?_; change puts Z x t p d (B i)= puts Z x t p (d+1) (M (B i)); rw [show M (B i)=T i from Module.Basis.constr_basis ..]; letI:= alive hp hφ x; exact tendsto_nhds_unique (orient H t p (fun _=>B i) _ (show Tendsto ((fun _=>B i) ∘ φ) atTop (𝓝 (B i)) from tendsto_const_nhds) _ hx) (s.believe hp hr hφ H (d+1) _ (a i) (v i) (hv i) (hA i) p t x hx)
-- for D.Ext genuine derivative expenditure.
variable (b:Axis)
lemma steer :∃ M:Label d→ₗ[ℂ] Label (d+2),∀ n (t:Fin n→TagF)(x:Points n), x∈conf n →∀ p (v:Label d), Exposes C φ (fun i=> tube C (packTag P t) p (fun k=> lDer C k b (stem P d k v)) (φ i)) x (puts Z x t p _ (M v)) :=by
    choose a hA v hV using fun i:Stone d=>hz.walks d i b; let T (i):=s.R _ (v i); let B:=lid d; let M:= B.constr ℂ T; refine ⟨M,fun n t x hx p u=>?_⟩
    let F(q:ℕ×Strings n): Label d→ₗ[ℂ] ℂ:=(readZ (C:=C) (φ q.1) p q.2 (fun j=> packTag P t j (φ q.1))).comp ((lDer C (φ q.1) b).comp (stem P d (φ q.1))); let V:= Watch C φ x; let K:=(puts Z x t p _).comp M
    have he(v:Label d)(q:ℕ×Strings n): tube C (packTag P t) p (fun k=>lDer C k b (stem P d k v)) (φ q.1) q.2= F q v:= meters (packTag P t) (fun k=>lDer C k b (stem P d k v)) p (φ q.1) q.2
    have hp':∀ v:Label d,Tendsto (fun q=> F q v) V (𝓝 (K v)):=by
         intro z; have h(i:Stone d): Tendsto (fun q=>F q (lid d i)) V (𝓝 (K (B i))):=by
             rw [show K (B i)= _ from (show K (B i)=puts Z x t p _ (T i) from DFunLike.congr_arg (puts Z x t p _) (show M (B i)=T i from Module.Basis.constr_basis ..))]; exact (s.believe hp hr hφ H _ _ _ _ (hV _) (hA i) p t x hx).congr (he _ )
         let v(i):=B.repr z i; let L(i):= lid d i; have hx: z=∑ i,v i • L i :=(B.sum_repr z).symm
         change Tendsto (fun q=> F q z) V (𝓝 (K z)); rw [hx]; simp_rw [map_sum,map_smul]; exact tendsto_finsetSum Finset.univ (fun i _=>((h i).const_smul _))
    exact (hp' u).congr (fun q=> (he u q).symm)
end Sash
end YM.Massive.Fir
#print axioms YM.Massive.Fir.Sash.increment
#print axioms YM.Massive.Fir.Sash.steer
