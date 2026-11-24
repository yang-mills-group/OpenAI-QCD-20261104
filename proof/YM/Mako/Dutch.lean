import YM.Mako.Tote
import YM.Work.A09
set_option maxHeartbeats 680000
set_option autoImplicit false
noncomputable section
namespace YM.Mako
open Function Filter Set Analysis
open Ortho (plane Skew)
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius
open Work.A09 Org
lemma clipneg {M:Type*}[Ring M](x y:M):clip x y= - clip y x:=by unfold clip; abel
lemma swapπ(a b:Axis):plane a b= -plane b a:= Subtype.ext (by simp [plane])
variable {V:Type*}[AddCommGroup V][Module ℂ V][FiniteDimensional ℂ V]
variable (F: Ortho.Skew →+ Module.End ℂ V)
def Clubs (F: Ortho.Skew →+ Module.End ℂ V):Prop:=∀(a b c d i:Axis),a≠i→b≠i→c≠i→d≠i→clip (F (plane a b)) (F (plane c d))= F (bracket (plane a b) (plane c d))
variable (h:Clubs F)
variable (a b c d:Axis)(hab:a≠b)(hac:a≠c)(had:a≠d)(hbc:b≠c)(hbd:b≠d)(hcd:c≠d)
lemma outside(a b c:Axis): ∃ x:Axis,a≠x∧b≠x∧c≠x:= (show ∀ a b c:Axis,∃ x:Axis,a≠x∧b≠x∧c≠x by decide) a b c
include h
lemma stuck (hab:a≠b)(hbc:b≠c)(hac:a≠c) : clip (F (plane a b)) (F (plane b c))=F (plane a c):=by
    obtain ⟨i,he,ht,hz⟩:=outside a b c; rw [h _ _ _ _ _ he ht ht hz,bracket_planes]; simp [hab,hac,hbc]
set_option quotPrecheck false
include hab hac had hbc hbd hcd h
lemma stunt : Commute (clip (F (plane a b)) (F (plane c d))) (F (plane b c)):=by
    apply (show clip (clip (F (plane a b)) (F (plane c d))) (F (plane b c))=0→ _ from sub_eq_zero.mp) -- sub_eq.. function codomain definitional
    rw [jac,stuck F h a b c hab hbc hac, stuck F h a c d hac hcd had, clipneg (F (plane c d)),stuck F h b c d hbc hcd hbd,show clip (F (plane a b)) (-F (plane b d))= -clip (F (plane a b)) (F (plane b d)) from (by unfold clip; rw[mul_neg,neg_mul]; abel),stuck F h a b d hab hbd had,add_neg_cancel]
lemma tacit : Commute (clip (F (plane a b)) (F (plane c d))) (F (plane a b)):=by
     let Q:=clip (F (plane a b)) (F (plane c d)); let X:= F (plane a c); let Y:= F (plane c b)
     have hx:Commute Q X:=by
           have hp:= stunt F h b a c d hab.symm hbc hbd hac had hcd
           rw [swapπ b a,map_neg, show ∀ u v:Module.End ℂ V,clip (-u) v= -clip u v from (fun u v=>by unfold clip; rw [neg_mul,mul_neg]; abel)] at hp
           have hv:= hp.neg_left; rw[neg_neg] at hv; exact hv
     have hy:Commute Q Y:=by unfold Y; rw [swapπ c b,map_neg]; exact (stunt F h a b c d hab hac had hbc hbd hcd).neg_right
     have ht:= (hx.mul_right hy).sub_right (hy.mul_right hx); change Commute Q (clip X Y) at ht; rwa [show clip X Y= _ from stuck F h a c b hac hbc.symm hab] at ht
omit hab hac had hbc hbd hcd
variable (Hc: ∀ u v:Axis,Clear (F (plane u v)))
include Hc
lemma both : clip (F (plane a b)) (F (plane c d))= F (bracket (plane a b) (plane c d)):=by
    by_cases hΩ:∃ i:Axis,a≠i∧b≠i∧c≠i∧d≠i
    · obtain ⟨i,ha,hb,hc,hd⟩:=hΩ; exact h a b c d i ha hb hc hd
    have hall:a≠b∧a≠c∧a≠d∧b≠c∧b≠d∧c≠d:=(show ∀ a b c d:Axis, (¬∃ i:Axis,a≠i∧b≠i∧c≠i∧d≠i)→a≠b∧a≠c∧a≠d∧b≠c∧b≠d∧c≠d by decide) a b c d hΩ
    obtain ⟨ha,he,hc,hz,hd,hy⟩:= hall; rw[vows _ _ (Hc a b) (tacit F h _ _ _ _ ha he hc hz hd hy).symm,bracket_planes]; simp [hz,he,hc,hd]
-- extend, avoid instance issues ℝ (Module End) from actual levels, use explicit Real-linear bridge to comp.
omit Hc h
section
local instance:Fintype Axis:=inferInstance
lemma u_addΛ(u v p:Ortho.Skew): bracket (u+v) p= bracket u p+bracket v p:=Subtype.ext (by simp [bracket, add_mul,mul_add]; abel)
lemma u_sΛ(u v:Ortho.Skew)(r:ℝ): bracket (r • u) v= r • bracket u v:=Subtype.ext (by simp [bracket, smul_sub])
lemma revΛ(u v:Ortho.Skew): bracket u v= -bracket v u:=Subtype.ext (by simp [bracket])
include Hc h
variable (hσ: ∀ r:ℝ,∀ u:Ortho.Skew,F (r • u)=(r:ℂ) • F u)
include hσ
lemma palms (u v:Ortho.Skew) : clip (F u) (F v)= F (bracket u v):=by
     let Sq(p:Ortho.Skew): Submodule ℝ Ortho.Skew := {
         carrier:={x|clip (F x) (F p)=F (bracket x p)}
         zero_mem':=by change clip (F 0) (F p)= F (bracket 0 p); rw [show bracket 0 p=0 from Subtype.ext (by simp [bracket])]; simp [clip]
         add_mem':=by intro a b (he:clip (F a) (F p)=_) (hi:clip (F b) (F p)=_); change clip (F (a+b)) (F p)= _; rw[map_add,u_addΛ,map_add,←he,←hi]; unfold clip; rw [add_mul,mul_add]; abel
         smul_mem':=by intro a x (he:clip (F x) (F p)=_); change clip (F (a • x)) (F p)= _; rw[hσ,u_sΛ,hσ,← he]; unfold clip; rw [smul_mul_assoc,mul_smul_comm,smul_sub] }
     have he(p:Ortho.Skew)(hp:∀ a b:Axis,plane a b∈ Sq p): (⊤:Submodule ℝ Ortho.Skew) ≤ Sq p:=by rw[← Spin.spans]; apply Submodule.span_le.mpr; rintro v ⟨i,rfl⟩; exact hp i.1 i.2
     have hv:⊤≤Sq v:= he v (fun a b=>by
           have ht:=he (plane a b) (fun c d=> both F h c d a b Hc) (show v∈(⊤:Submodule ℝ Ortho.Skew) from Submodule.mem_top); change clip (F v) (F (plane a b))= _ at ht; change clip _ _= _; rw [clipneg,ht]; rw [revΛ v,map_neg,neg_neg])
     exact hv (show u∈ (⊤:Submodule ℝ Ortho.Skew) from Submodule.mem_top)
end
end YM.Mako
#print axioms YM.Mako.tacit
#print axioms YM.Mako.palms
