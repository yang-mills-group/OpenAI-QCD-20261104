import YM.QCD.Bay.Wharf
/-! # rotate Land-letters. Warrant picks. Varies by same phase on both letter indices. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Bay
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.Local
open Jets Sun Revolve Garden Strut LeafM
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {D V:Type*}[Fintype D][Fintype V][DecidableEq D][DecidableEq V]{f c: Side}{g:D→ Site f}{h:V→Site f}{δ A t a:ℝ}{m:ℕ}
variable {s:Ratio c f}{P: Therm D s g}{Q:Therm V s h}{G:Grid f→ArrayL D V}{X:Land f D V}{Y:Pays f D V}
namespace Strut
variable {v: Strut f}{a b: Site f→ℂ} {S U:Spike}
lemma faith (h:Warrant v a S)(ht:Warrant v b U):∃ c:ℂ,star c*c=1 ∧∀ x, lightP v S a x=c • lightP v U b x:=by
  obtain ⟨c,u,he,hJ,hc,hA,H⟩:= unique_scalar h ht; refine ⟨c*star u,?_,fun i=>?_⟩
  · rw [star_mul,hJ,star_star]; calc _= star u*u*(c*c):=by ring
                                      _= _ := by rw [hc,he,one_mul]
  unfold lightP; rw [H,hA,star_smul,show wave (star u • star U) = star u • wave (star U) from Matrix.smul_kronecker ..,smul_smul,smul_smul,mul_right_comm]
lemma basket {D:Pulse f→Bundle}{x y}(h:Warrant v a S)(ht:Warrant v b U): tips v a S x y D=tips v b U x y D:=by
  obtain ⟨c,hc,H⟩:= faith h ht; funext X; unfold tips; rw [H,H,star_smul]; simp only [Matrix.mul_smul,Matrix.smul_mul,smul_smul,mul_comm c, hc,one_smul]
lemma passage {v u: Strut f}(x y)(Z:Pulse f→Bundle)(s t:Site f→ℂ)(A B:Spike)(U:Grid f): tips (pod u v) (coin v s t) (A*B) x y Z (settled U) = tips u s A (act v x) (act v y) (tips v t B x y Z) (settled U) :=by
    simp only [tips,still,posture,star_mul,skying,Matrix.mul_assoc]
end Strut

-- W.S.P > *
lemma rush (s: Ratio c f)(u v:Strut c) : raiseS s (pod u v)=(raiseS s v).trans (raiseS s u):=by
  ext1 i; unfold raiseS; rw [ups u v s,podA]; simp -- check

def ink (v: Strut f):= (secure v).choose
def sat (v: Strut f):= (secure v).choose_spec.choose
lemma assured (v:Strut f):Warrant v (ink v) (sat v):=(secure v).choose_spec.choose_spec

lemma brightD {l:Site f→ℂ}{T:Spike}{u:Strut c}(hv:Warrant (raise s u) l T)(F:Land f D V)(p i j): driveD s P Q u T l F p i j= driveD s P Q u (sat (raise s u)) (ink (raise s u)) F p i j :=basket hv (assured _)

lemma courier (Vf: Grid f)(s:Ratio c f)(P:Therm D s g)(Q:Therm V s h)(u v:Strut c)(T A : Spike)(p t:Site f→ℂ)(hp: Warrant (raise s u) p T)(ht:Warrant (raise s v) t A)(i j k)(F:Land f D V):
    driveD s P Q u T p (driveD s P Q v A t F) i j k (settled Vf)= driveD s P Q (pod u v) (sat (raise s (pod u v))) (ink (raise s (pod u v))) F i j k (settled Vf):=by
    obtain ⟨x,rfl⟩:= (P.shiftP (pod u v)).surjective i; obtain ⟨y,rfl⟩:= (Q.shiftP (pod u v)).surjective j; obtain ⟨k,rfl⟩:=(raiseS s (pod u v)).surjective k
    have he: raise s (pod u v)=pod (raise s u) (raise s v):=ups ..
    have hc: Warrant (raise s (pod u v)) (coin (raise s v) p t) (T*A):= he.symm ▸ comb hp ht
    rw [← brightD hc]; unfold driveD; simp only [Equiv.symm_apply_apply]; rw [P.steps,Q.steps,rush]; simp only [Equiv.trans_apply,Equiv.symm_apply_apply]; rw [he,P.bills,Q.bills, ← passage] -- need `P.bills`

end YM.QCD.Bay
