import YM.Gust.Lift
import YM.Push.STRESS_FLUX.Solve
set_option maxHeartbeats 480000
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Gust
open Analysis Function Set Filter MeasureTheory Table Work.A05 Tarn Tarn.Choir
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {Q: Choir}{C: Sequence}{P:Calibration C}{d m n:ℕ}{x:Points (n+1)}{χ:E4→ℝ}{V:E4→E4}
variable (S: Axis→Axis→ Q.W) (hq:Q.Domestic) (hx:x∈conf _) (hw:Window x χ)
variable (hv:∀ b:Axis, Continuous fun y:E4=> V y b) (p:Fin n→ Q.W)
def bladeD (y:E4)(a b:Axis): Q.W→ₗ[ℂ] ℂ:= (Q.total _ (Points.cons y x)).toLinearMap (Fin.cons (S a b) (Fin.cons 0 p)) (Fin.succ 0)
lemma bladeT(y:E4)(a b:Axis)(u:Q.W): bladeD (x:=x) S p y a b u = Q.total _ (Points.cons y x) (Fin.cons (S a b) (Fin.cons u p)):=by
     refine congr_arg (Q.total _ _) ?_; ext1 i; induction i using Fin.cases with
     | zero=> simp
     | succ i=>
                 refine Fin.cases ?_ (fun j=> ?_) i
                 · simp
                 rw [update_of_ne (Fin.succ_injective _|>.ne (Fin.succ_ne_zero _))]; rfl
include hq hx hw hv
lemma flux_add(u v:Q.W):fluxG S χ V x (Fin.cons (u+v) p)=fluxG S χ V x (Fin.cons u p) + fluxG S χ V x (Fin.cons v p):=by
     have he a b y : termG S χ V x (Fin.cons (u+v) p) a b y=termG S χ V x (Fin.cons u p) a b y+ termG S χ V x (Fin.cons v p) a b y:=by simp only [termG,←bladeT,map_add,mul_add]
     have hh a b : (∫ y,termG S χ V x (Fin.cons (u+v) p) a b y)=(∫ y,termG S χ V x (Fin.cons u p) a b y)+(∫ y,termG S χ V x (Fin.cons v p) a b y):=by simp_rw [he]; exact integral_add (termG_integrable S χ V x _ hq hx hw a b (hv b)) (termG_integrable S χ V x _ hq hx hw a b (hv b))
     simp_rw [fluxG,hh,Finset.sum_add_distrib]; abel
lemma flux_by(u:Q.W)(c:ℂ):fluxG S χ V x (Fin.cons (c • u) p) = c • fluxG S χ V x (Fin.cons u p):=by
     have he a b y : termG S χ V x (Fin.cons (c • u) p) a b y=c*termG S χ V x (Fin.cons u p) a b y:=by simp only [termG,←bladeT,map_smul,smul_eq_mul,mul_left_comm]
     simp_rw [fluxG,he,integral_const_mul,smul_neg,Finset.smul_sum, smul_eq_mul]
noncomputable def legacyG (S:Axis→Axis→ Q.W)(V:E4→E4)(x:Points (n+1))(p:Fin n → Q.W)(χ:E4→ℝ)(hq:Q.Domestic)(hx:x∈conf _)(hw:Window x χ)(hv:∀ b:Axis,Continuous fun y:E4=> V y b):Q.W→ₗ[ℂ]ℂ where
   toFun u:= fluxG S χ V x (Fin.cons u p)
   map_add':=flux_add S hq hx hw hv p
   map_smul' c x := flux_by S hq hx hw hv p x c
omit hx hw hv
variable (B:Q.W) (A:Q.W)
abbrev Captures (K:Choir)(J:Axis→Axis→ K.W)(V:E4→E4)(x y:K.W):Prop:=∀ n:ℕ,∀ s:Points (n+1),∀ c:E4→ℝ,s∈conf _ → Window s c → ∀ v:Fin n→ K.W, about J c V s (Fin.cons x v)=headG v s y
variable (T:∃ J:Axis→Axis→ UV.Label 8, ∀ a b, Q.focus none 8 (J a b)= S a b)(hT:Safe Q S)
variable {F:Pollens P Q}(hP:Foil P Q F) (hE:∀ a b,F.parity (S a b)= S a b)(hg:StressFlux.Annular.Motion 1 V) (hO:Orb P Q d F) {β e:ℝ}(hp:C.Path β e)
open UV Poised Plans Plans.Stamp Intag Intag.Vale Needle Patria.Hub
open Patria Patria.Depth
variable (G:∀ d,Cottage P d) (hs:Sway C.S) 
include T hp hg hT hO hE G hs hP -- hQ ?
lemma exhaust (u:Label d)(b:Bool)(hh:u≠0)(ht:moored u.val b):∃ A:Label d,Captures Q S V (Q.focus none d u) (Q.focus none d A):=by
   choose ψ hψ using fun s:Patrol P=> Work.A01.exists_window (xP s) s.ok
   let J(s:Patrol P):=(visionR Q s).comp (Q.focus none d); let X:=Q.focus none d u; let W(s):=about S (ψ s) V (xP s) (Fin.cons X (wordsP Q s))
   obtain ⟨A,hA⟩:= StressFlux.Annular.total J W (fun n s c h=> floated S hq T hT hE hg s c hO hp G hs u b hh ht _ (fun i=> hψ (s i)) (fun v=>by simp_rw [← who]; exact h v))
   let X':= Q.focus none d A
   have hC (s:Patrol P)(χ)(hw:Window (xP s) χ):about S χ V (xP s) (Fin.cons X (wordsP Q s))=headG (wordsP Q s) (xP s) X':=by
        refine Eq.trans (?_ : _= W s) (hA s).symm; simp only [W,about,hereP,sub_zero]; exact independent hq hT _ hg.smooth hg.rigid s.ok hw (hψ _) _
   refine ⟨A,fun n x χ hx hw p=>?_⟩; let z:= -(x 0); let W:= Points.across z x; have hh:W ∈conf _:= Points.across_in z hx; have he: points (Fin.cons 0 (Points.tail W).ofLp) = W:=by ext1 i; cases i using Fin.cases <;> simp [Points.tail,W,z]
   choose! d X h' using fun i:Fin n=> (show ∃ d,∃ x:Label d,Q.focus none d x=p i from (hq.absorbs (p i))) -- absorbs membership defin?
   let r:Patrol P:=⟨n,d,X,(Points.tail W).ofLp,he.symm ▸ hh⟩
   let c:=fun y=> χ (y-z); have hw':Window (xP r) c:=by rw [show xP r=W from he]; exact StressFlux.Annular.shifted_window z hw
   have ht:=hC r c hw'; have hh: wordsP Q r=p:=funext h'; change about S c V (xP r) (Fin.cons _ (wordsP Q r))=headG (wordsP Q r) (xP r) _ at ht; rw [hh,show xP r=W from he] at ht; unfold c W at ht; rw [heads,moved S V z hP hx hw,hP.translation _ x hx z _] at ht; exact ht.trans (heads ..).symm
omit T hp hg hT hO hE hP G hs
variable (V)
include hv
lemma cap_scale (h: Captures Q S V B A)(c:ℂ):Captures Q S V (c • B) (c • A):=by
     intro n x χ hx hw p; unfold about; rw [flux_by (V:=fun y=> V (y-x 0)) S hq hx hw (fun b=> (hv b).comp (continuous_id.sub continuous_const)) p,map_smul]; exact congr_arg _ (h n x χ hx hw p) -- about expand in h
lemma cap_zero: Captures Q S V 0 0:=by
     intro n x χ hx hw p; exact (map_zero (legacyG S _ _ p _ hq hx hw (fun b=> (hv b).comp (continuous_id.sub continuous_const)))).trans (map_zero _).symm
lemma cap_plus (h:Captures Q S V B A)(u v:Q.W)(hz:Captures Q S V u v):Captures Q S V (B+u) (A+v):=by
     intro n x χ hx hw p; unfold about; rw[flux_add (V:=fun y=> V (y-x 0)) S hq hx hw (fun b=>(hv b).comp (continuous_id.sub continuous_const)),map_add]; exact congr_arg₂ (· + ·) (h n x χ hx hw p) (hz n x χ hx hw p)
omit hv
include T hp hg hT hO hE hP G hs
lemma surge (w:Q.W)(hj:w∈Q.level d):∃ u:Q.W,u∈ Q.level d∧Captures Q S V w u:=by
   have hv(b:Axis):= (hg.smooth b).continuous
   obtain ⟨p,rfl⟩:=hj; have hp' (u:Label d)(b:Bool)(h:moored u.val b): ∃ v:Label d,Captures Q S V (Q.focus none d u) (Q.focus none d v):=by
        by_cases he:u=0; · refine ⟨0,?_⟩; rw[he,map_zero]; exact cap_zero V S hq hv -- V arg
        exact exhaust S hq T hT hP hE hg hO hp G hs u b he h -- V before changed? declared implicit when exhaust.
   let X b:= facing P.sym b p; choose U hU using fun b=> hp' (X b) b (fronting P.sym p b)
   have hh: p=X true+X false:= revelation P.sym p; exact ⟨_, (Q.level d).add_mem (show Q.focus none d (U true)∈Q.level d from ⟨_,rfl⟩) (show Q.focus none d (U false)∈Q.level d from ⟨_,rfl⟩), (Eq.trans (congr_arg (Q.focus none d) hh) (map_add (Q.focus none d) (X true) (X false))).symm ▸ cap_plus V S hq hv _ _ (hU true) _ _ (hU false) ⟩
end YM.Massive.Gust
#print axioms YM.Massive.Gust.surge
