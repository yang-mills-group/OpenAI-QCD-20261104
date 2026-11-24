import YM.QCD.Fold.Peel
/-! # anti-periodic Loom licence lifts to odd mesh. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Folding
open Function Lattice Wilson Lat Flume Orbit Run Fork Kit Cost Finset Relation
open PhysicalNext.Repeat.Deck Push.Local Further.PhysicalPeriodLimitF933 Macrame Shingle
open Bay Strut Sway Revolve Quarry
open RG
open scoped Classical Matrix Matrix.Norms.L2Operator BigOperators
variable {c C f F:Side}{D b B:ℕ}{G:Ratio C F}{Q:Ratio c f}{v:Strut F}{u:Strut f}
variable (M:Window f F D) {d:Site F→ℂ}
def aims (v:Strut F)(u:Strut f):Prop:= v.1=u.1 ∧ M.cut ∘ act v=act u ∘ M.cut
lemma pegs (hh:f.val∣F.val)(he:M.cut=(⇑(splitter hh)))(H:v.1=u.1)(hv:M.cut v.2=u.2): aims M v u:=by
   refine ⟨H,funext fun i=>?_⟩; change M.cut (v.1.act i+v.2)=u.1.act (M.cut i)+u.2; rw [← hv,he,map_add, usual, H]
lemma belt (hv : Quaint M d)(ha:aims M v u)(t:Spike){k:Site f→ℂ}(hk:Warrant u k t):∃ q:Site F→ℂ,Warrant v q t ∧∀ i,k (M.cut i)*d i=q i*d (act v i):=by
   let e i:=k (M.cut i)*d i*d (act v i); have hh i:d i*d i=1:=by rcases hv.sign i with h|h <;>rw[h]<;>simp
   have he i:e i*d (act v i)=k (M.cut i)*d i:=by unfold e; rw [mul_assoc,hh,mul_one]
   have ht := ha.1; have hi i:M.cut (act v i)=act u (M.cut i):=congr_fun ha.2 i
   refine ⟨e, ⟨⟨?_,?_⟩, show Swing v.1 t from ht.symm ▸ hk.2⟩,fun i=>(he i).symm⟩
   · intro x; unfold e; rcases hv.sign x with h|h <;>rcases hv.sign (act v x) with b|b <;> rcases hk.1.sign (M.cut x) with c|c<;>rw [c,h,b]<;>simp
   intro i x; let a:= posDir i; let b:= x+step i
   let p:= a.rotate v.1
   have hf: act v b=act v x + p.vec:=affine_add v.1 v.2 x a
   have hG:= hv.lift (act v x) p -- check order
   apply mul_right_cancel₀ (show d (act v b)≠0 from (by intro h; have hq:=hh (act v b); rw [h,zero_mul] at hq; exact zero_ne_one hq))
   rw [mul_assoc, he b,mul_assoc (e x),show d (act v b)=d (act v x+p.vec) from congr_arg d hf]
   have hv' : Lat.seam 0 x i*d b=d x*Lat.seam 0 (M.cut x) i:=hv.lift x a
   change Lat.seam 0 x i * (k (M.cut b)*d b)= e x * (glint 0 (act v x) p*d (act v x+p.vec)); rw [hG, ← mul_assoc (e x),he]
   rw [show Lat.seam 0 x i * (k (M.cut b)*d b)= k (M.cut b)*(Lat.seam 0 x i*d b) from (by ring),hv', show M.cut b=M.cut x+step i from M.step_up .., hi]; unfold p; rw [ht]; have he':= hk.1.reflects i (M.cut x)
   calc
     _ = d x* (Lat.seam 0 (M.cut x) i*k (M.cut x+step i)):=by ring
     _ = _:=by rw [he']; change _= k _* d x*glint 0 (affine u.1 u.2 (M.cut x)) (a.rotate u.1); unfold a; ring
end YM.QCD.Folding
