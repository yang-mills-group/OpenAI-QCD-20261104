import YM.Siro.Flow
import YM.Ward.Motion
set_option maxHeartbeats 420000
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Siro
open Complex
open Set Function Filter Analysis
open Fields (SimpleK homogeneous located slab)
open OS (Cross)
open Ward (inc)
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace ContDiff
variable {F : Fields} {a b : Axis} {S:F.Kernel}(V:Chamber S a)
-- spot on RHS avoids all token permutations in Gram extension
noncomputable def host (w:F.W)(x:E4)(hx:0<x a): Future F a:= ⟨[(x,w)],(locations (F:=F)).mpr (by simp),by intro p hp; rw[List.mem_singleton] at hp; subst p; exact hx⟩
def spotR (p:F.W)(x:E4): V.GNS.H:= if h:0<x a then V.GNS.plant (host p x h) else 0
@[simp]lemma stamp (x:E4)(h:0<x a)(p:F.W): spotR V p x= V.GNS.plant (host p x h):= dif_pos h
lemma slides (s : ℝ≥0) (t : F.W) (x : E4) (hx : 0<x a) : spotR V t (inc a x s)=V.flow.E s (spotR V t x) := by
     rw [stamp V _ hx,← V.atBirth, stamp V _ (by simp [inc]; positivity)]; rfl
lemma rests (s : Cross a) (t : F.W) (x : E4) (hx : 0<x a) : spotR V t (x+s.val)=V.flow.U s (spotR V t x) := by
     rw [stamp V _ hx,← V.across, stamp V _ (by simp [hx, show s.val a=0 from s.property])]; rfl
lemma light {x:E4}(p:F.W)(hb:b≠a)(hx:0<x a): Continuous fun t:ℝ=> spotR V p (inc b x t):=by
      let f(t:ℝ):Cross a:=⟨t • basis b, show _ from by change (t • basis b) a=0; simp[Ne.symm hb]⟩; have hf:Continuous f:=(continuous_id.smul (continuous_const (y:=basis b))).subtype_mk _; exact ((V.flow.continuousU (spotR V p x)).comp hf).congr (fun t=> (rests V (f t) p x hx).symm)
-- absolute points vector
noncomputable def post (w: Cluster F) (x:E4) : Points (w.length+1):= points (Fin.append (positions w).ofLp (![x]))
noncomputable abbrev pureT(w:Cluster F)(v:F.W): Fin (w.length+1)→ F.W:= Fin.append (tokens w) (![v])
lemma plays(w:Cluster F)(x:E4)(u:F.W): w++[(x,u)]=realize (F:=F) (pureT w u) (post w x):=by
      have he:= placements w [(x,u)] 0; rw [rest] at he; let v:= post w x; have hg: composite w [(x,u)] 0=v:=by
                apply PiLp.ext; intro i; refine Fin.addCases (fun i=> ?_) (fun i=>?_) (show Fin (w.length+1) from i)
                · change (points (Fin.append (positions w).ofLp _)) (Fin.castAdd 1 i)= _; simp [v,post]
                fin_cases i; simp only[composite,post,v,points_apply]; change (Fin.append (positions w).ofLp (Points.across 0 (positions [(x,u)])).ofLp _) =_; rw [Fin.append_right,Fin.append_right,Points.across_coord,add_zero]; rfl
      rw [hg] at he; refine he.trans ?_; congr 1; funext i; refine Fin.addCases (fun i=>?_) (fun i=>?_) i
      · simp [pureT]
      unfold pureT; rw [Fin.append_right,Fin.append_right]; change Fin 1 at i; fin_cases i; rfl
lemma post_d (w:Cluster F)(x:E4)(b:Axis)(s:ℝ): HasDerivAt (fun t=> post w (inc b x t)) (Points.direction (Fin.natAdd w.length (0:Fin 1)) b) s:=by
      let u:= Fin.natAdd w.length (0:Fin 1); rw [show (fun t=> post w (inc b x t))=Ward.cast (post w x) u b from ?_]; apply Ward.moves; funext t; apply PiLp.ext; intro i; refine Fin.addCases ?_ ?_ i
      · intro j; rw [Ward.near _ _ _ (show Fin.castAdd 1 j≠ u from by intro h; have he:= congr_arg Fin.val h; simp only [u,Fin.val_natAdd,Fin.val_castAdd] at he; omega)]; simp[post]
      intro j; fin_cases j; change post w _ u=Ward.cast _ u _ _ u; rw [Ward.atCast]; simp [post,u]
lemma link (q:Future F a)(p:F.W)(x:E4)(h:0<x a):inner ℂ (V.GNS.plant q) (spotR V p x)= S _ (post (reflect (F:=F) q.val a) x) (pureT (reflect q.val a) p) :=by
     rw [stamp V _ h,V.GNS.measure]; change Fields.pointMoment _ ((reflect q.val a)++[(x,p)])=_; rw[plays,readAt]
lemma hot (q:Future F a)(x:E4)(h:0<x a): post (reflect q.val a) x∈conf _:=by
     have hx:= twoSides q.property (host (F:=F) 0 x h).property; change Fields.distinct (F:=F) (reflect q.val a++[(x,0)]) at hx; rw[plays,realized] at hx; exact hx
lemma woody(w:Cluster F)(p q:F.W): update (pureT w p) (Fin.natAdd w.length (0:Fin 1)) q=pureT w q:=by
     funext i; refine Fin.addCases ?_ ?_ i; · intro j; rw [update_of_ne (show _≠_ from ?_)]; simp[pureT]; intro h; have he:=congr_arg Fin.val h; simp only [Fin.val_natAdd,Fin.val_castAdd] at he; omega
     intro j; fin_cases j; simp [pureT]
variable (H: SimpleK S) {x:E4}(p:F.W)(j:b≠a)(hp:0<x a)
include H hp j
lemma responds(t:ℝ):HasDerivAt (fun z=> spotR V p (inc b x z)) (spotR V (F.partialD b p) (inc b x t)) t:=by
     apply represents V.GNS (fun z=> spotR V p (inc b x z)) (fun z=> spotR V (F.partialD b p) (inc b x z)) (light V _ j hp); intro q y
     simp_rw[link V q p _ (Ward.step hp _ j)]; rw [link V q (F.partialD b p) _ (Ward.step hp _ j)]
     let R:= reflect q.val a; let w:=pureT R p; let Y:= post R (inc b x y); have hY:Y∈conf _:=hot q _ (Ward.step hp y j)
     let f:=fun u:Points (R.length+1)=> S _ u w; have ht:DifferentiableAt ℝ f Y := ((H.smooth _ w).differentiableOn (by simp)).differentiableAt ((conf_open _).mem_nhds hY); apply (ht.hasFDerivAt.comp_hasDerivAt y (post_d R x b y)).congr_deriv
     change D _ f Y=_; unfold f; rw[H.derivatives _ w _ _ hY]; change S _ _ (update (pureT R _) _ (F.partialD b (pureT R p _)))=_; simp[woody]; rfl -- need replace
lemma shines : ContDiff ℝ ∞ fun z=> spotR V p (inc b x z):=by
     apply contDiff_infty.mpr; intro n; induction n generalizing p with
     | zero=> exact contDiff_zero.mpr (light V p j hp)
     | succ n ih=>
           push_cast; apply contDiff_succ_iff_deriv.mpr; have he:= responds V H p j hp; refine ⟨fun x=>(he x).differentiableAt,fun hz=>?_,?_⟩; simp at hz; rw[funext (fun i=>(he i).deriv)]; exact ih _
-- adapted straight from Ward.Plants
omit H hp j
lemma advancing (p : F.W) (x : E4) (u : ℝ) (hx : 0 < inc a x u a) :
    AnalyticAt ℝ (fun t => spotR V p (inc a x t)) u := by
  let t := u-inc a x u a/2
  have ht : t<u := by unfold t; linarith
  let y := inc a x t
  have hy : 0 < y a := by dsimp only [y,t]; simp only [inc,PiLp.add_apply,PiLp.smul_apply,basis_eq,if_true,smul_eq_mul,mul_one] at *;linarith
  let r := spotR V p y
  let k (i : ℝ) := ((i-t:ℝ):ℂ)
  let F (s : ℝ) := V.flow.F (k s) r
  have he := V.flow.localHeat (k u) (show _ from sub_pos.mpr ht)
  have hp : ContDiffAt ℝ ω (fun z : ℂ => V.flow.F z) (k u) := he.contDiffAt.restrict_scalars ℝ
  have hh : AnalyticAt ℝ F u :=
    ( (ContinuousLinearMap.apply ℂ V.GNS.H.space r).restrictScalars ℝ |>.analyticAt _ ).comp
      (hp.analyticAt.comp ((Complex.ofRealCLM.analyticAt _).comp (analyticAt_id.sub analyticAt_const)))
  apply hh.congr
  filter_upwards [lt_mem_nhds ht] with i hi
  let z : ℝ≥0 := ⟨i-t,(sub_pos.mpr hi).le⟩
  change V.flow.F (OS.Semigroup.duration z) r = _
  rw [V.flow.roots_heat (t := z) (show (0:ℝ) < z from sub_pos.mpr hi),← slides V z p y hy]
  congr 1
  change x + t • _ + (i-t) • _ = _
  rw [add_assoc, ← add_smul, add_sub_cancel]
end YM.Massive.Siro
#print axioms YM.Massive.Siro.advancing
#print axioms YM.Massive.Siro.shines
