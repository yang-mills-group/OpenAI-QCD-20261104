import YM.QCD.Pearl.Delta

/-! # path first contacts and seagulls, before Fourier -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Pearl
open Lattice Wilson Function Finset Metric Lat Rudder Kit NormedSpace RG
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology ContDiff
variable {n : Side} {E F D : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup D] [NormedSpace ℂ D]
variable (C : su.Color)
lemma dig_plain [FiniteDimensional ℂ F] [FiniteDimensional ℂ D] (g : F→ D) (h:E→L[ℂ] F) (u v x:E) (hg:Differentiable ℂ g): dig u v (g ∘ h) x=dig (h u) (h v) g (h x):=by
  unfold dig; rw [show dew v _=dew (h v) g ∘ h from funext fun y=>by rw [dew_chain (h.differentiableAt (x:=y)) (hg _),dewp]; rfl];
  -- needs hf analytic
  haveI := FiniteDimensional.complete ℂ D
  rw [dew_chain h.differentiableAt (voiced _ (PolyDisc.finiteD g (Filter.Eventually.of_forall hg))),dewp]
lemma dig_home (g : F→L[ℂ] D) [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (f:E→F) (u v x:E) (h:Differentiable ℂ f):dig u v (g ∘ f) x=g (dig u v f x):=by
  letI:=FiniteDimensional.complete ℂ F
  unfold dig; rw [show dew v _=g ∘ dew v f from funext fun y=>by rw [dew_chain (h y) g.differentiableAt,dewp]; rfl]
  rw [dew_chain (voiced v (PolyDisc.finiteD f (Filter.Eventually.of_forall h))) g.differentiableAt,dewp g]

lemma steam (x z:ℂ): dew z (lunar C) x= z • (lunar C x*echo C) := by
  -- norm instances
  have he : deriv (lunar C) x= lunar C x * echo C:=(shineD ..).deriv
  rw [dew_ℂ, he]
lemma lunar_dig (u v:ℂ) : dig u v (lunar C) 0=(v*u) • (echo C*echo C):=by
  let a:=echo C
  unfold dig; rw [funext (fun x=>steam C x v)]
  have ht : DifferentiableAt ℂ (fun x : ℂ=> lunar C x*a) 0 := (liveD C _).fun_mul (differentiableAt_const _)
  rw [dew_s (differentiableAt_const (x:=(0:ℂ)) v) ht, dew_mul (liveD C _) (differentiableAt_const _),steam,lunar_nil,dew_zero]
  rw [dew_zero v]; simp [a,Matrix.smul_mul,smul_smul]
lemma bore_dig (i:su.ColorIndex)(u v:ℂ):dig u v (bore C i) 0=0:=by
  let f := bore C i
  let N: ℂ→L[ℂ] ℂ:= -ContinuousLinearMap.id ℂ ℂ
  have ht := dig_plain f N u v 0 (bore_diff C i)
  rw [show f ∘ N= - f from funext fun x=>bore_odd ..] at ht
  have he (g:ℂ→ℂ)(x u:ℂ): dew u (-g) x= -dew u g x:=by unfold dew; rw [fderiv_neg]; rfl
  have hh := PolyDisc.finiteD f (x:=0) (Filter.Eventually.of_forall (bore_diff C i)); rw [dig_two _ _ hh] -- f defin
  rw [show dig u v (-f) 0= - dig u v f 0 from by unfold dig; rw [show dew v (-f)=-dew v f from funext fun x=>he f x _]; exact he .., map_zero N, show N u= -u from rfl,show N v= -v from rfl,dig_two _ _ hh,dig_two _ _ hh,map_neg,map_neg,_root_.neg_apply,neg_neg] at ht; apply neg_eq_self.mp ht

lemma jot {I:Type*} (s:Finset I) [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (f:I→ E→F) (h:∀ i∈s,Differentiable ℂ (f i))(u v x:E): dew u (fun z=>∑ i∈s,f i z) x=∑ i∈s,dew u (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty=> simp only [sum_empty]; exact dew_zero _ _ _
  | insert a s ha ih=>
    have ht:=fun i (hi:i∈s)=> h i (mem_insert_of_mem hi); simp_rw [sum_insert ha];
    change dew u (f a+(fun z=>∑ i∈s,f i z)) x=_
    rw [dew_plus (h a (mem_insert_self ..) x) (DifferentiableAt.fun_sum (fun i hi=> ht i hi x)),ih ht]
lemma jip {I:Type*} (s:Finset I) [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (f:I→ E→F) (h:∀ i∈s,Differentiable ℂ (f i))(u v x:E): dig u v (fun z=>∑ i∈s,f i z) x=∑ i∈s,dig u v (f i) x:=by
  haveI:=FiniteDimensional.complete ℂ F; unfold dig; rw [funext (fun x=> jot s f h v u x)]; exact jot s (fun i=> dew v (f i)) (fun i hi x=> voiced v (PolyDisc.finiteD _ (Filter.Eventually.of_forall (h i hi)))) u v x
lemma shifts (i: Site n) (w:Walk):∃ L:Weather n→L[ℂ] ℂ,∀ Z,L Z=bill Z i w:= by
  induction w generalizing i with
  | nil=> exact ⟨0,fun Z=>rfl⟩
  | cons a w ih=>
    obtain ⟨V,hV⟩:= ih (i+a.vec); let X:Weather n →L[ℂ] ℂ:= ContinuousLinearMap.proj (a.used i)
    refine ⟨(if a.neg then -X else X)+V,fun Z=>?_⟩
    rw [ContinuousLinearMap.add_apply,bill,hV]; split <;> rfl
lemma bill0 (x: Site n)(w):bill (0:Weather n) x w=0:=by obtain ⟨L,h⟩:=shifts x w; rw [← h,map_zero]
lemma drip_gate (F: Weather n → Site n→Bundle)(h:Differentiable ℂ F)(u v:Weather n):
    dew u (fun z=> rides (Equiv.refl _) (F z)) v=rides (Equiv.refl _) fun i=> dew u (fun z=> F z i) v:=by
  let R := gate n
  rw [show (fun z=> rides _ (F z))=R ∘ F from rfl,dew_chain (h v) R.differentiableAt,dewp]; unfold dew;
  change rides _ _=_; congr 1; funext x
  let T: (Site n→Bundle)→L[ℂ] Bundle:=ContinuousLinearMap.proj x
  exact (by rw [show fderiv ℂ (fun z=>F z x) v u=dew u (T ∘ F) v from rfl,dew_chain (h v) T.differentiableAt,dewp]; rfl)
lemma dive_gate (F: Weather n → Site n→Bundle)(h:Differentiable ℂ F)(u v x:Weather n): dig u v (fun z=> rides (Equiv.refl _) (F z)) x= rides (Equiv.refl _) fun i=> dig u v (fun z=> F z i) x:= by
  change dig u v (gate n ∘ F) x= _; rw [dig_home _ _ _ _ _ h]; change rides _ _=_; congr 1; funext i; exact (dig_home (ContinuousLinearMap.proj i) F u v x h).symm
lemma amass0 (t : Site n) w: amass C t w 0=routeM t 1 w:= by unfold amass; simp only [bill0,lunar_nil,show TouchL 1=1 from touch_one,ridden,one_mul]
def pump (u:Weather n) (w) (Z:Bundle):= rides (Equiv.refl _) (fun i:Site n=> bill u i w • Z)

def screen (w:Walk)(U:Weather n):= fun x: Site n=> TouchL (lunar C (bill U x w))
lemma radar w :Differentiable ℂ (screen (n:=n) C w):=by refine differentiable_pi.mpr fun i=>TouchL.differentiable.comp ((liveD C).comp (billD _ w))
lemma sight_dew (w:Walk)(u : Weather n)(x:Site n): dew u (fun Z=>screen C w Z x) 0=bill u x w • touch (echo C):=by
  obtain ⟨L,h⟩:=shifts x w
  have H : dew (L u) (TouchL ∘ lunar C) 0= (L u) • TouchL (echo C):=by rw [dew_chain (liveD C _) TouchL.differentiableAt, dewp,steam, map_smul,lunar_nil,one_mul]
  rw [show (fun Z=>screen C w Z x)=(TouchL ∘ lunar C) ∘ L from funext fun i=> by simp only [Function.comp_apply,h,screen],dew_chain L.differentiableAt (TouchL.differentiable.comp (liveD C) _),dewp,map_zero,H,h]; rfl
lemma sight_dig (w:Walk)(u v: Weather n)(x:Site n): dig u v (fun Z=>screen C w Z x) 0=(bill v x w*bill u x w) • touch (echo C*echo C):=by
  obtain ⟨L,h⟩:=shifts x w; rw [show (fun Z=>screen C w Z x)=(TouchL ∘ lunar C) ∘ L from funext fun i=> by simp only [Function.comp_apply,h,screen],dig_plain _ L _ _ _ (TouchL.differentiable.comp (liveD C)),map_zero,dig_home _ _ _ _ _ (liveD C),lunar_dig,map_smul,h,h]; rfl
lemma dew_mul_const' [FiniteDimensional ℂ E] {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [FiniteDimensional ℂ R] {f:E→R}(h:Differentiable ℂ f)(u x:E) (M:R): dew u (fun z=>f z*M) x=dew u f x*M:=by rw [dew_mul (h x) (differentiableAt_const _),dew_zero,mul_zero,zero_add]
lemma dig_mul_const' [FiniteDimensional ℂ E]{R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [FiniteDimensional ℂ R]{f:E→R}(h:Differentiable ℂ f)(u v x:E)(M:R): dig u v (fun z=> f z*M) x=dig u v f x*M := by unfold dig; rw [funext (fun x=>dew_mul_const' h v x M)]; haveI:=FiniteDimensional.complete ℂ R; exact dew_mul_const' (fun x=>voiced v (PolyDisc.finiteD _ (Filter.Eventually.of_forall h))) _ _ _
lemma amass_dew (u:Weather n)(w t): dew u (amass C t w) 0=pump u w (touch (echo C))*routeM t 1 w:=by
  change dew u (fun Z=> (gate n ∘ screen C w) Z *routeM t 1 w) 0=_; rw [dew_mul_const' ((gate n).differentiable.comp (radar C w))]; congr 1; change dew u (fun Z=> rides _ (screen C w Z)) 0=_; rw [drip_gate _ (radar C w)]; simp_rw [funext (sight_dew C w u)]; rfl
lemma amass_dig (u v:Weather n)(w t): dig u v (amass C t w) 0=rides (Equiv.refl _) (fun x:Site n=> (bill v x w*bill u x w) • touch (echo C*echo C))*routeM t 1 w:=by change dig u v (fun Z=> (gate n ∘ screen C w) Z *routeM t 1 w) 0=_; rw [dig_mul_const' ((gate n).differentiable.comp (radar C w))]; congr 1; change dig u v (fun Z=> rides _ (screen C w Z)) 0=_; rw [dive_gate _ (radar C w)]; congr 1; funext i; exact sight_dig ..
end YM.QCD.Pearl
