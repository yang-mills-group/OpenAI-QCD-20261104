import YM.Iceberg.Pitch
set_option autoImplicit false
noncomputable section
namespace YM.Mako
open Set Function Filter Analysis Lattice QCD QCD.Lat
open Massive Massive.UV Massive.UV.Free Massive.Gust
open scoped Topology ContDiff BigOperators Classical Matrix Matrix.Norms.Frobenius
open Heron Iceberg Massive.Poised.Plans.Stamp
open scoped YM.Iceberg YM.Massive.Poised.Plans.Stamp
local instance (d:ℕ):NormedSpace ℝ (Label d):=NormedSpace.restrictScalars ℝ ℂ _
private lemma seed (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] : ContinuousSMul ℝ V:=inferInstance
local instance (d:ℕ) : ContinuousSMul ℝ (Label d) := by exact seed (Label d)
-- chain rule for varying linear map with weakly given derivatives
lemma darwin {V W:Type*}[NormedAddCommGroup V][NormedSpace ℂ V][FiniteDimensional ℂ V][NormedSpace ℝ V][IsScalarTower ℝ ℂ V]
    [NormedAddCommGroup W][NormedSpace ℂ W][NormedSpace ℝ W][IsScalarTower ℝ ℂ W] {F:ℝ→ V→ₗ[ℂ] W} {P:V→ₗ[ℂ] W} {g:ℝ→V}{a:ℝ}{v:V}(h:∀i:V,HasDerivAt (fun t=>F t i) (P i) a)(H:HasDerivAt g v a):HasDerivAt (fun t=> F t (g t)) (P (g a)+F a v) a:=by
     let B:=Module.finBasis ℂ V
     have hf(t:V)(p:V→ₗ[ℂ]W): p t=∑ i,B.coord i t • p (B i):=by simp_rw[←map_smul,← map_sum]; exact congr_arg p (B.sum_repr t).symm
     conv=> arg 1; ext x; rw [hf];
     rw[hf (g a),hf v]; have hg i: HasDerivAt (fun t=> B.coord i (g t)) (B.coord i v) a:= ((B.coord i).toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt a H; rw [← Finset.sum_add_distrib]; exact HasDerivAt.fun_sum fun i _=> (hg i).smul (h (B i))

def FullL(d:ℕ): EuPin →* (Label d ≃ₗ[ℂ] Label d) where
   toFun p:=putH (p,plainPicture p) d
   map_one':=LinearEquiv.ext (fun p=>Subtype.ext (carr_one p.val))
   map_mul' g h:= LinearEquiv.ext (fun p=>Subtype.ext (carr_times (g,plainPicture g) (h,plainPicture h) p.val))
variable {d:ℕ}(A:EuPin)(b:IceT)(x:Label d)
def regionL(s:Finset IceT)(A:EuPin): EuPin × PClan := (if none ∈s then A else 1,fun i=> if some i∈s then A else 1)
@[simp]lemma full_region : putH (regionL Finset.univ A) d x= FullL d A x :=by rw [show regionL Finset.univ A= (A,plainPicture A) from by unfold regionL plainPicture; simp]; rfl
@[simp]lemma chilly(s:Finset IceT) (d:ℕ):putH (regionL s 1) d=LinearEquiv.refl ℂ _:=by refine LinearEquiv.ext (fun p=>Subtype.ext ?_); change carr (regionL s 1) d p.val=p.val; rw[show regionL s 1=1 from (by apply Prod.ext<;> simp [regionL]; rfl), carr_one]
lemma hop (s:Finset IceT)(hs:b∉s): regionL (insert b s) A= sectorP b A*regionL s A:=by
    cases b with
    | none=>
       apply Prod.ext; · simp [regionL,sectorP, bPaneB,hs]
       funext i; simp [regionL,sectorP,bPaneB]
    | some i =>
       apply Prod.ext; · simp [regionL,sectorP,aPaneB]
       funext j; by_cases hi:i=j; · subst j; simp [regionL, sectorP, aPaneB,maskH,hs]
       simp [regionL,sectorP,aPaneB,maskH,hi,Ne.symm hi]
variable (Δ:Ortho.Skew)(g:ℝ→EuPin)(hg:EuPin.Path Δ g)
include hg
lemma span_d(s:Finset IceT):HasDerivAt (fun z=>putH (regionL s (g z)) d x) (∑ i∈s,Cane g Δ hg i d x) 0:=by
    induction s using Finset.induction_on with
    | empty=> simp_rw[show ∀ z:EuPin, regionL ∅ z=regionL ∅ 1 from (fun z=>by simp [regionL]),chilly]; simp; exact hasDerivAt_const ..
    | insert a s hi h =>
         let F(t:ℝ):Module.End ℂ (Label d):= (putH (sectorP a (g t)) _).toLinearMap
         let w:=fun t:ℝ=> putH (regionL s (g t)) d x; have hQ:= darwin (F:=F) (tCane g Δ hg a) (show HasDerivAt w _ 0 from h)
         rw[show w 0=x from by simp [w,hg.1],show F 0=1 from ?_] at hQ; swap
         · unfold F; rw[hg.1,show sectorP a 1=1 from (by cases a; rfl; simp only [sectorP,aPaneB,mask_one]; rfl)]
           exact LinearMap.ext (fun x=>Subtype.ext (carr_one x.val))
         rw [Finset.sum_insert hi]; apply hQ.congr_of_eventuallyEq; exact Eventually.of_forall fun z=>Subtype.ext (by dsimp only; rw[hop _ _ _ hi]; exact carr_times _ _ _)
lemma full_d:HasDerivAt (fun t=> FullL d (g t) x) (∑ i:IceT,Cane g Δ hg i d x) 0:= by simpa only [full_region] using (span_d x Δ g hg Finset.univ)
open Massive.Bridge.Spinor
omit hg
lemma printG : Continuous printS:=by
     apply Continuous.prodMk (f:=fun p=>(printS p).1) (g:=fun p:EuPin=>(printS p).2)
     · apply continuous_pi; intro i; apply continuous_pi; intro j; refine Complex.continuous_ofReal.comp (show Continuous fun p:EuPin=>p.coord.val i j from ?_); let X:M4 →ₗ[ℝ] ℝ:={ toFun:=fun p:M4=>p i j,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }; refine X.continuous_of_finiteDimensional.comp (show Continuous fun p:EuPin=>p.coord.val from ?_); exact continuous_subtype_val.comp (show Continuous fun p:EuPin=>p.coord from continuous_subtype_val.fst)
     refine Continuous.prodMk (f:=fun p:EuPin=> p.matrix.val) (g:=fun p:EuPin=>p.matrix⁻¹.val) ?_ ?_ <;> (unfold EuPin.matrix; fun_prop)
lemma canvas: Continuous (fun p:EuPin=> FullL d p x):=by
    letI Hi:Module.Free ℂ (Label d):= Module.Free.of_divisionRing ℂ _
    let B:= Module.finBasis ℂ (Label d)
    let F(p:EuPin):= FullL d p x
    change Continuous F; rw [show F=(fun p=>∑ i,B.coord i (F p) • B i) from funext fun t=> (B.sum_repr _).symm]; apply continuous_finsetSum; intro i _
    refine Continuous.smul (show Continuous fun a:EuPin=>B.coord i (F a) from ?_) (continuous_const (y:=B i)); let P:= (labels d).subtype; choose L hL using LinearMap.exists_leftInverse_of_injective P (LinearMap.ker_eq_bot.mpr (labels d).subtype_injective); let X:= B.coord i ∘ₗ L
    obtain ⟨f,h,h'⟩:=Vertex.figures x.val X
    refine (h.continuous.comp printG).congr (fun z=>?_)
    rw [Function.comp_apply,h']; change X (pinAct z x.val)= _; rw[←spine_pin]; change B.coord i (L (P (F z)))= _; exact congr_arg _ (DFunLike.congr_fun hL (F z))
lemma auth (h:RawSym) : FullL d A x=h.pin d A x:=Subtype.ext (Eq.trans (spine_pin A x.val) (h.pinActs d A x).symm)
end YM.Mako
#print axioms YM.Mako.full_d
#print axioms YM.Mako.canvas
#print axioms YM.Mako.auth
