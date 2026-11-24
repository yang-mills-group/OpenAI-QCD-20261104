import YM.Vern.Vale
set_option autoImplicit false
noncomputable section
namespace YM.Vern
open Function Set Filter Analysis MeasureTheory Lattice QCD QCD.Lat QCD.Grass
open Massive Massive.UV Massive.Tarn Massive.Tarn.Choir Massive.Tarn.Choir.Strip Massive.Patria.Gall.Onyx
open Massive.Tarn.ChargeQ Massive.Poised.Plans.Stamp.Stair Massive.Gust
open scoped Topology ContDiff BigOperators Classical ComplexOrder Matrix InnerProductSpace
open Sprig Intag.Sprig UV.Free Massive.Poised.Plans.Stamp Heron Iceberg Lobo
variable {C:Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K}(H:K.Domestic){d:ℕ}{x:K.W}(hx:x∈safeV T)
variable (g:FlavorTorus)(t:EuPin)(s:Signed)(ht:t.Lifts s)
lemma classic (B:Bundle):Commute (UV.turned (d:=d) t B) (UV.byFlavor g fun i:SpinMode d=>i.2):=by
     let f(i:SpinMode d):ℂ:=g i.2; change Commute _ (Matrix.diagonal f); unfold Commute SemiconjBy; ext i j; rw [Matrix.mul_diagonal,Matrix.diagonal_mul]; by_cases he:i.2=j.2; · rw [show f i=f j from congr_arg (fun i:Flavor 6=>(g i:ℂ)) he, mul_comm]
     rw [show UV.turned t B i j=0 from (by unfold UV.turned; simp [Matrix.of_apply,he]),mul_zero,zero_mul]
include ht H
lemma spins_u (x:K.W): T.flavor g (T.spin t x)= T.spin t (T.flavor g x):=by
     obtain ⟨d,v,rfl⟩:=H.absorbs x; rw [T.w _ _ ht,T.f,T.f,T.w _ _ ht]; apply congr_arg (K.focus (Averaging.permute s none) _); apply Subtype.ext; rw [P.sym.flavorActs,P.sym.pinActs,P.sym.pinActs, P.sym.flavorActs]
     induction v.val using TensorProduct.induction_on with
     | zero=> simp
     | add x y hx hy=> simp only [map_add,hx,hy]
     | tmul x y=> unfold flavorAct pinAct; simp_rw [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, Grass.adapt_together,(classic (d:=d) g t _).eq,(classic (d:=d) g⁻¹ t _).eq]; rfl
include hx
lemma spinning:T.spin t x∈safeV T:= ⟨(spinClamp T H _ _ ht x).trans (congr_arg _ hx.1),fun u=> (spins_u H u _ _ ht x).trans (congr_arg _ (hx.2 u))⟩
omit hx
variable (u:K.level d)(hv:u∈seedP T d)
include hv
lemma crane :∃ v:K.level d,v.val=T.spin t u.val∧v∈ seedP T d:=by
     obtain ⟨x,hx⟩:=u.property; change K.focus none _ x=u.val at hx; have h:T.spin t u.val∈ K.level d:=by
                  rw [←hx,T.w _ _ ht d]; rw[← H.tops (Averaging.permute s none)]; exact LinearMap.mem_range_self ..
     exact ⟨⟨_,h⟩,rfl, spinning H (show u.val∈safeV T from hv) t s ht⟩
omit hv ht
noncomputable def shipP(i:Lobo.Tri)(d:ℕ):seedP T d≃ₗ[ℂ] seedP T d:=by
     let B:=SpinQ i; let S:= Cup i; have ht :B.Lifts S:=fL i
     choose f hf hT using fun x:↥(seedP T d)=> crane H _ _ ht x.val x.property
     let P': ↥(seedP T d)→↥(seedP T d):= fun x=> ⟨f x,hT x⟩; have hX(x): (P' x).val.val=T.spin B x.val.val:= hf x
     let F: Module.End ℂ ↥(seedP T d):= {toFun:=P',map_add':=fun x y=>Subtype.ext (Subtype.ext (by change (P' (x+y)).val.val=(P' x).val.val+(P' y).val.val; rw [hX,hX,hX]; exact map_add (T.spin B) _ _ )), map_smul':=fun c x=>Subtype.ext (Subtype.ext (by change (P' (c • x)).val.val=c • (P' x).val.val; rw [hX,hX]; exact map_smul (T.spin B) c x.val.val))}; have ht : Injective F:=fun x y he=>Subtype.ext (Subtype.ext ((T.spin B).injective ((hX x).symm.trans ((congr_arg (fun x: ↥(seedP T d)=> x.val.val) he).trans (hX y)))))
     exact LinearEquiv.ofBijective F ⟨ht,LinearMap.surjective_of_injective ht⟩
-- definitional unfolding proof tactic choose irreducible? use structure instead
#check shipP
lemma sails (i:Lobo.Tri)(d:ℕ)(x:seedP T d):(shipP (T:=T) H i d x).val.val=T.spin (SpinQ i) x.val.val:=by unfold shipP; dsimp; exact (crane H _ _ (fL i) _ x.property).choose_spec.1
end YM.Vern
#print axioms YM.Vern.spinning
#print axioms YM.Vern.shipP
#print axioms YM.Vern.sails
