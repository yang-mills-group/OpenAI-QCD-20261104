import YM.Kly.Palm
set_option maxHeartbeats 520000
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Bridge.Kly
open Function Set Filter Analysis MeasureTheory Measure UV UV.Free
open OS (Cross)
open Fields (pointMoment distinct gram)
open scoped Topology BigOperators InnerProductSpace NNReal ContDiff ComplexOrder Matrix
variable {F:Fields} {S:F.Kernel} {V:Chamber S timeAxis}(P:Spread V)
variable (H:Steady V) (Y:Fields.Euclidean S)(R:Angular S) {Q:Sequence}{C:Calibration Q}(E:F.System C){B:Bases F}{M':Momentum F}(U:B.Content C M')
variable (x:F.W)(w:P.algebra→⋆ₐ[ℂ]ℂ)(hx:Continuous w)
local notation "Sα"=>bloom P H w
local notation "t₀"=>timeAxis
-- Flavor transports from mixture invariance
noncomputable def jug (t:FlavorTorus)(x: Cluster F):Cluster F:= x.map fun p=>(p.1,F.flavor t p.2)
abbrev Fruits(S:F.Kernel):Prop:=∀ t:FlavorTorus,∀ b:Cluster F,distinct b→ pointMoment S (jug t b)=pointMoment S b
variable (h:Fruits S)(t:FlavorTorus)
abbrev bank(t:FlavorTorus)(x:Pack F):Pack F:=⟨jug t x.val, by apply locations.mpr; rw [jug,List.map_map]; exact locations.mp x.property⟩
lemma jar (v:Future F t₀): Positive (jug t v.val) t₀:= by refine ⟨(bank t ⟨v.val,v.property.1⟩).property,fun i hi=>?_⟩; obtain ⟨x,h,rfl⟩:=List.mem_map.mp hi; exact v.property.2 x h
noncomputable def boat(t:FlavorTorus)(v:Future F t₀):Future F t₀:= ⟨jug t v.val,jar t v⟩
variable (v b:Future F t₀)
lemma jarOne(x:Cluster F):jug 1 x=x:=by unfold jug; rw[map_one]; exact List.map_id x
lemma jarM(t u:FlavorTorus)(x:Cluster F):jug (t*u) x=jug t (jug u x):=by unfold jug; rw[List.map_map,map_mul]; rfl
lemma boatOne:boat 1 v=v:= Subtype.ext (jarOne _)
lemma boatM(y:FlavorTorus): boat (t*y) v=boat t (boat y v):= Subtype.ext (jarM ..)
lemma boat_start : boat t (air t₀ (F:=F))=air t₀:=Subtype.ext rfl
lemma teaB(r:ℝ≥0): boat t (travel v r)=travel (boat t v) r:= by apply Subtype.ext; change jug _ (carry _ _)=carry (jug _ _) _; simp only [jug, carry,List.map_map]; rfl
include E h
lemma scolder : Bridge.kernel S t₀ (boat t v).val (boat t b).val=Bridge.kernel S t₀ v.val b.val:=by
      unfold Bridge.kernel; rw[← h t _ (twoSides v.property b.property)]; apply congr_arg (pointMoment S); change reflect (jug _ _) _++jug _ _=_; unfold jug; rw [List.map_append]; apply congr_arg₂ _ _ rfl; simp only [reflectedPoint,List.map_map,← List.map_reverse]; congr 1; funext i; exact Prod.ext rfl ((E.flavorTurns t t₀ i.2).symm)
include V
lemma merits(v b: Voice F t₀): let f:= Finsupp.linearCombination ℂ fun i:Future F t₀=> V.GNS.plant (boat t i); inner ℂ (f v) (f b)=inner ℂ (V.GNS.stems v) (V.GNS.stems b):=by
      intro f; induction v using Finsupp.induction_linear with
      | add x y hx hy=> simp only [map_add,inner_add_left,hx,hy]
      | zero=> simp
      | single i c=>
        unfold f; simp only[Kernel.Gram.stems,Finsupp.linearCombination_single,inner_smul_left]; congr 1; induction b using Finsupp.induction_linear with
        | add x y hx hy=> simp only [map_add, inner_add_right,hx,hy]
        | zero=> simp
        | single j v=> rw[Finsupp.linearCombination_single,Finsupp.linearCombination_single,inner_smul_right,inner_smul_right,V.GNS.measure,V.GNS.measure,scolder E h]
lemma mintP:∃ T:FlavorTorus→*(V.H≃ₗᵢ[ℂ] V.H), ∀ p:FlavorTorus,∀ v, T p (V.GNS.plant v)=V.GNS.plant (boat p v):=by
      have ht(t:FlavorTorus): ∃ f:V.H.Op, ‖f‖≤ 1 ∧∀ v,f (V.GNS.plant v)=V.GNS.plant (boat t v):=by
               refine V.GNS.by_bound _ _ zero_le_one fun i=>?_ ; rw[one_mul]; apply le_of_eq; apply pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (NeZero.ne 2)|>.mp; apply Complex.ofReal_injective; have hx:= merits (V:=V) E h t i i; dsimp only at hx; rw [inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K] at hx; exact_mod_cast hx
      choose f hf hV using ht
      have h1 :f 1=1:=by refine V.GNS.by_bud fun i=>?_ ; rw [hV,boatOne]; rfl
      have he(x y:FlavorTorus) : f (x*y)=f x*f y:=by apply V.GNS.by_bud; intro i; change _= f x (f y _); rw [hV,hV,hV, boatM]
      have hL(p: FlavorTorus)(v):f p⁻¹ (f p v)=v:=by change (f _*f _) v=v; rw[← he, inv_mul_cancel,h1]; rfl
      have hR(p:FlavorTorus)(v):f p (f p⁻¹ v)=v:=by nth_rw 1 [← inv_inv p]; exact hL _ _
      have hE(p:FlavorTorus)(v:V.H):‖f p v‖ ≤ ‖v‖:= (ContinuousLinearMap.le_opNorm (f p) _).trans (mul_le_of_le_one_left (norm_nonneg _) (hf _))
      let G(p:FlavorTorus): V.H≃ₗ[ℂ] V.H:=LinearEquiv.ofLinear (f p).toLinearMap (f p⁻¹).toLinearMap (LinearMap.ext (hR p)) (LinearMap.ext (hL p))
      let T(p:FlavorTorus): V.H≃ₗᵢ[ℂ] V.H:= { G p with norm_map' := fun v=> show ‖f p v‖= _ from le_antisymm (hE ..) (show ‖v‖≤ ‖f p v‖ from (Eq.trans_le (congr_arg norm (hL p v).symm) (hE p⁻¹ (f p v)))) }
      exact ⟨⟨⟨T,LinearIsometryEquiv.ext fun x=>show f 1 x=x from (by rw[h1]; rfl)⟩,fun p q=>LinearIsometryEquiv.ext (fun i=>by change f (p*q) i=f p (f q i); rw [he]; rfl)⟩,hV⟩
end YM.Massive.Bridge.Kly
#print axioms YM.Massive.Bridge.Kly.mintP
#print axioms YM.Massive.Bridge.Kly.teaB
