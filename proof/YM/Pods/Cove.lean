import YM.Pods.Circle
/-! Estimate on normalized expectation of full oscillating reflection replica.
Primary label is exact physical if mix from OrderMix. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria
open Set Filter Function Finset Lattice Source
open scoped ContDiff Topology BigOperators Classical
namespace Hub
open QCD QCD.Lat UV Cylinder RG Wilson Grass MeasureTheory Cells QCD.RP Planned
open Massive.Romance Massive.Chess
open Poised Plans Display Poised.Plans Stamp
open Massive.Patria.Depth TorusPCAC.Geometry
variable {c f m:Side}{n k d:ℕ}{F:ℕ} (R:Regulator f 6)
-- march bare expectation through all signs.AP.Vacuum.G heat.
variable (x y : Insertion f 6)
lemma ferryX (h:R.t=0)(b:Cover)(he: march b x = y) : R.average x=R.average y:=by
    let M := R.density; let G := QCD.Revolve.hues (wrap f b) 1 (heat b) 1; let F:= M*x; let P:= QCD.Kit.disguise (copies 6 G)
    have hh : (R.density : Insertion f 6)=M:=rfl; let k:=pull (K:=su.El) 1 (wrap f b)
    have hz(U:Grid f): R.density U*y U=P (F (k U)):=by rw [show R.density U=P (M (k U)) from (congr_fun (Exposure.move_pivot R b h) U).symm,congr_fun he U|>.symm]; exact (map_mul P _ _).symm -- left rhs possibly rewriting inside M
    let Φ:=fun V:Grid f=> ber (Modes f 6) (F V); have hΦ:Integrable Φ (prior su f):= R.integrable _; have hk : MeasurePreserving k (prior su f) (prior su f):= prior_pull ..
    apply congr_arg (fun v:ℂ=> R.Z⁻¹ * v); change (∫ U, Φ U ∂prior su f)= ∫ U,ber (Modes f 6) ((R.density*y) U) ∂prior su f
    rw [show (∫ U, Φ U ∂prior su f)=(∫ U, Φ (k U) ∂prior su f) from (by rw [← integral_map hk.aemeasurable (hk.map_eq.symm ▸ hΦ.aestronglyMeasurable),hk.map_eq])]
    apply integral_congr_ae; refine Filter.Eventually.of_forall fun V=>?_ ; change Φ (k V)= ber _ (R.density V * y V); rw [hz]; exact (Kit.vanishV (copies_unitary _ _ (QCD.Revolve.colour_wheel (glares _) QCD.Revolve.Swing.none)) _).symm -- ambiguity
variable {I:Type}[Fintype I](l: List I)(T:Tiling f)
lemma signed_product (x y:I→Insertion f 6)(he:∀ i,SignedEq (x i) (y i)) : SignedEq (l.map x).prod (l.map y).prod:=by induction l with| nil=>exact SignedEq.refl _| cons a l h=> exact (he a).mul h
lemma ferry_many (h:R.t=0)(b:Cover)(x y:I→Insertion f 6)(he:∀ i,march b (x i)= y i) : R.average (l.map x).prod=R.average (l.map y).prod:=by
    apply ferryX R _ _ h b; induction l with
    | nil=>exact funext fun i=> map_one (crank (N:=6) 1 1 (wrap f b) (heat b))
    | cons a l ih=>exact funext fun i=> (map_mul (crank (N:=6) 1 1 (wrap f b) (heat b)) _ _).trans (congr_arg₂ (·*·) (congr_fun (he a) i) (congr_fun ih i)) -- apply constrained f.No storage
variable (sym:RawSym)(Z:Bore d)(hz:Rubric sym Z)(u:Label d)(q:Bool)(hu:moored u.val q)
-- mixing transformation. Need at reference. normalized quantities base.We instead norm. Neg persistence.
variable (Φ:Label d ≃ₗ[ℂ] Label d)(hX:∀ x:Label d,sym.parity d (Φ x)=Φ (sym.parity d x))(hQ:∀ a:Axis,∀ x:Label d,sym.adj d a (Φ x)=Φ (sym.adj d a x))(Yv:ℝ)
local notation "Lx"=>Φ u
include hu
lemma toured (s:List Axis)(h:u≠0) : moored (spine sym u s).val q ∧ spine sym u s≠0:=by
    induction s with| nil=> exact ⟨hu,h⟩| cons a k ih=>rw [spine]; exact ⟨durable _ _ _ ih.1 a,by intro he; exact ih.2 ((sym.adj d a).injective (he.trans (map_zero _).symm))⟩
include hz
variable (g:Ratio c f) (hp:Odd g.count.val)(he:Even c.val)
variable (b:Cover) (hr:R.t=0)
local notation "T₁"=>mural g he (wrap f b)
local notation "κ"=> Z f b (Φ u)
local notation "R₁"=>R.zeroCut
local notation "Tχ"=>tally T₁ -- plan.G
include hp hr hX hQ
lemma chapel (h:u≠0)(hY:0 ≤ Yv)(hB:∀ (s:Site c→List Axis),(∀ i:Site c,(s i).length≤8) → ‖R.average ((univ :Finset (Site c)).toList.map (fun i=> Z f (g.count.val • Lattice.lift i) (Φ (spine sym u (s i))))).prod‖ ≤ Yv ^ (Fintype.card (Site c))) : floorL T₁ R.average R κ (0 : Site c) ≤ Yv:=by
    let b' := wrap f b; let T:= T₁; let x (v:Site c):= b +g.count.val • Lattice.lift v
    have hh(v): T.copyMap v b'=wrap f (x v):= (tuned g he hp b' v).trans (by rw [show _= _ from map_add (wrap f) b _]; rfl) -- syntax
    have hG : x 0=b:=by unfold x; rw [show Lattice.lift (0:Site c)=0 from (by funext; simp [Lattice.lift]),smul_zero,add_zero]
    have hv : ∀ (p:T.Cell)(a:Axis)(v:T.Cell),wrap f (x (T.mate p a v))=(T.bandCut p a).reflect (wrap f (x v)):=fun p a v=> (hh _).symm.trans ((T.after p a v b').trans (congr_arg (T.bandCut p a).reflect (hh v))) -- check after lemma
    choose L he₁ ht using fun v: T.Cell=> legsT T 0 v; let Q(v:T.Cell):= axes (pathT T (L v)); have h(Q' : List Axis): spine sym (Φ u) Q'= Φ (spine sym u Q'):= by induction Q' with|nil=>rfl|cons a l ih=>rw [spine,ih,hQ,spine]
    have he₂:T.kind=.link:=rfl
    have hx0:moored (Φ u).val q:= by apply (moored_iff sym _ _).2; rw [hX,(moored_iff sym u q).1 hu,map_smul]
    let P:= Z f b (Φ u); let X(v:T.Cell):= Z f (x v) (Φ (spine sym u (Q v))); let Y(v:T.Cell):= Z f (g.count.val • Lattice.lift (show Site c from v)) (Φ (spine sym u (Q v)))
    have hx (v) : SignedEq (replicateR T R P 0 v) (X v):=by
         let ht' :Parity P:= ⟨q,fade Z sym hz _ _ hx0 b⟩ -- c inserted args.T
         apply SignedEq.trans (SignedEq.symm (along T R.zeroCut P (L v) 0 v ht' hr he₂ (ht v)))
         have hw:= (spirals R Z sym hz (Φ u) q hx0 T 0 he₂ x hv hr (L v)).2; rw [show x (0:T.Cell)=b from hG,h,ht] at hw; exact hw
    let l:= (Finset.univ :Finset T.Cell).toList; change floorL T _ _ P (0:T.Cell) ≤ Yv; apply le_of_pow_le_pow_left₀ T.cells_positive.ne' hY; rw [roof_power]; change ‖R.average ((l.map _).prod)‖ ≤ Yv ^ Fintype.card T.Cell
    rw [Chess.Fortuna.Array.holds_period R.average (signed_product l _ _ hx), ← ferry_many R l hr b Y X (fun i=>?_)] -- order
    · refine hB Q ?_; intro i; unfold Q axes pathT; simp only [List.length_map]; exact he₁ _
    unfold Y X x; rw [hz.advances]; exact congr_arg (fun o:Cover=> ⇑(Z f o (Φ (spine sym u (Q i))))) (add_comm _ b)
end Hub
end YM.Massive.Patria
#print axioms YM.Massive.Patria.Hub.chapel
