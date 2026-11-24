import YM.QCD.Agate.Inner
import YM.QCD.Land.Refract
import YM.QCD.RP.Yard
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Agate
open Plum Land Lattice Wilson Grass Lat NormedSpace Function MeasureTheory Filter RP Kit Finset RG Push.GridApprox Jets
open scoped BigOperators Matrix.Norms.L2Operator Matrix Topology ComplexOrder Classical
variable {n c f : Side}{F:ℕ}{β:ℝ} {R:Cells.Cut c} {K:KernelChoices}
open Tide Flume YM.Next.Free Kites Acre Rails Rain Loom Fleet
variable {X:Pixel c F}{J:Patch}{w z:ℝ} {A:Set (Site c)}
variable {D S Y:Lot}
abbrev Coast (V:ℝ)(p: Malt D F):Prop:=∀ i,‖p.val i‖ ≤ V
lemma gravity (D:Lot)(s:ℕ→Side)(he:Tendsto (fun i=> (s i).val) atTop atTop):∀ᶠ i in atTop,Fits (s i) D:=by
   obtain ⟨r,hr⟩ := encompassed D
   filter_upwards [he.eventually (eventually_gt_atTop (2*r))] with n ht
   apply (wrap_injOn _).mono; intro x hx i; have hk := box_test.mp (hr hx); have hl := hk.1 i; have hh := hk.2 i; omega
lemma spade (D:Lot)(s:ℕ→Side)(he:Tendsto (fun i=> (s i).val) atTop atTop):∃ r:ℕ,∀ᶠ i in atTop,∀ p:Site (s i),∃ q:Site (s i),windows D p⊆RP.square q (fun _=>r):=by
   obtain ⟨r,hr⟩:= encompassed D; refine ⟨2*r+1,?_⟩; filter_upwards [he.eventually (eventually_gt_atTop (2*r))] with k hk p; refine ⟨leap p (fun _=> -(r:ℤ)),?_⟩; rintro x ⟨x,hx,rfl⟩ j
   let t:= x j +(r:ℤ); have h:= box_test.mp (hr hx); have h0:=h.1 j; have h1:=h.2 j; have he :t ≤2*r:=by unfold t; omega
   have hp : 0 ≤ t:=by unfold t; omega
   let N:= s k; have hv: t.toNat < (s k).val:=by omega
   change (leap p x j-leap p (fun _=> -(r:ℤ)) j).val <2*r+1; rw [show leap p x j-leap p (fun _=> -(r:ℤ)) j=((t.toNat:ℕ):Per (s k)) from ?_,ZMod.val_natCast_of_lt hv]; omega
   change (((x j:ℤ):Per N)+_) - _= _
   rw [← Int.cast_natCast (R:=Per N) t.toNat, Int.toNat_of_nonneg hp]; change (((x j:ℤ):Per N)+p j)-(((-(r:ℤ)):ℤ)+p j)=_; unfold t; push_cast; ring
lemma gainW(p:Site c)(h:Fits c D)(X:Malt D F)(hp:Coast w X): Plum.WithinP w (visit p X):=fun i=> (Land.pass_price (pensI p h) _).trans (hp (crest p i))
lemma ner (D:Lot)(s:ℕ→Side)(he:Tendsto (fun i=> (s i).val) atTop atTop) (hp:∀ i,Even (s i).val) (K:ℝ)(J:Patch)(F:ℕ):∃ A:ℝ,0≤A∧∀ᶠ i in atTop,∀ (P:Pixel (s i) F)(p: Site (s i)), Tide.Healing J P→ Continuous P → (Cvol P)=1 →(∀ U,‖P U‖ ≤ Globe.expo K (s i)) →∀(Z:Malt D F)(w:ℝ),Coast w Z→ ‖Tide.fresh P (visit p Z)‖ ≤ A*w :=by
   obtain ⟨r,hR⟩:= spade D s he; refine ⟨quota J r K,(Real.exp_pos _).le,?_⟩; filter_upwards [gravity D s he,hR,he.eventually (eventually_ge_atTop (r+2*longM J)),he.eventually (eventually_ge_atTop 4)] with i hk hh hr h4 U p hU hx hv hA Z w hZ; obtain ⟨q,hq⟩:=hh p; exact planetary hU hx hv (hp i) h4 q hr _ ((palps p Z).high hq) (gainW p hk Z hZ) K hA -- shadows fix
noncomputable def walk (h:D⊆S)(x:Paper D F):Paper S F:=fun U=> pass (channel h) (x (carries h U))
lemma quipper(h:D⊆S)(x:Malt D F):walk h x.val ∈ political S F:=by
   refine ⟨((staysP x).travel ((carries_cont h).measurable)).flows ((Grass.pass (channel (F:=F) h)).toLinearMap.continuous_of_finiteDimensional),fun k U=> ?_⟩
   have he :=turn_pass (court h) k (x.val (carries h (stain k U))); unfold walk; exact he.trans (congr_arg _ (yoke x (k∘court h) (carries h U))) -- stain equality
noncomputable def wheel (h:D ⊆ S): Malt D F →ₐ[ℂ] Malt S F where
    toFun x:= ⟨walk h x.val,quipper h x⟩
    map_one' :=Subtype.ext (funext fun _=>map_one _)
    map_zero':=Subtype.ext (funext fun _=>map_zero _)
    map_add' _ _:=Subtype.ext (funext fun _=>map_add _ _ _)
    map_mul' _ _:=Subtype.ext (funext fun _=>map_mul _ _ _)
    commutes' _:=Subtype.ext (funext fun _=>AlgHom.commutes _ _)
lemma wheeling(p:Site c)(X:Malt D F)(h:D⊆S) : visit p (wheel h X)=visit p X:=by funext i; apply AlgHom.congr_fun (pass_comp (channel h) (pens (D:=S) p)) (X.val (crest p i))
end YM.QCD.Agate
