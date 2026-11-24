import YM.QCD.Spice.Gowns
/-! # Prices for ψ comparison operator. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Spice
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run Jets
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.AbsoluteSums Footprint Trees
open Sun Cove.Fj Jets.Touch MeasureTheory
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F k j:ℕ}{c f: Side} {δ q κ a u v η ξ x y w t b':ℝ}{l b:ℕ}{G:Flight j k}{h:f.val=c.val*G.L.val}
local notation "R"=> Junta c f F
local notation "S"=> sliceL G h
variable {T:Grid f→Sheet f}(P:Sun G c f h δ v q u a l T)
open Dust Stew Brick Garden Sway OrbitG Revolve
variable {σ σ' ζ K D μ B₀ m τ γ Λ Λ' :ℝ}
variable (o: Site f)(U V:Grid f)(X: Support f)
lemma pearl_len (X: Mat)(U:su.El): ‖X*colour U‖ ≤ ‖X‖:= (norm_mul_le ..).trans (mul_le_of_le_one_right (norm_nonneg _) (Lat.rotation_price (show colour U ∈ unitary _ from ⟨su.mat_star_mul _,su.mat_mul_star _⟩)))
-- conversion for SAGE geometry. uses ‖·‖_op.
def BeamRaw (X:Support f)(U V:Grid f)(p:ℝ):Prop :=∀ i:Edge (Site f),i.1∈ X→i.1+step i.2∈ X → su.chord (U i*(V i)⁻¹) ≤ p
lemma boughtX : ∃ C:ℝ,0<C∧∀ (f:Side)(U V:Grid f)(X:Support f)(b:ℝ), BeamRaw X U V b→beamAt X U V (C*b):=by
    obtain ⟨C,hC,h⟩:=Fork.halo_chart; refine ⟨C,hC,fun f U V X b ht i hi hx=>?_⟩
    let a:= V i; let u:=U i; let p:=colour a; let v:=u*a⁻¹
    have he: colour u-colour a=(colour v -1)*p:=by rw [sub_mul,one_mul, ← Lat.colour_mul,show v*a=u from inv_mul_cancel_right ..]
    change ‖colour u-p‖≤_; rw [he]; exact (pearl_len _ a).trans ((h v).trans (mul_le_mul_of_nonneg_left (ht i hi hx) hC.le)) -- inv_
lemma celia (h:BeamRaw X U V t) (g:Frame f): BeamRaw X (gauge g U) (gauge g V) t:=fun i hi hx =>by
    apply le_trans _ (h i hi hx); rw [Lattice.gauge,Lattice.gauge,show g i.1 * U i*(g (i.1+step i.2))⁻¹ * (g i.1 * V i*(g (i.1+step i.2))⁻¹)⁻¹ =g i.1*(U i*(V i)⁻¹)*(g i.1)⁻¹ from (by group), su.chord_conj]
lemma raysFort (h:beamAt X U V x)(hp:beamAt X V (1:Grid f) y):beamAt X U 1 (x+y) := fun i hi hj=>(norm_sub_le_norm_sub_add_norm_sub _ (colour (V i)) _).trans (add_le_add (h _ hi hj) (hp _ hi hj))
lemma holly (G:Frame f): ‖Dust.ramp f G‖≤ 1:=by
   have hh (p:su.El): ‖Lat.touch (colour p)‖≤1:= Lat.rotation_price (Lat.touch_u (x:=colour p) ⟨su.mat_star_mul _,su.mat_mul_star _⟩)
   unfold Dust.ramp; rw [Prod.norm_def]; exact max_le ((pi_norm_le_iff_of_nonneg zero_le_one).2 (fun i=>hh _)) ((pi_norm_le_iff_of_nonneg zero_le_one).2 (fun i=> hh _)) -- Primed
variable {E J : Type}{P':Rise f F E J} -- E J variables
lemma sparkleG [Countable E][Countable J](H:P'.Reframe) (U:Grid f)(g:Frame c)(s:Finset (Fj (Tr f) E J)):
   let T:= P.equip F b; let p:= g ∘ (sliceL G h).parent
   changeVars (tor (ramp c g)) (light _ (hue T P' x s (gauge p U))) = light _ (hue T P' x s U):=by
    intro T p; have hg: p ∘ (sliceL G h).embed = g:=funext (fun i=> congr_arg g ((sliceL G h).embed_parent _))
    have hf : Parade (gauge p U) U (trade (rotates F p)) P' (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) x :=by
       refine ⟨by simp,fun _=>Finset.image_id.symm,fun _=>rfl,fun _=>Finset.image_id.symm,fun _=>Finset.image_id.symm,fun i=>Subtype.ext (H.main ..),fun i=>Subtype.ext (H.plug ..)⟩
    have he:=hatch (heatE P F b U p) hf s; rw [hg] at he; simp [Sway.sail] at he; exact (Dust.pendulum ..).trans (congr_arg Subtype.val he)
-- reader at ANY g. norms budget via ℓ.D, even spin sign.Limit.
abbrev rootBill (o:Site f)(p:ℝ)(T:Crate f F→L[ℝ]ℝ):Prop:=∀ i,‖T i‖ ≤ Stew.plank o p i
def testG (g:Frame f)(T:Crate f F→L[ℝ]ℝ):Crate f F→L[ℝ]ℝ:=T.comp (((changeVars (tor (ramp f g))).toLinearMap.toContinuousLinearMap).restrictScalars ℝ)
lemma kinFare (h:0<v)(t:Crate f F→L[ℝ]ℝ)(g:Frame f)(he:rootBill o v t)(hh:fareG 1 v F ≤ w): rootBill o w (testG g t):=fun i=> (he _).trans (Dust.stems (ramp f g) (holly g) zero_lt_one h hh i)
lemma shard {c:Side}(U:Support c)(o:Site c)(m:ℕ)(ht:∀ i∈U,separation i o ≤ m)(x:EvenA c F)(hy:0<v)(h:Gated U x): Sen o v x ≤ (1+(m:ℝ))^2*load (fun _=>v) (light _ x):=by
    have hx(i:Keys c F)(hi:i∈limits U): Stew.lens o i≤ m:=ht _ (mem_filter.mp hi).2
    apply le_trans (b:=camp (fun _=>v) (Stew.lens o) 2 (light _ x)) ?_ (camps (fun _=>hy) _ _ _ h _ hx); unfold Sen Stew.plank camp; rw [pricesD _ hy.le]; apply le_of_eq; refine sum_congr rfl fun i _=>?_ ; unfold starch Cove.weight pieD regionW; simp -- syntax
end YM.QCD.Spice
